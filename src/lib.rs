#![feature(try_reserve)]
#![feature(str_internals)]
#![feature(pattern)]
#![feature(slice_range)]
#![feature(extend_one)]
#![feature(min_specialization)]
#![feature(fmt_internals)]

use core::str::lossy;
use std::{
    borrow::Cow,
    char::{decode_utf16, REPLACEMENT_CHARACTER},
    fmt, hash,
    iter::{from_fn, FromIterator, FusedIterator},
    ops::{self, Add, AddAssign, Index, IndexMut, Range, RangeBounds},
    ptr, slice,
    str::{
        from_utf8, from_utf8_unchecked, from_utf8_unchecked_mut, pattern::Pattern, Chars, FromStr,
        Utf8Error,
    },
};

use thin_vec::ThinVec;

#[derive(PartialOrd, Eq, Ord)]
pub struct ThinString {
    vec: ThinVec<u8>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FromUtf8Error {
    bytes: ThinVec<u8>,
    error: Utf8Error,
}

pub struct FromUtf16Error(());

impl ThinString {
    #[inline]
    pub fn new() -> ThinString {
        ThinString {
            vec: ThinVec::new(),
        }
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> ThinString {
        ThinString {
            vec: ThinVec::with_capacity(capacity),
        }
    }

    #[inline]
    pub fn from_utf8(vec: ThinVec<u8>) -> Result<ThinString, FromUtf8Error> {
        match from_utf8(&vec) {
            Ok(..) => Ok(ThinString { vec }),
            Err(e) => Err(FromUtf8Error {
                bytes: vec,
                error: e,
            }),
        }
    }

    pub fn from_utf8_lossy(v: &[u8]) -> ThinString {
        let mut iter = lossy::Utf8Lossy::from_bytes(v).chunks();

        let (first_valid, first_broken) = if let Some(chunk) = iter.next() {
            let lossy::Utf8LossyChunk { valid, broken } = chunk;
            if valid.len() == v.len() {
                debug_assert!(broken.is_empty());
                return ThinString::from(valid);
            }
            (valid, broken)
        } else {
            return ThinString::new();
        };

        const REPLACEMENT: &str = "\u{FFFD}";

        let mut res = ThinString::with_capacity(v.len());
        res.push_str(first_valid);
        if !first_broken.is_empty() {
            res.push_str(REPLACEMENT);
        }

        for lossy::Utf8LossyChunk { valid, broken } in iter {
            res.push_str(valid);
            if !broken.is_empty() {
                res.push_str(REPLACEMENT);
            }
        }

        res
    }

    pub fn from_utf16(v: &[u16]) -> Result<ThinString, FromUtf16Error> {
        let mut ret = ThinString::with_capacity(v.len());
        for c in decode_utf16(v.iter().cloned()) {
            if let Ok(c) = c {
                ret.push(c);
            } else {
                return Err(FromUtf16Error(()));
            }
        }
        Ok(ret)
    }

    #[inline]
    pub fn from_utf16_lossy(v: &[u16]) -> ThinString {
        decode_utf16(v.iter().cloned())
            .map(|r| r.unwrap_or(REPLACEMENT_CHARACTER))
            .collect()
    }

    #[inline]
    pub unsafe fn from_utf8_unchecked(bytes: ThinVec<u8>) -> ThinString {
        ThinString { vec: bytes }
    }

    #[inline]
    pub fn into_bytes(self) -> ThinVec<u8> {
        self.vec
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        self
    }

    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        self
    }

    #[inline]
    pub fn push_str(&mut self, string: &str) {
        self.vec.extend_from_slice(string.as_bytes())
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional)
    }

    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.vec.reserve_exact(additional)
    }

    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit()
    }

    #[inline]
    pub fn push(&mut self, ch: char) {
        match ch.len_utf8() {
            1 => self.vec.push(ch as u8),
            _ => self
                .vec
                .extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
        }
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.vec
    }

    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len)
        }
    }

    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let newlen = self.len() - ch.len_utf8();
        unsafe {
            self.vec.set_len(newlen);
        }
        Some(ch)
    }

    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = idx + ch.len_utf8();
        let len = self.len();
        unsafe {
            ptr::copy(
                self.vec.as_ptr().add(next),
                self.vec.as_mut_ptr().add(idx),
                len - next,
            );
            self.vec.set_len(len - (next - idx));
        }
        ch
    }

    pub fn remove_matches<'a, P>(&'a mut self, pat: P)
    where
        P: for<'x> Pattern<'x>,
    {
        use core::str::pattern::Searcher;

        let rejections = {
            let mut searcher = pat.into_searcher(self);
            // Per Searcher::next:
            //
            // A Match result needs to contain the whole matched pattern,
            // however Reject results may be split up into arbitrary many
            // adjacent fragments. Both ranges may have zero length.
            //
            // In practice the implementation of Searcher::next_match tends to
            // be more efficient, so we use it here and do some work to invert
            // matches into rejections since that's what we want to copy below.
            let mut front = 0;
            let rejections: ThinVec<_> = from_fn(|| {
                let (start, end) = searcher.next_match()?;
                let prev_front = front;
                front = end;
                Some((prev_front, start))
            })
            .collect();
            rejections
                .into_iter()
                .chain(core::iter::once((front, self.len())))
        };

        let mut len = 0;
        let ptr = self.vec.as_mut_ptr();

        for (start, end) in rejections {
            let count = end - start;
            if start != len {
                // SAFETY: per Searcher::next:
                //
                // The stream of Match and Reject values up to a Done will
                // contain index ranges that are adjacent, non-overlapping,
                // covering the whole haystack, and laying on utf8
                // boundaries.
                unsafe {
                    ptr::copy(ptr.add(start), ptr.add(len), count);
                }
            }
            len += count;
        }

        unsafe {
            self.vec.set_len(len);
        }
    }

    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(char) -> bool,
    {
        struct SetLenOnDrop<'a> {
            s: &'a mut ThinString,
            idx: usize,
            del_bytes: usize,
        }

        impl<'a> Drop for SetLenOnDrop<'a> {
            fn drop(&mut self) {
                let new_len = self.idx - self.del_bytes;
                debug_assert!(new_len <= self.s.len());
                unsafe { self.s.vec.set_len(new_len) };
            }
        }

        let len = self.len();
        let mut guard = SetLenOnDrop {
            s: self,
            idx: 0,
            del_bytes: 0,
        };

        while guard.idx < len {
            let ch = unsafe {
                guard
                    .s
                    .get_unchecked(guard.idx..len)
                    .chars()
                    .next()
                    .unwrap()
            };
            let ch_len = ch.len_utf8();

            if !f(ch) {
                guard.del_bytes += ch_len;
            } else if guard.del_bytes > 0 {
                unsafe {
                    ptr::copy(
                        guard.s.vec.as_slice().as_ptr().add(guard.idx),
                        guard
                            .s
                            .vec
                            .as_mut_slice()
                            .as_mut_ptr()
                            .add(guard.idx - guard.del_bytes),
                        ch_len,
                    );
                }
            }

            // Point idx to the next char
            guard.idx += ch_len;
        }

        drop(guard);
    }

    #[inline]
    pub fn insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx));
        let mut bits = [0; 4];
        let bits = ch.encode_utf8(&mut bits).as_bytes();

        unsafe {
            self.insert_bytes(idx, bits);
        }
    }

    unsafe fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
        let len = self.len();
        let amt = bytes.len();
        self.vec.reserve(amt);

        ptr::copy(
            self.vec.as_slice().as_ptr().add(idx),
            self.vec.as_mut_slice().as_mut_ptr().add(idx + amt),
            len - idx,
        );
        ptr::copy(bytes.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
        self.vec.set_len(len + amt);
    }

    #[inline]
    pub fn insert_str(&mut self, idx: usize, string: &str) {
        assert!(self.is_char_boundary(idx));

        unsafe {
            self.insert_bytes(idx, string.as_bytes());
        }
    }

    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut ThinVec<u8> {
        &mut self.vec
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> ThinString {
        assert!(self.is_char_boundary(at));
        let other = self.vec.split_off(at);
        unsafe { ThinString::from_utf8_unchecked(other) }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.vec.clear()
    }

    pub fn drain<R>(&mut self, range: R) -> Drain<'_>
    where
        R: RangeBounds<usize>,
    {
        // Memory safety
        //
        // The ThinString version of Drain does not have the memory safety issues
        // of the vector version. The data is just plain bytes.
        // Because the range removal happens in Drop, if the Drain iterator is leaked,
        // the removal will not happen.
        let Range { start, end } = slice::range(range, ..self.len());
        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));

        // Take out two simultaneous borrows. The &mut ThinString won't be accessed
        // until iteration is over, in Drop.
        let self_ptr = self as *mut _;
        // SAFETY: `slice::range` and `is_char_boundary` do the appropriate bounds checks.
        let chars_iter = unsafe { self.get_unchecked(start..end) }.chars();

        Drain {
            start,
            end,
            iter: chars_iter,
            string: self_ptr,
        }
    }
}

impl FromUtf8Error {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    pub fn into_bytes(self) -> ThinVec<u8> {
        self.bytes
    }

    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl fmt::Display for FromUtf8Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl fmt::Display for FromUtf16Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt("invalid utf-16: lone surrogate found", f)
    }
}

impl Clone for ThinString {
    fn clone(&self) -> Self {
        ThinString {
            vec: self.vec.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.vec.clone_from(&source.vec);
    }
}

impl FromIterator<char> for ThinString {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> ThinString {
        let mut buf = ThinString::new();
        buf.extend(iter);
        buf
    }
}

impl<'a> FromIterator<&'a char> for ThinString {
    fn from_iter<I: IntoIterator<Item = &'a char>>(iter: I) -> ThinString {
        let mut buf = ThinString::new();
        buf.extend(iter);
        buf
    }
}

impl<'a> FromIterator<&'a str> for ThinString {
    fn from_iter<I: IntoIterator<Item = &'a str>>(iter: I) -> ThinString {
        let mut buf = ThinString::new();
        buf.extend(iter);
        buf
    }
}

impl FromIterator<ThinString> for ThinString {
    fn from_iter<I: IntoIterator<Item = ThinString>>(iter: I) -> ThinString {
        let mut iterator = iter.into_iter();

        // Because we're iterating over `String`s, we can avoid at least
        // one allocation by getting the first string from the iterator
        // and appending to it all the subsequent strings.
        match iterator.next() {
            None => ThinString::new(),
            Some(mut buf) => {
                buf.extend(iterator);
                buf
            }
        }
    }
}

impl FromIterator<Box<str>> for ThinString {
    fn from_iter<I: IntoIterator<Item = Box<str>>>(iter: I) -> ThinString {
        let mut buf = ThinString::new();
        buf.extend(iter);
        buf
    }
}

impl<'a> FromIterator<Cow<'a, str>> for ThinString {
    fn from_iter<I: IntoIterator<Item = Cow<'a, str>>>(iter: I) -> ThinString {
        let mut iterator = iter.into_iter();

        // Because we're iterating over CoWs, we can (potentially) avoid at least
        // one allocation by getting the first item and appending to it all the
        // subsequent items.
        match iterator.next() {
            None => ThinString::new(),
            Some(cow) => {
                let mut buf = cow.to_thin_string();
                buf.extend(iterator);
                buf
            }
        }
    }
}

impl Extend<char> for ThinString {
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push(c));
    }

    #[inline]
    fn extend_one(&mut self, c: char) {
        self.push(c);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

impl<'a> Extend<&'a char> for ThinString {
    fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }

    #[inline]
    fn extend_one(&mut self, &c: &'a char) {
        self.push(c);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

impl<'a> Extend<&'a str> for ThinString {
    fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(s));
    }

    #[inline]
    fn extend_one(&mut self, s: &'a str) {
        self.push_str(s);
    }
}

impl Extend<Box<str>> for ThinString {
    fn extend<I: IntoIterator<Item = Box<str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

impl Extend<ThinString> for ThinString {
    fn extend<I: IntoIterator<Item = ThinString>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }

    #[inline]
    fn extend_one(&mut self, s: ThinString) {
        self.push_str(&s);
    }
}

impl<'a> Extend<Cow<'a, str>> for ThinString {
    fn extend<I: IntoIterator<Item = Cow<'a, str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }

    #[inline]
    fn extend_one(&mut self, s: Cow<'a, str>) {
        self.push_str(&s);
    }
}

impl PartialEq for ThinString {
    #[inline]
    fn eq(&self, other: &ThinString) -> bool {
        PartialEq::eq(&self[..], &other[..])
    }
    #[inline]
    fn ne(&self, other: &ThinString) -> bool {
        PartialEq::ne(&self[..], &other[..])
    }
}

#[doc(hidden)]
macro_rules! impl_eq {
    ($lhs:ty, $rhs: ty) => {
        #[allow(unused_lifetimes)]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }

        #[allow(unused_lifetimes)]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }
    };
}

impl_eq! { ThinString, str }
impl_eq! { ThinString, &'a str }
impl_eq! { Cow<'a, str>, ThinString }

impl Default for ThinString {
    /// Creates an empty `String`.
    #[inline]
    fn default() -> ThinString {
        ThinString::new()
    }
}

impl fmt::Display for ThinString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl fmt::Debug for ThinString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl hash::Hash for ThinString {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        (**self).hash(hasher)
    }
}

impl Add<&str> for ThinString {
    type Output = ThinString;

    #[inline]
    fn add(mut self, other: &str) -> ThinString {
        self.push_str(other);
        self
    }
}

impl AddAssign<&str> for ThinString {
    #[inline]
    fn add_assign(&mut self, other: &str) {
        self.push_str(other);
    }
}

impl ops::Index<ops::Range<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::Range<usize>) -> &str {
        &self[..][index]
    }
}

impl ops::Index<ops::RangeTo<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeTo<usize>) -> &str {
        &self[..][index]
    }
}

impl ops::Index<ops::RangeFrom<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeFrom<usize>) -> &str {
        &self[..][index]
    }
}

impl ops::Index<ops::RangeFull> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &str {
        unsafe { from_utf8_unchecked(&self.vec) }
    }
}

impl ops::Index<ops::RangeInclusive<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeInclusive<usize>) -> &str {
        Index::index(&**self, index)
    }
}

impl ops::Index<ops::RangeToInclusive<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeToInclusive<usize>) -> &str {
        Index::index(&**self, index)
    }
}

impl ops::IndexMut<ops::Range<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::Range<usize>) -> &mut str {
        &mut self[..][index]
    }
}

impl ops::IndexMut<ops::RangeTo<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeTo<usize>) -> &mut str {
        &mut self[..][index]
    }
}

impl ops::IndexMut<ops::RangeFrom<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeFrom<usize>) -> &mut str {
        &mut self[..][index]
    }
}

impl ops::IndexMut<ops::RangeFull> for ThinString {
    #[inline]
    fn index_mut(&mut self, _index: ops::RangeFull) -> &mut str {
        unsafe { from_utf8_unchecked_mut(&mut *self.vec) }
    }
}

impl ops::IndexMut<ops::RangeInclusive<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeInclusive<usize>) -> &mut str {
        IndexMut::index_mut(&mut **self, index)
    }
}

impl ops::IndexMut<ops::RangeToInclusive<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeToInclusive<usize>) -> &mut str {
        IndexMut::index_mut(&mut **self, index)
    }
}

impl ops::Deref for ThinString {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        unsafe { from_utf8_unchecked(&self.vec) }
    }
}

impl ops::DerefMut for ThinString {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        unsafe { from_utf8_unchecked_mut(&mut *self.vec) }
    }
}

pub type ParseError = core::convert::Infallible;

impl FromStr for ThinString {
    type Err = core::convert::Infallible;
    #[inline]
    fn from_str(s: &str) -> Result<ThinString, Self::Err> {
        Ok(ThinString::from(s))
    }
}

impl ToString for ThinString {
    #[inline]
    fn to_string(&self) -> String {
        unsafe { String::from_utf8_unchecked(self.vec.to_vec()) }
    }
}

impl From<String> for ThinString {
    #[inline]
    fn from(string: String) -> ThinString {
        ThinString::from(string.as_str())
    }
}

impl From<ThinString> for String {
    #[inline]
    fn from(string: ThinString) -> String {
        string.to_string()
    }
}

pub trait ToThinString {
    fn to_thin_string(&self) -> ThinString;
}

impl<T: fmt::Display + ?Sized> ToThinString for T {
    #[inline]
    default fn to_thin_string(&self) -> ThinString {
        let mut buf = ThinString::new();
        let mut formatter = core::fmt::Formatter::new(&mut buf);
        // Bypass format_args!() to avoid write_str with zero-length strs
        fmt::Display::fmt(self, &mut formatter)
            .expect("a Display implementation returned an error unexpectedly");
        buf
    }
}

impl ToThinString for char {
    #[inline]
    fn to_thin_string(&self) -> ThinString {
        ThinString::from(self.encode_utf8(&mut [0; 4]))
    }
}

impl ToThinString for u8 {
    #[inline]
    fn to_thin_string(&self) -> ThinString {
        let mut buf = ThinString::with_capacity(3);
        let mut n = *self;
        if n >= 10 {
            if n >= 100 {
                buf.push((b'0' + n / 100) as char);
                n %= 100;
            }
            buf.push((b'0' + n / 10) as char);
            n %= 10;
        }
        buf.push((b'0' + n) as char);
        buf
    }
}

impl ToThinString for i8 {
    #[inline]
    fn to_thin_string(&self) -> ThinString {
        let mut buf = ThinString::with_capacity(4);
        if self.is_negative() {
            buf.push('-');
        }
        let mut n = self.unsigned_abs();
        if n >= 10 {
            if n >= 100 {
                buf.push('1');
                n -= 100;
            }
            buf.push((b'0' + n / 10) as char);
            n %= 10;
        }
        buf.push((b'0' + n) as char);
        buf
    }
}

impl ToThinString for str {
    #[inline]
    fn to_thin_string(&self) -> ThinString {
        ThinString::from(self)
    }
}

impl ToThinString for Cow<'_, str> {
    #[inline]
    fn to_thin_string(&self) -> ThinString {
        self[..].to_thin_string()
    }
}

impl ToThinString for ThinString {
    #[inline]
    fn to_thin_string(&self) -> ThinString {
        self.to_owned()
    }
}

impl AsRef<str> for ThinString {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl AsMut<str> for ThinString {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}

impl AsRef<[u8]> for ThinString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl From<&str> for ThinString {
    fn from(s: &str) -> ThinString {
        let mut vec = ThinVec::with_capacity(s.bytes().len());
        vec.extend_from_slice(s.as_bytes());
        ThinString { vec }
    }
}

impl From<&mut str> for ThinString {
    #[inline]
    fn from(s: &mut str) -> ThinString {
        let mut vec = ThinVec::with_capacity(s.bytes().len());
        vec.extend_from_slice(s.as_bytes());
        ThinString { vec }
    }
}

impl From<&ThinString> for ThinString {
    #[inline]
    fn from(s: &ThinString) -> ThinString {
        s.clone()
    }
}

impl<'a> From<Cow<'a, str>> for ThinString {
    fn from(s: Cow<'a, str>) -> ThinString {
        s.to_thin_string()
    }
}

impl<'a> From<&'a ThinString> for Cow<'a, str> {
    #[inline]
    fn from(s: &'a ThinString) -> Cow<'a, str> {
        Cow::Borrowed(s.as_str())
    }
}

impl From<ThinString> for ThinVec<u8> {
    fn from(string: ThinString) -> ThinVec<u8> {
        string.into_bytes()
    }
}

impl fmt::Write for ThinString {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}

pub struct Drain<'a> {
    /// Will be used as &'a mut ThinString in the destructor
    string: *mut ThinString,
    /// Start of part to remove
    start: usize,
    /// End of part to remove
    end: usize,
    /// Current remaining range to remove
    iter: Chars<'a>,
}

impl fmt::Debug for Drain<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_str()).finish()
    }
}

unsafe impl Sync for Drain<'_> {}
unsafe impl Send for Drain<'_> {}

impl Drop for Drain<'_> {
    fn drop(&mut self) {
        unsafe {
            // Use ThinVec::drain. "Reaffirm" the bounds checks to avoid
            // panic code being inserted again.
            let self_vec = (*self.string).as_mut_vec();
            if self.start <= self.end && self.end <= self_vec.len() {
                self_vec.drain(self.start..self.end);
            }
        }
    }
}

impl<'a> Drain<'a> {
    pub fn as_str(&self) -> &str {
        self.iter.as_str()
    }
}

impl Iterator for Drain<'_> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        self.next_back()
    }
}

impl DoubleEndedIterator for Drain<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        self.iter.next_back()
    }
}

impl FusedIterator for Drain<'_> {}

impl From<char> for ThinString {
    #[inline]
    fn from(c: char) -> Self {
        c.to_thin_string()
    }
}
