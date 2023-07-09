# thin-string
`ThinString` is a mirror of `String` except it stores length and capacity in the allocation on the heap.  
It uses [thin_vec](https://github.com/Gankra/thin-vec) internally instead of a `Vec`. `ThinString` makes a best effort to support the whole std api where possible.

## Compiler support
`thin-string` requires a nightly toolchain as it currently uses unstable features to mirror the internals of `String`.


