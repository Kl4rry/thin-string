# thin-string
ThinString is a mirror of String except it stores len and capacity in the allocation on the heap.  
It uses [thin_vec](https://github.com/Gankra/thin-vec) internally instead of a vec. ThinString makes a best effort to support the whole std api where possible.


