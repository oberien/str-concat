# str-concat

[![Crates.io](https://img.shields.io/crates/v/str-concat.svg)](https://crates.io/crates/str-concat)
[![Docs.rs](https://docs.rs/str-concat/badge.svg)](https://docs.rs/str-concat/)

Concatenate two adjacent string slices.

# Examples

```rust
use str_concat::{concat, concat_unordered, Error};

fn main() {
    let s = "0123456789";
    // ordered, `a` before `b`
    assert_eq!(Ok("0123456"), concat(&s[..5], &s[5..7]));
    assert_eq!(Ok("0123456"), concat_unordered(&s[..5], &s[5..7]));

    // unordered, `b` before `a`
    assert_eq!(Err(Error::NotAdjacent), concat(&s[5..7], &s[..5]));
    assert_eq!(Ok("0123456"), concat_unordered(&s[5..7], &s[..5]));
}
```

# Safety

It is generally not safe to concatenate two adjacent slices.
This is explained in [#8], [bluss/odds#25], [rust-lang/rust#66111], [rust-lang/rust#62765], [rust-lang/rfcs#2806] and [tokio-rs/bytes#347].
To sum it up, when rust calculates offset to borrow part of a referenced type such as a slice, it makes the assumption that those offsets stem from the same allocation.
If two different allocations are adjacent to each other, the `concat*` functions in this crate would readily combine them, breaking internal assumptions of `rustc` and thus may result in UB.
Therefore, all functions in this crate are marked as `unsafe`.
The user must ensure that the slices to be concatenated stem from the same allocation (the same `String`, `Vec<_>`, …).

Another edge-case are zero-sized types (ZST).
Multiple slices over different ZST may point to the same memory-region.
That is because instances of ZSTs, including slices, can not be identified by their address even for different types.
This is because a ZST does not occupy any space, it does not "alias" any memory.
As such, there is no need to actually allocate any space during runtime when using a ZST (or a `Vec` or slice of it).
Instead, a slice to ZSTs may point to the smallest non-zero address with the correct alignment (for example `vec![()].as_ptr() as usize == 1`).
Technically it's sound to arbitrarily elongate a slice of ZST given it already contains at least one element.
However, we decided that semantically it doesn't make sense to use this functionality.
As we also don't have any way to tell that two ZST slices are adjacent, we decided to always return an error if two ZST slices are passed to be concatenated.
For further reading surrounding this issue with ZST slices, see [#5], [rust-lang/unsafe-code-guidelines#93] and [rust-lang/unsafe-code-guidelines#168].

[#8]: https://github.com/oberien/str-concat/issues/8
[rust-lang/rfcs#2806]: https://github.com/rust-lang/rfcs/pull/2806
[tokio-rs/bytes#347]: https://github.com/tokio-rs/bytes/issues/347
[rust-lang/rust#66111]: https://github.com/rust-lang/rust/pull/66111
[bluss/odds#25]: https://github.com/bluss/odds/issues/25
[rust-lang/rust#62765]: https://github.com/rust-lang/rust/issues/62765
[#5]: https://github.com/oberien/str-concat/issues/5
[rust-lang/unsafe-code-guidelines#93]: https://github.com/rust-lang/unsafe-code-guidelines/issues/93#issuecomment-512178989
[rust-lang/unsafe-code-guidelines#168]: https://github.com/rust-lang/unsafe-code-guidelines/issues/168


# License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
