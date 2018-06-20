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

# License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
