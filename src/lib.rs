use std::{slice, str};

/// Error that can occur during [`concat`](fn.concat.html).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The passed strs are not adjacent.
    NotAdjacent,
    /// The first str is too long for concatenation.
    TooLong,
}

/// Concatenate two string slices if they are adjacent.
///
/// If two strs are adjacent to each other in memory, this function
/// concatenates both, creating a single str.
///
/// # Errors
///
/// Returns `Err` if the two slices aren't adjacent, `a` is after `b`, or if
/// `a` is too long for proper concatenation (longer than `isize::MAX`).
///
/// # Examples
///
/// Correct usage:
///
/// ```rust
/// # use str_concat::concat;
/// let s = "0123456789";
/// assert_eq!("0123456", concat(&s[..5], &s[5..7]).unwrap());
/// ```
///
/// Non-adjacent string slices:
///
/// ```rust
/// # use str_concat::{concat, Error};
/// let s = "0123456789";
/// assert_eq!(Err(Error::NotAdjacent), concat(&s[..5], &s[6..7]))
/// ```
pub fn concat<'a>(a: &'a str, b: &'a str) -> Result<&'a str, Error> {
    let a_ptr = a.as_bytes().as_ptr();
    let b_ptr = b.as_bytes().as_ptr();
    
    unsafe {
        if a.len() > isize::max_value() as usize {
            return Err(Error::TooLong);
        }
        // https://doc.rust-lang.org/std/primitive.pointer.html#safety-1
        // * starting pointer in-bounds obviously
        // * ending pointer one byte past the end of an allocated object
        // * explicit isize overflow check above
        // * no wraparound required
        if a_ptr.offset(a.len() as isize) != b_ptr {
            return Err(Error::NotAdjacent);
        }
        // * strs are adjacent (checked above)
        // * no double-free / leak because we work on borrowed data
        // * no use-after-free because `a` and `b` have same lifetime
        let slice = slice::from_raw_parts(a_ptr, a.len() + b.len());
        // * concatenating two valid UTF8 strings will produce a valid UTF8 string
        // * a BOM in `b` is still valid:
        //   > It is important to understand that the character U+FEFF appearing at
        //   > any position other than the beginning of a stream MUST be interpreted
        //   > with the semantics for the zero-width non-breaking space, and MUST
        //   > NOT be interpreted as a signature.
        // * the grapheme *clusters* (and thus potentially the semantics of the string
        //   might change if the first code point of `b` is a combining character,
        //   a zero width joiner or similar.
        //   This does not affect the correctness of UTF-8.
        Ok(str::from_utf8_unchecked(slice))
    }
}

/// Concatenate two adjacent string slices no matter their order.
///
/// This is the same as [`concat`] except that it also concatenates
/// `b` to `a` if `b` is in front of `a` (in which case [`concat`] errors).
///
/// # Examples
///
/// Reversed order:
///
/// ```rust
/// # use str_concat::concat_unordered;
/// let s = "0123456789";
/// assert_eq!("0123456", concat_unordered(&s[5..7], &s[..5]).unwrap());
/// ```
///
/// Normal order:
///
/// ```rust
/// # use str_concat::{concat_unordered, Error};
/// let s = "0123456789";
/// assert_eq!("0123456", concat_unordered(&s[..5], &s[5..7]).unwrap())
/// ```
///
/// [`concat`]: fn.concat.html
pub fn concat_unordered<'a>(a: &'a str, b: &'a str) -> Result<&'a str, Error> {
    // add lengths to handle empty-string cases correctly
    let a_ptr = a.as_bytes().as_ptr() as usize + a.len();
    let b_ptr = b.as_bytes().as_ptr() as usize + b.len();
    
    // make the order of `a` and `b` not matter
    let (a, b) = if a_ptr <= b_ptr {
        (a, b)
    } else {
        (b, a)
    };

    concat(a, b)
}

#[cfg(test)]
mod tests {
    use super::{concat, concat_unordered, Error};

    #[test]
    fn simple_success() {
        let s = "0123456789";
        assert_eq!(Ok("0123456"), concat(&s[..5], &s[5..7]));
        assert_eq!(Ok("0123456"), concat_unordered(&s[..5], &s[5..7]));
    }

    #[test]
    fn unordered() {
        let s = "0123456789";
        assert_eq!(Err(Error::NotAdjacent), concat(&s[5..7], &s[..5]));
        assert_eq!(Ok("0123456"), concat_unordered(&s[5..7], &s[..5]));
    }

    #[test]
    fn simple_fail() {
        let s = "0123456789";
        assert_eq!(Err(Error::NotAdjacent), concat(&s[..5], &s[6..7]))
    }

    #[test]
    fn zero_width_joiner() {
        let s = "0\u{200d}1";
        assert_eq!(Ok("0\u{200d}1"), concat(&s[..1], &s[1..5]));
    }

    #[test]
    fn zero_width_joiner_combining_grave() {
        let s = "0\u{200d}̀1";
        assert_eq!(Ok("0\u{200d}\u{300}1"), concat(&s[..1], &s[1..7]));
    }

    #[test]
    fn bom() {
        let s = "0\u{FEFF}1";
        assert_eq!(Ok("0\u{FEFF}1"), concat(&s[..1], &s[1..5]));
    }

    #[test]
    fn empty_str() {
        let s = "0123";
        assert_eq!(Ok("0123"), concat(&s[..0], s));
        assert_eq!(Ok("0123"), concat_unordered(&s[..0], s));
        assert_eq!(Ok("0123"), concat(s, &s[4..]));
        assert_eq!(Ok("0123"), concat_unordered(s, &s[4..]));
    }
}
