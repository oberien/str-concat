#![no_std]
use core::{mem, slice, str};

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
/// # Safety
///
/// The provided slices must come from the same underlying allocation. The adjacency test can not
/// reliably differentiate between the one-past-the-end pointer of one allocation and the start of
/// another. However, all slices must be within a single allocation.
///
/// # Examples
///
/// Correct usage:
///
/// ```rust
/// # use str_concat::concat;
/// let s = "0123456789";
/// unsafe {
///     // SAFETY: slices from the same str originally.
///     assert_eq!("0123456", concat(&s[..5], &s[5..7]).unwrap());
/// }
/// ```
///
/// Non-adjacent string slices:
///
/// ```rust
/// # use str_concat::{concat, Error};
/// let s = "0123456789";
/// unsafe {
///     // SAFETY: slices from the same str originally.
///     assert_eq!(Err(Error::NotAdjacent), concat(&s[..5], &s[6..7]))
/// }
/// ```
pub unsafe fn concat<'a>(a: &'a str, b: &'a str) -> Result<&'a str, Error> {
    let slice = concat_slice(a.as_bytes(), b.as_bytes())?;

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

/// Concatenate two slices if they are adjacent.
///
/// If two slices are adjacent to each other in memory, this function
/// concatenates both, creating a single longer slice. Note that slices of
/// zero-sized types (ZST) are never considered adjacent. Otherwise it would be
/// possible to concatenate a slice to itself.
///
/// # Errors
///
/// Returns `Err` if the two slices aren't adjacent, `a` is after `b`, or if the
/// result is too long to be represented as a slice (size in bytes is larger
/// than `isize::MAX`).
///
/// When T is a ZST then returns `Err(TooLong)` if the total length would overflow
/// `usize` and `Err(NotAdjacent)` otherwise.
///
/// # Safety
///
/// The provided slices must come from the same underlying allocation. The adjacency test can not
/// reliably differentiate between the one-past-the-end pointer of one allocation and the start of
/// another. However, all slices must be within a single allocation.
///
/// # Examples
///
/// Correct usage:
///
/// ```rust
/// # use str_concat::concat_slice;
/// let s = b"0123456789";
/// unsafe {
///     // SAFETY: slices from the same bytes originally.
///     assert_eq!(b"0123456", concat_slice(&s[..5], &s[5..7]).unwrap());
/// }
/// ```
///
/// Non-adjacent byte slices:
///
/// ```rust
/// # use str_concat::{concat_slice, Error};
/// let s = b"0123456789";
/// unsafe {
///     // SAFETY: slices from the same bytes originally.
///     assert_eq!(Err(Error::NotAdjacent), concat_slice(&s[..5], &s[6..7]))
/// }
/// ```
///
pub unsafe fn concat_slice<'a, T>(a: &'a [T], b: &'a [T]) -> Result<&'a [T], Error> {
    let a_ptr = a.as_ptr();
    let b_ptr = b.as_ptr();

    let a_len = a.len();
    let b_len = b.len();

    if mem::size_of::<T>() == 0 {
        // Not safety critical but we check that the length is as expected.
        if a_len.checked_add(b_len).is_none() {
            return Err(Error::TooLong)
        }

        // Never consider ZST slices adjacent. You could otherwise infinitely
        // duplicate a non-zero length slice by concatenating it to itself.
        return Err(Error::NotAdjacent)
    }

    // `max_len <= isize::max_value()`
    let max_len = isize::max_value() as usize / mem::size_of::<T>();

    // These should be guaranteed for the slices.
    assert!(a_len <= max_len as usize);
    assert!(b_len <= max_len as usize);

    // https://doc.rust-lang.org/std/primitive.pointer.html#safety-1
    // * starting pointer in-bounds obviously
    // * ending pointer one byte past the end of an allocated object
    // * explicit isize overflow check above
    // * no wraparound required
    // why: this is the one byte past the end pointer for the input slice `a`
    if a_ptr.offset(a_len as isize) != b_ptr {
        return Err(Error::NotAdjacent);
    }
    // UNWRAP: both smaller than isize, can't wrap in usize.
    // This is because in rust `usize` and `isize` are both guaranteed to have
    // the same number of bits as a pointer [1]. As `isize` is signed, a `usize`
    // can always store the sum of two positive `isize`.
    // [1]: https://doc.rust-lang.org/reference/types/numeric.html#machine-dependent-integer-types
    let new_len = a_len.checked_add(b_len).unwrap();
    // Ensure the length is bounded. The bound is strict from the definition of `max_len`
    // `new_len <= max_len` <=> `new_len * mem::size_of::<T>() <= isize::max_value()`
    if !(new_len <= max_len) {
        return Err(Error::TooLong);
    }
    // https://doc.rust-lang.org/std/slice/fn.from_raw_parts.html#safety
    // * slices are adjacent (checked above)
    // * no double-free / leak because we work on borrowed data
    // * no use-after-free because `a` and `b` have same lifetime
    // * the total size is smaller than `isize::MAX` bytes, as max_len is rounded down
    Ok(slice::from_raw_parts(a_ptr, new_len))
}

/// Concatenate two adjacent string slices no matter their order.
///
/// This is the same as [`concat`] except that it also concatenates
/// `b` to `a` if `b` is in front of `a` (in which case [`concat`] errors).
///
/// # Safety
///
/// The provided slices must come from the same underlying allocation. The adjacency test can not
/// reliably differentiate between the one-past-the-end pointer of one allocation and the start of
/// another. However, all slices must be within a single allocation.
///
/// # Examples
///
/// Reversed order:
///
/// ```rust
/// # use str_concat::concat_unordered;
/// let s = "0123456789";
/// unsafe {
///     // SAFETY: slices from the same str originally.
///     assert_eq!("0123456", concat_unordered(&s[5..7], &s[..5]).unwrap());
/// }
/// ```
///
/// Normal order:
///
/// ```rust
/// # use str_concat::{concat_unordered, Error};
/// let s = "0123456789";
/// unsafe {
///     // SAFETY: slices from the same str originally.
///     assert_eq!("0123456", concat_unordered(&s[..5], &s[5..7]).unwrap())
/// }
/// ```
///
/// [`concat`]: fn.concat.html
pub unsafe fn concat_unordered<'a>(a: &'a str, b: &'a str) -> Result<&'a str, Error> {
    // add lengths to handle empty-string cases correctly
    let a_ptr = a.as_bytes().as_ptr() as usize;
    let a_end_ptr = a_ptr + a.len();
    let b_ptr = b.as_bytes().as_ptr() as usize;

    // make the order of `a` and `b` not matter
    let (a, b) = if a_ptr <= b_ptr && a_end_ptr <= b_ptr {
        (a, b)
    } else {
        (b, a)
    };

    concat(a, b)
}

/// Concatenate two adjacent slices no matter their order.
///
/// This is the same as [`concat_slice`] except that it also concatenates `b` to
/// `a` if `b` is in front of `a` (in which case of [`concat_slice`] errors).
/// Keep in mind that slices of ZSTs will still not be concatenated.
///
/// # Safety
///
/// The provided slices must come from the same underlying allocation. The adjacency test can not
/// reliably differentiate between the one-past-the-end pointer of one allocation and the start of
/// another. However, all slices must be within a single allocation.
///
/// # Examples
///
/// Reversed order:
///
/// ```rust
/// # use str_concat::concat_slice_unordered;
/// let s = b"0123456789";
/// unsafe {
///     // SAFETY: slices from the same bytes originally.
///     assert_eq!(b"0123456", concat_slice_unordered(&s[5..7], &s[..5]).unwrap());
/// }
/// ```
///
/// Normal order:
///
/// ```rust
/// # use str_concat::{concat_slice_unordered, Error};
/// let s = b"0123456789";
/// unsafe {
///     // SAFETY: slices from the same bytes originally.
///     assert_eq!(b"0123456", concat_slice_unordered(&s[..5], &s[5..7]).unwrap())
/// }
/// ```
///
/// [`concat_slice`]: fn.concat_slice.html
pub unsafe fn concat_slice_unordered<'a, T>(a: &'a [T], b: &'a [T]) -> Result<&'a [T], Error> {
    // add lengths to handle empty cases correctly
    let a_ptr = a.as_ptr() as usize;
    let a_end_ptr = a_ptr + a.len() * mem::size_of::<T>();
    let b_ptr = b.as_ptr() as usize;

    // make the order of `a` and `b` not matter
    let (a, b) = if a_ptr <= b_ptr && a_end_ptr <= b_ptr {
        (a, b)
    } else {
        (b, a)
    };

    concat_slice(a, b)
}

#[cfg(test)]
mod tests {
    use super::{concat, concat_unordered, concat_slice, concat_slice_unordered, Error};

    #[test]
    fn simple_success() {
        let s = "0123456789";
        unsafe {
            assert_eq!(Ok("0123456"), concat(&s[..5], &s[5..7]));
            assert_eq!(Ok("0123456"), concat_unordered(&s[..5], &s[5..7]));
        }
    }

    #[test]
    fn unordered() {
        let s = "0123456789";
        unsafe {
            assert_eq!(Err(Error::NotAdjacent), concat(&s[5..7], &s[..5]));
            assert_eq!(Ok("0123456"), concat_unordered(&s[5..7], &s[..5]));
        }
    }

    #[test]
    fn simple_fail() {
        let s = "0123456789";
        unsafe {
            assert_eq!(Err(Error::NotAdjacent), concat(&s[..5], &s[6..7]))
        }
    }

    #[test]
    fn zero_width_joiner() {
        let s = "0\u{200d}1";
        unsafe {
            assert_eq!(Ok("0\u{200d}1"), concat(&s[..1], &s[1..5]));
        }
    }

    #[test]
    fn zero_width_joiner_combining_grave() {
        let s = "0\u{200d}̀1";
        unsafe {
            assert_eq!(Ok("0\u{200d}\u{300}1"), concat(&s[..1], &s[1..7]));
        }
    }

    #[test]
    fn bom() {
        let s = "0\u{FEFF}1";
        unsafe {
            assert_eq!(Ok("0\u{FEFF}1"), concat(&s[..1], &s[1..5]));
        }
    }

    #[test]
    fn empty_str() {
        let s = "0123";
        unsafe {
            assert_eq!(Ok("0123"), concat(&s[..0], s));
            assert_eq!(Ok("0123"), concat_unordered(&s[..0], s));
            assert_eq!(Ok("0123"), concat_unordered(s, &s[..0]));
            assert_eq!(Ok("0123"), concat(s, &s[4..]));
            assert_eq!(Ok("0123"), concat_unordered(s, &s[4..]));
            assert_eq!(Ok("0123"), concat_unordered(&s[4..], s));
        }
    }

    #[test]
    fn typed_slices() {
        #[derive(Debug, PartialEq)]
        struct T(usize);

        let s: &[T] = &[T(0), T(1), T(2), T(3)][..];
        unsafe {
            assert_eq!(Ok(s), concat_slice(&s[..2], &s[2..]));
            assert_eq!(Ok(s), concat_slice_unordered(&s[..2], &s[2..]));
            assert_eq!(Ok(s), concat_slice_unordered(&s[2..], &s[..2]));

            // One slice empty
            assert_eq!(Ok(s), concat_slice(&s[..0], s));
            assert_eq!(Ok(s), concat_slice_unordered(&s[..0], s));
            assert_eq!(Ok(s), concat_slice_unordered(s, &s[..0]));
            assert_eq!(Ok(s), concat_slice(s, &s[4..]));
            assert_eq!(Ok(s), concat_slice_unordered(s, &s[4..]));
            assert_eq!(Ok(s), concat_slice_unordered(&s[4..], s));
        }
    }

    #[test]
    fn typed_fail() {
        #[derive(Debug, PartialEq)]
        struct T(usize);

        let s: &[T] = &[T(0), T(1), T(2), T(3)][..];
        unsafe {
            assert_eq!(Err(Error::NotAdjacent), concat_slice(&s[..1], &s[2..]));
            assert_eq!(Err(Error::NotAdjacent), concat_slice_unordered(&s[..1], &s[2..]));
            assert_eq!(Err(Error::NotAdjacent), concat_slice(&s[2..], &s[..2]));
        }
    }
}
