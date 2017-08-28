//! This module provides miscellaneous utility functions.

/// Conversion from something coercible to a string slice into `Box<str>`.
pub fn to_boxed_str<S: AsRef<str>>(s: S) -> Box<str> {
    s.as_ref().into()
}
