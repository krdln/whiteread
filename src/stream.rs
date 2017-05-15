//! This module defines the `StrStream` trait.

use std::str::SplitWhitespace;
use std::io;

/// A streaming iterator yielding borrowed strings.
pub trait StrStream {
    fn next(&mut self) -> io::Result<Option<&str>>;
}

impl<'a> StrStream for SplitWhitespace<'a> {
    fn next(&mut self) -> io::Result<Option<&str>> {
        Ok(Iterator::next(self))
    }
}

/// Fast version of std::str::SplitWhitespace, but with some drawbacks.
///
/// It considers to be whitespace everything with codepoint <= 0x20
/// (this includes " \t\n\r", but also some other unprintable characters).
/// It doesn't consider to be whitespace any of non-ascii UTF whitespace characters
/// (such as non-breaking space).
pub struct SplitAsciiWhitespace<'a> {
    s: &'a str,
}

impl<'a> SplitAsciiWhitespace<'a> {
    pub fn new(s: &'a str) -> Self { SplitAsciiWhitespace { s: s } }
}

impl<'a> StrStream for SplitAsciiWhitespace<'a> {
    fn next(&mut self) -> io::Result<Option<&str>> {
        let bytes = self.s.as_bytes();
        let mut start = 0;
        while let Some(&c) = bytes.get(start) {
            if c > b' ' {
                break;
            }
            start += 1;
        }
        let mut end = start;
        while let Some(&c) = bytes.get(end) {
            if c <= b' ' {
                break;
            }
            end += 1;
        }
        let ret = if start != end {
            Ok(Some(unsafe { self.s.slice_unchecked(start, end) }))
        } else {
            Ok(None)
        };
        self.s = unsafe { self.s.slice_unchecked(end, bytes.len()) };
        ret
    }
}

/// Extends a `str` with `split_ascii_whitespace` method.
pub trait StrExt {
    fn split_ascii_whitespace(&self) -> SplitAsciiWhitespace;
}

impl StrExt for str {
    fn split_ascii_whitespace(&self) -> SplitAsciiWhitespace {
        SplitAsciiWhitespace { s: self }
    }
}

