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
    position: usize,
}

impl<'a> SplitAsciiWhitespace<'a> {
    pub fn new(s: &'a str) -> Self { SplitAsciiWhitespace { s: s, position: 0 } }

    pub fn position(&self) -> usize { self.position }

    pub fn from_parts(s: &'a str, position: usize) -> Self {
        SplitAsciiWhitespace { s: s, position: position }
    }
}

impl<'a> Iterator for SplitAsciiWhitespace<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        let bytes = self.s.as_bytes();
        let mut start = self.position;
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
        self.position = end;
        if start != end {
            Some(&self.s[start..end])
        } else {
            None
        }
    }
}

impl<'a> StrStream for SplitAsciiWhitespace<'a> {
    fn next(&mut self) -> io::Result<Option<&str>> {
        Ok(Iterator::next(self))
    }
}

/// Extends a `str` with `split_ascii_whitespace` method.
pub trait StrExt {
    fn split_ascii_whitespace(&self) -> SplitAsciiWhitespace;
}

impl StrExt for str {
    fn split_ascii_whitespace(&self) -> SplitAsciiWhitespace {
        SplitAsciiWhitespace::new(self)
    }
}

