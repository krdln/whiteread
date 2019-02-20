//! This module defines the `StrStream` and `FromStream` traits
//!
//! The [`FromStream`] trait defines how to convert a
//! [`StrStream`](trait.StrStream.html) (a stream of strings)
//! to a value. See [its definition][`FromStream`] for more documentation.

use std::io;
use std::str::SplitWhitespace;

/// A streaming iterator yielding borrowed strings.
pub trait StrStream {
    fn next(&mut self) -> io::Result<Option<&str>>;
}

impl<'a> StrStream for SplitWhitespace<'a> {
    fn next(&mut self) -> io::Result<Option<&str>> { Ok(Iterator::next(self)) }
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
        SplitAsciiWhitespace {
            s: s,
            position: position,
        }
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
    fn next(&mut self) -> io::Result<Option<&str>> { Ok(Iterator::next(self)) }
}

/// Extends a `str` with `split_ascii_whitespace` method.
pub trait StrExt {
    fn split_ascii_whitespace(&self) -> SplitAsciiWhitespace;
}

impl StrExt for str {
    fn split_ascii_whitespace(&self) -> SplitAsciiWhitespace { SplitAsciiWhitespace::new(self) }
}

/// Trait for values that can be parsed from stream of whitespace-separated words.
///
/// Implementations for primtives consume and parse one element from a stream
/// (advancing a stream).
/// Implementations for tuples just parse elements from left to right.
/// Implementation for vector parses till the end of stream.
///
/// # Examples
///
/// Using a trait directly
///
/// ```
/// use whiteread::FromStream;
/// let mut stream = "123".split_whitespace();
/// assert_eq!(<i32 as FromStream>::read(&mut stream).unwrap(), 123)
/// ```
///
/// Semantics of provided trait implementations:
///
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::adapters::{Skip, Lengthed};
/// // tuples (up to 6)
/// assert_eq!(parse_string("2 1 3 4").ok(), Some( ((2, 1), (3, 4)) ));
///
/// // eager vector
/// assert_eq!(parse_string("2 1 3 4").ok(), Some( vec![2, 1, 3, 4] ));
///
/// // vec prefixed with length
/// assert_eq!(parse_string("2 1 3").ok(), Some( Lengthed(vec![1, 3]) ));
///
/// // placeholder
/// assert_eq!(parse_string("spam 3").ok(), Some( (Skip, 3) ));
///
/// // you can mix impls of course
/// assert_eq!(parse_string("a 1 b 2").ok(), Some( vec![('a', 1), ('b', 2)] ));
/// ```
///
/// There are a few more structs in this module,
/// which implement the `FromStream` trait in various way.
/// See their definition for more explanation.
pub trait FromStream: Sized {
    fn read<I: StrStream>(it: &mut I) -> Result<Self>;
}

pub type Result<T> = ::std::result::Result<T, Error>;

/// Error which can occur while parsing `FromStream` object.
///
/// It's convertible into `io::Error`, so it composes well with other reading functions.
///
/// # Examples
///
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::stream::Error::*;
/// if let Err(TooShort) = parse_string::<(u8, u16)>("1") {} else { panic!(); }
/// if let Err(Leftovers) = parse_string::<char>("x y z") {} else { panic!(); }
/// if let Err(ParseError) = parse_string::<i32>("seven") {} else { panic!(); }
/// ```
#[derive(Debug)]
pub enum Error {
    /// There was not enough input to parse a value.
    TooShort,

    /// Excessive input was provided.
    Leftovers,

    /// Parse error occured (data was in invalid format).
    ParseError,

    /// IO Error occured.
    IoError(io::Error),
}

/// # Variants checking
impl Error {
    pub fn is_too_short(&self) -> bool {
        match *self {
            Error::TooShort => true,
            _ => false,
        }
    }

    pub fn is_leftovers(&self) -> bool {
        match *self {
            Error::Leftovers => true,
            _ => false,
        }
    }

    pub fn is_parse_error(&self) -> bool {
        match *self {
            Error::ParseError => true,
            _ => false,
        }
    }

    pub fn is_io_error(&self) -> bool {
        match *self {
            Error::IoError(_) => true,
            _ => false,
        }
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error { Error::IoError(e) }
}

impl ::std::error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            Error::TooShort => "not enough input to parse a value",
            Error::Leftovers => "excessive input provided",
            Error::ParseError => "parse error occured",
            Error::IoError(ref e) => e.description(),
        }
    }

    fn cause(&self) -> Option<&::std::error::Error> {
        #[allow(deprecated)] // Rust 1.15 doesn't have Error::source yet
        match *self {
            Error::IoError(ref e) => e.cause(),
            _ => None,
        }
    }
}

impl ::std::fmt::Display for Error {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        use std::error::Error as _StdError;
        match *self {
            Error::IoError(ref e) => e.fmt(fmt),
            _ => fmt.write_str(self.description()),
        }
    }
}

impl From<Error> for io::Error {
    fn from(e: Error) -> io::Error {
        match e {
            Error::IoError(e) => e,
            e => io::Error::new(io::ErrorKind::InvalidData, e),
        }
    }
}
// not using T: FromStr here because of coherence and tuples
macro_rules! white {
    ($T:ident) => {
        impl FromStream for $T {
            fn read<I: StrStream>(it: &mut I) -> Result<$T> {
                try!(it.next())
                    .ok_or(Error::TooShort)
                    .and_then(|s| s.parse().or(Err(Error::ParseError)))
            }
        }
    };
}

white!(bool);
white!(u8);
white!(u16);
white!(u32);
white!(u64);
white!(usize);
white!(i8);
white!(i16);
white!(i32);
white!(i64);
white!(isize);
white!(String);
white!(f32);
white!(f64);

impl FromStream for char {
    fn read<I: StrStream>(it: &mut I) -> Result<char> {
        let s = it.next()?;
        s.and_then(|s| s.chars().next()).ok_or(Error::TooShort)
    }
}

macro_rules! impl_tuple {
    ( $($x:ident),* ) => {
        impl< $( $x: FromStream ),* > FromStream for ( $( $x, )* ) {
            fn read<I: StrStream>(_it: &mut I) -> Result<Self> {
                Ok(( $( $x::read(_it)?, )* ))
            }
        }
    };
}

impl_tuple!();
impl_tuple!(A);
impl_tuple!(A, B);
impl_tuple!(A, B, C);
impl_tuple!(A, B, C, D);
impl_tuple!(A, B, C, D, E);
impl_tuple!(A, B, C, D, E, F);

impl<T: FromStream> FromStream for Vec<T> {
    fn read<I: StrStream>(it: &mut I) -> Result<Vec<T>> {
        let mut v = vec![];
        loop {
            match FromStream::read(it) {
                Err(Error::TooShort) => break,
                x => v.push(x?),
            }
        }
        Ok(v)
    }
}
