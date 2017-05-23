//! This module defines the `White` trait and some helpful structs.

use super::stream::StrStream;
use std::io;
use std::result;

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
/// use whiteread::White;
/// let mut stream = "123".split_whitespace();
/// assert_eq!(<i32 as White>::read(&mut stream).unwrap(), 123)
/// ```
///
/// Semantics of provided trait implementations:
///
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::Lengthed;
/// // tuples (up to 3)
/// assert_eq!(parse_string("2 1 3 4").ok(), Some( ((2, 1), (3, 4)) ));
///
/// // eager vector
/// assert_eq!(parse_string("2 1 3 4").ok(), Some( vec![2, 1, 3, 4] ));
///
/// // vec prefixed with length
/// assert_eq!(parse_string("2 1 3").ok(), Some( Lengthed(vec![1, 3]) ));
///
/// // you can mix impls of course
/// assert_eq!(parse_string("a 1 b 2").ok(), Some( vec![('a', 1), ('b', 2)] ));
/// ```
pub trait White: Sized {
    fn read<I: StrStream>(it: &mut I) -> Result<Self>;
}

pub type Result<T> = result::Result<T, Error>;

/// Error which can occur while parsing `White` object.
///
/// It's convertible into `io::Error`, so it composes well with other reading functions.
///
/// # Examples
///
/// ```
/// # use whiteread::{parse_string, TooShort, Leftovers, ParseError};
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
pub use self::Error::*;

/// # Variants checking
impl Error {
    pub fn is_too_short(&self) -> bool {
        match *self {
            TooShort => true,
            _ => false,
        }
    }

    pub fn is_leftovers(&self) -> bool {
        match *self {
            Leftovers => true,
            _ => false,
        }
    }

    pub fn is_parse_error(&self) -> bool {
        match *self {
            ParseError => true,
            _ => false,
        }
    }

    pub fn is_io_error(&self) -> bool {
        match *self {
            IoError(_) => true,
            _ => false,
        }
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        IoError(e)
    }
}

impl ::std::error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            TooShort => "not enough input to parse a value",
            Leftovers => "excessive input provided",
            ParseError => "parse error occured",
            IoError(ref e) => e.description(),
        }
    }

    fn cause(&self) -> Option<&::std::error::Error> {
        match *self {
            IoError(ref e) => e.cause(),
            _ => None,
        }
    }
}

impl ::std::fmt::Display for Error {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        use ::std::error::Error;
        match *self {
            IoError(ref e) => e.fmt(fmt),
            _ => fmt.write_str(self.description()),
        }
    }
}

impl From<Error> for io::Error {
    fn from(e: Error) -> io::Error {
        match e {
            IoError(e) => e,
            e => io::Error::new(io::ErrorKind::InvalidData, e),
        }
    }
}
// not using T: FromStr here because of coherence and tuples
macro_rules! white {
    ($T:ident) => (
        impl White for $T {
            fn read<I: StrStream>(it: &mut I) -> Result<$T> {
                try!( it.next() ).ok_or(TooShort).and_then( |s| s.parse().or(Err(ParseError)) )
            }
        }
    )
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

impl White for char {
    fn read<I: StrStream>(it: &mut I) -> Result<char> {
        let s = it.next()?;
        s.and_then(|s| s.chars().next()).ok_or(TooShort)
    }
}

impl<T: White, U: White> White for (T, U) {
    fn read<I: StrStream>(it: &mut I) -> Result<(T, U)> {
        Ok((White::read(it)?, White::read(it)?))
    }
}

impl<T: White, U: White, V: White> White for (T, U, V) {
    fn read<I: StrStream>(it: &mut I) -> Result<(T, U, V)> {
        Ok((White::read(it)?, White::read(it)?, White::read(it)?))
    }
}

impl White for () {
    fn read<I: StrStream>(_: &mut I) -> Result<()> {
        Ok(())
    }
}

impl<T: White> White for Vec<T> {
    fn read<I: StrStream>(it: &mut I) -> Result<Vec<T>> {
        let mut v = vec![];
        loop {
            match White::read(it) {
                Err(TooShort) => break,
                x => v.push(x?),
            }
        }
        Ok(v)
    }
}

/// Used to consume and ignore one whitespace-separated value
///
/// # Examples
///
/// Providing type hint
///
/// ```
/// # use whiteread::{parse_string, Skip};
/// let (_, x, _): (Skip, i32, Skip) = parse_string("foo 5 30").unwrap();
/// assert_eq!(x, 5);
/// ```
///
/// Relying on type inference (for some reason, {} are mandatory)
///
/// ```
/// # use whiteread::{parse_string, Skip};
/// let (Skip{}, x, Skip{}) = parse_string("foo 5 30").unwrap();
/// let x: i32 = x;
/// assert_eq!(x, 5);
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct Skip;

impl White for Skip {
    fn read<I: StrStream>(it: &mut I) -> Result<Skip> {
        it.next()?;
        Ok(Skip)
    }
}

/// Used to ignore everything till the end of the reader
///
/// Using this should be only necessary in conjuction with `parse_line`
/// and `parse_string`, to avoid the `Leftovers` error.
/// When using `Reader`, you can just use `start_line` or `parse`
/// instead.
///
/// # Examples
///
/// Providing type hint
///
/// ```
/// # use whiteread::{parse_string, SkipAll};
/// let (s, x, _): (String, i32, SkipAll) = parse_string("foo 5 ... ... ...").unwrap();
/// assert_eq!((s, x), ("foo".to_owned(), 5));
/// ```
///
/// Relying on type inference (for some reason, {} are mandatory)
///
/// ```
/// # use whiteread::{parse_string, SkipAll};
/// let (s, x, SkipAll{}) = parse_string("foo 5").unwrap();
/// let x: i32 = x;
/// let s: String = s;
/// assert_eq!((s, x), ("foo".to_owned(), 5));
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct SkipAll;

impl White for SkipAll {
    fn read<I: StrStream>(it: &mut I) -> Result<SkipAll> {
        while let Some(_) = it.next()? {};
        Ok(SkipAll)
    }
}

/// Wrapper for reading vector of values represented by a list prepended by a number of elements.
///
/// # Examples
/// ```
/// # use whiteread::{parse_string, Lengthed};
/// let Lengthed(v): Lengthed<u8> = parse_string("3 5 6 7").unwrap();
/// assert_eq!(v, &[5, 6, 7]);
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct Lengthed<T>(pub Vec<T>);

impl<T: White> White for Lengthed<T> {
    fn read<I: StrStream>(it: &mut I) -> Result<Lengthed<T>> {
        let sz = White::read(it)?;
        let mut v = Vec::with_capacity(sz);
        loop {
            v.push(White::read(it)?);
            if v.len() == sz {
                return Ok(Lengthed(v));
            }
        }
    }
}

/// Wrapper for reading vector of numbers represented by a list ending with 0.
///
/// # Examples
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::white::{Zeroed, Error};
/// let (Zeroed(v), _): (Zeroed<u8>, String) = parse_string("20 21 22 0 foo").unwrap();
/// assert_eq!(v, &[20, 21, 22]);
///
/// assert!(parse_string::<Zeroed<u8>>("20 21 22").is_err());
/// ```
#[derive(Debug)]
pub struct Zeroed<T>(pub Vec<T>);

impl<T: White + Default + PartialEq> White for Zeroed<T> {
    fn read<I: StrStream>(it: &mut I) -> Result<Zeroed<T>> {
        let mut v = vec![];
        let zero = Default::default();
        loop {
            let x = White::read(it)?;
            if x == zero {
                return Ok(Zeroed(v));
            } else {
                v.push(x)
            }
        }
    }
}

