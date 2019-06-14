//! This module defines adapters for [`FromStream`] trait.
//!
//! This module contains a few structs, which implement
//! [`FromStream`] in a special way. Eg. `Skip` serves the role
//! of a placeholder, and `Lengthed` allows to read a vector
//! prepended by its length.
//!
//! See also [implementation of `FromStream` for std types][impls]
//! which among implementation for primitives and strings,
//! contains implementation on tuples, `Vec` and `Option`.
//!
//! [impls]: ../stream/trait.FromStream.html#foreign-impls

use super::stream::{FromStream, Result, ResultExt, StrStream};

/// Used to consume and ignore one whitespace-separated value
///
/// # Examples
///
/// Providing type hint
///
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::adapters::Skip;
/// let (_, x, _): (Skip, i32, Skip) = parse_string("foo 5 30").unwrap();
/// assert_eq!(x, 5);
/// ```
///
/// Relying on type inference (for some reason, {} are mandatory)
///
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::adapters::Skip;
/// let (Skip{}, x, Skip{}) = parse_string("foo 5 30").unwrap();
/// let x: i32 = x;
/// assert_eq!(x, 5);
/// ```
#[derive(Default, Debug, Eq, PartialEq)]
pub struct Skip;

impl FromStream for Skip {
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
/// # use whiteread::parse_string;
/// # use whiteread::adapters::SkipAll;
/// let (s, x, _): (String, i32, SkipAll) = parse_string("foo 5 ... ... ...").unwrap();
/// assert_eq!((s, x), ("foo".to_owned(), 5));
/// ```
///
/// Relying on type inference (for some reason, {} are mandatory)
///
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::adapters::SkipAll;
/// let (s, x, SkipAll{}) = parse_string("foo 5").unwrap();
/// let x: i32 = x;
/// let s: String = s;
/// assert_eq!((s, x), ("foo".to_owned(), 5));
/// ```
#[derive(Default, Debug, Eq, PartialEq)]
pub struct SkipAll;

impl FromStream for SkipAll {
    fn read<I: StrStream>(it: &mut I) -> Result<SkipAll> {
        while let Some(_) = it.next()? {}
        Ok(SkipAll)
    }
}

/// Wrapper for reading vector of values represented by a list prepended by a number of elements.
///
/// # Examples
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::adapters::Lengthed;
/// let Lengthed(v): Lengthed<u8> = parse_string("3 5 6 7").unwrap();
/// assert_eq!(v, &[5, 6, 7]);
///
/// let Lengthed(v): Lengthed<u8> = parse_string("0").unwrap();
/// assert!(v.is_empty());
/// ```
#[derive(Default, Debug, Eq, PartialEq)]
pub struct Lengthed<T>(pub Vec<T>);

impl<T: FromStream> FromStream for Lengthed<T> {
    fn read<I: StrStream>(it: &mut I) -> Result<Lengthed<T>> {
        let sz = FromStream::read(it)?;
        let mut v = Vec::with_capacity(sz);
        loop {
            if v.len() == sz {
                return Ok(Lengthed(v));
            }
            v.push(FromStream::read(it).as_subsequent()?);
        }
    }
}

/// Wrapper for reading vector of numbers represented by a list ending with 0.
///
/// # Examples
///
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::adapters::Zeroed;
/// # use whiteread::stream::Error;
/// let (Zeroed(v), _): (Zeroed<u8>, String) = parse_string("20 21 22 0 foo").unwrap();
/// assert_eq!(v, &[20, 21, 22]);
///
/// assert!(parse_string::<Zeroed<u8>>("20 21 22").is_err());
/// ```
///
/// If the element can be represented by multiple words (eg. it's a tuple or a vector),
/// the full "zeroed" element should be provided:
///
/// ```
/// # use whiteread::parse_string;
/// # use whiteread::adapters::{Lengthed, Zeroed};
/// let _: Zeroed<(i32, i32)> = parse_string("22 33  44 55  0 0").unwrap();
/// let _: Zeroed<Lengthed<String>> = parse_string("3 a b c  2 d e  0").unwrap();
/// ```
#[derive(Default, Debug)]
pub struct Zeroed<T>(pub Vec<T>);

impl<T: FromStream + Default + PartialEq> FromStream for Zeroed<T> {
    fn read<I: StrStream>(it: &mut I) -> Result<Zeroed<T>> {
        let mut v = vec![];
        let zero = Default::default();
        loop {
            let result = FromStream::read(it);
            let x = if v.is_empty() { result? } else { result.as_subsequent()? };
            if x == zero {
                return Ok(Zeroed(v));
            } else {
                v.push(x)
            }
        }
    }
}

/// Hints the parsing function not to render errors
///
/// By default, [`Reader`](crate::Reader) will pretty-print the error location, [like
/// so](crate::reader::Error).
///
/// This struct is intended to be used when an error is expected and rendering the lineinfo (which
/// creates an allocation to remember the source line) is not needed.
///
/// # Examples
///
/// ```
/// use whiteread::reader::Reader;
/// use whiteread::adapters::WithCheapError;
/// use std::io::Cursor;
///
/// // The displayed error doesn't contain the rendered lineinfo.
/// let result = Reader::new(Cursor::new("foo")).parse::<WithCheapError<i32>>();
/// assert!(!result.unwrap_err().to_string().contains("foo"));
///
/// // By default the error line is pretty printed.
/// let result = Reader::new(Cursor::new("foo")).parse::<i32>();
/// assert!(result.unwrap_err().to_string().contains("foo"));
/// ```
#[derive(Default, Debug)]
pub struct WithCheapError<T>(pub T);

impl<T: FromStream> FromStream for WithCheapError<T> {
    fn read<I: StrStream>(it: &mut I) -> Result<WithCheapError<T>> {
        T::read(it).map(WithCheapError)
    }

    const REQUEST_CHEAP_ERROR: bool = true;
}

#[test]
fn partial_lengthed() {
    type V = Lengthed<(u8, u8)>;
    assert_eq!(super::parse_string::<V>("2  10 11  12 13").unwrap().0.len(), 2);
    assert!(super::parse_string::<V>("2  10 11").unwrap_err().is_partial());
    assert!(super::parse_string::<V>("2").unwrap_err().is_partial());
    assert!(super::parse_string::<V>("").unwrap_err().is_nothing());
}

#[test]
fn partial_zeroed() {
    type V = Zeroed<(u8, u8)>;
    assert_eq!(super::parse_string::<V>("10 11  12 13  0 0").unwrap().0.len(), 2);
    assert!(super::parse_string::<V>("10 11  0").unwrap_err().is_partial());
    assert!(super::parse_string::<V>("10 11").unwrap_err().is_partial());
    assert!(super::parse_string::<V>("10").unwrap_err().is_partial());
    assert!(super::parse_string::<V>("").unwrap_err().is_nothing());
}
