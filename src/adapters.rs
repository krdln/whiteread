//! This module defines adapters for `White` trait.
//!
//! This module contains a few structs, which implement
//! [`White`] in a special way. Eg. `Skip` serves the role
//! of a placeholder, and `Lengthed` allows to read a vector
//! prepended by its length.
//!
//! [`White`]: ../stream/trait.White.html

use super::stream::{StrStream, White, Result};

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

impl White for SkipAll {
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

impl<T: White> White for Lengthed<T> {
    fn read<I: StrStream>(it: &mut I) -> Result<Lengthed<T>> {
        let sz = White::read(it)?;
        let mut v = Vec::with_capacity(sz);
        loop {
            if v.len() == sz {
                return Ok(Lengthed(v));
            }
            v.push(White::read(it)?);
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
