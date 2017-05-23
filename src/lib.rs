//! Crate for reading whitespace-separated values.
//!
//! The crate defines a trait [`White`](trait.White.html), which
//! describes types that can be parsed from whitespace-separated words,
//! which includes eg. integers, tuples and vectors.
//!
//! The definition of whitespace used in this crate is described in
//! [`SplitAsciiWhitespace`](stream/struct.SplitAsciiWhitespace.html).
//!
//! # Examples
//!
//! Basics
//!
//! ```
//! # use whiteread::parse_string;
//! let (s, i): (String, i32) = parse_string("  answer  42 ").unwrap();
//! # assert!(s == "answer" && i == 42);
//! ```
//!
//! Easy reading from stdin.
//!
//! ```no_run
//! # use whiteread::parse_line;
//! let x: i32 = parse_line().unwrap();
//! ```
//!
//! Efficient reading from stdin (newline-agnostic) with [`Reader`](struct.Reader.html).
//! Stops on error.
//!
//! ```no_run
//! # use whiteread::Reader;
//! let i = std::io::stdin();
//! let mut i = Reader::new(i.lock());
//! while let Ok(f) = i.parse::<f64>() {
//!     println!("{}", f);
//! }
//! ```
//!
//! If you want better error handling in while-let loops,
//! use [`ok_or_none`](trait.WhiteResultExt.html#tymethod.none_on_too_short)

use std::path::Path;
use std::io;

pub mod stream;

pub mod white;
pub use self::white::{White, Skip, SkipAll, Lengthed, Zeroed};
pub use self::white::{TooShort, ParseError, Leftovers};

pub mod reader;
pub use self::reader::Reader;
pub use self::reader::OwnedError as ReaderError;
pub use self::reader::OwnedResult as ReaderResult;

/// Reexports of traits containing the extension methods.
pub mod prelude {
    pub use super::reader::BorrowedResultExt;
    pub use super::reader::PrettyUnwrap;
}

// Helpers -----------------------------------------------------------------------------------------

/// Helper function for parsing `White` value from one line of stdin.
///
/// Leftovers are considered an error.
/// This function locks a mutex and allocates a buffer, so
/// don't use it when reading more than few lines –
/// use [`Reader`](struct.Reader.html) instead.
///
/// # Examples
/// ```no_run
/// # use whiteread::parse_line;
/// let x: i32 = parse_line().unwrap();
/// ```
pub fn parse_line<T: White>() -> white::Result<T> {
    let mut line = String::new();
    io::stdin().read_line(&mut line)?;
    parse_string(&line)
}

/// Helper function for parsing `White` value from string. Leftovers are considered an error.
///
/// # Examples
/// ```
/// # use whiteread::parse_string;
/// let number: i32 = parse_string(" 123  ").unwrap();
/// assert!(number == 123);
/// ```
pub fn parse_string<T: White>(s: &str) -> white::Result<T> {
    let mut stream = stream::SplitAsciiWhitespace::new(s);
    let value = White::read(&mut stream)?;

    if let Ok(Some(_)) = stream::StrStream::next(&mut stream) {
        Err(Leftovers)
    } else {
        Ok(value)
    }
}

/// Parses a whole file as a `White` value
///
/// If you want to parse the file in multiple steps,
/// use [`Reader::open`](struct.Reader.html#method.open).
///
/// # Examples
///
/// Parse the whole file as an tuple.
///
/// ```no_run
/// # use whiteread::parse_file;
/// let x: (i32, i32) = parse_file("coords.txt").unwrap();
/// ```
pub fn parse_file<T: White, P: AsRef<Path>>(path: P) -> ReaderResult<T> {
    Ok( Reader::open(path)?.finish()? )
}

