// Remove when bumping minimum Rust version to 1.27
#![allow(bare_trait_objects)]

//! Crate for reading whitespace-separated values.
//!
//! The crate defines a trait [`FromStream`](stream::FromStream), which
//! describes types that can be parsed from whitespace-separated words,
//! which includes eg. integers, tuples, vectors and various [adapters].
//!
//! The definition of whitespace used in this crate is described in
//! [`SplitAsciiWhitespace`](stream::SplitAsciiWhitespace).
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
//! Efficient reading from stdin (newline-agnostic) with [`Reader`](reader::Reader).
//!
//! ```no_run
//! # use whiteread::Reader;
//! # foo().unwrap();
//! # fn foo() -> whiteread::reader::Result<()> {
//! let mut i = Reader::from_stdin_naive();
//! while let Some(f) = i.parse::<Option<f64>>()? {
//!     println!("{}", f);
//! }
//! # Ok(())
//! # }
//! ```

use std::io;
use std::path::Path;

pub mod stream;
pub use self::stream::FromStream;

pub mod adapters;

pub mod reader;
pub use self::reader::Reader;

// Helpers -----------------------------------------------------------------------------------------

/// Helper function for parsing [`FromStream`] value from one line of stdin.
///
/// Leftovers are considered an error.
/// This function locks a mutex and allocates a buffer, so
/// don't use it when reading more than few lines –
/// use [`Reader`](reader::Reader) instead.
///
/// # Examples
/// ```no_run
/// # use whiteread::parse_line;
/// let x: i32 = parse_line().unwrap();
/// ```
pub fn parse_line<T: FromStream>() -> reader::Result<T> {
    use std::sync::atomic;
    #[allow(deprecated)] // suggested AtomicUsize::new() doesn't work on 1.20
    static LINE_NUMBER: atomic::AtomicUsize = atomic::ATOMIC_USIZE_INIT;
    let row = 1 + LINE_NUMBER.fetch_add(1, atomic::Ordering::Relaxed);

    let mut line = String::new();
    io::stdin().read_line(&mut line)?;
    Reader::single_line(row as u64, line).finish_line()
}

/// Helper function for parsing [`FromStream`] value from string. Leftovers are considered an error.
///
/// # Examples
/// ```
/// # use whiteread::parse_string;
/// let number: i32 = parse_string(" 123  ").unwrap();
/// assert!(number == 123);
/// ```
pub fn parse_string<T: FromStream>(s: &str) -> stream::Result<T> {
    let mut stream = stream::SplitAsciiWhitespace::new(s);
    let value = FromStream::read(&mut stream)?;

    if let Ok(Some(_)) = stream::StrStream::next(&mut stream) {
        Err(stream::Error::Leftovers)
    } else {
        Ok(value)
    }
}

/// Parse the whole stdin as a [`FromStream`] value
///
/// Use [`Reader`](reader::Reader) if you want more complex logic.
///
/// # Examples
/// ```
/// # use whiteread::parse_stdin;
/// /// Read whitespace-separated numbers from stdin, newline agnostic.
/// let numbers: Vec<i32> = parse_stdin().unwrap();
/// ```
pub fn parse_stdin<T: FromStream>() -> reader::Result<T> {
    let stdin = io::stdin();
    // Explicit return is necessary here to shorten the lifetime of `stdin.lock()`
    return Reader::new(stdin.lock()).finish();
}

/// Parses a whole file as a [`FromStream`] value
///
/// Calling this function is equivalent to:
///
/// ```no_run
/// # use whiteread::{Reader, reader, FromStream};
/// # fn foo<T: FromStream>() -> reader::Result<T> {
/// # let path = "foo";
/// # Ok(
/// Reader::open(path)?.finish()?
/// # )
/// # }
/// ```
///
/// If you want to parse the file in multiple steps,
/// use [`Reader::open`](crate::reader::Reader::open).
///
/// # Examples
///
/// Parse the whole file as an tuple.
///
/// ```no_run
/// # use whiteread::parse_file;
/// let x: (i32, i32) = parse_file("coords.txt").unwrap();
/// ```
pub fn parse_file<T: FromStream, P: AsRef<Path>>(path: P) -> reader::Result<T> {
    Ok(Reader::open(path)?.finish()?)
}
