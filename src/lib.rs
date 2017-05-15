//! Crate for reading whitespace-separated values.
//!
//! The crate defines a trait [`White`](trait.White.html), which
//! describes types that can be parsed from whitespace-separated words,
//! which includes eg. integers, tuples and vectors.
//!
//! The definition of whitespace used in this crate is described in
//! [`SplitAsciiWhitespace`](struct.SplitAsciiWhitespace.html).
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
//! use [`ok_or_none`](trait.WhiteResultExt.html#tymethod.ok_or_none)

use std::path::Path;
use std::fs::File;
use std::io::{self, BufRead};
use std::str::SplitWhitespace;
use std::result;

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

pub trait StrExt {
    fn split_ascii_whitespace(&self) -> SplitAsciiWhitespace;
}

impl StrExt for str {
    fn split_ascii_whitespace(&self) -> SplitAsciiWhitespace {
        SplitAsciiWhitespace { s: self }
    }
}

// White trait -------------------------------------------------------------------------------------

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

// ~ impl From<Error> for io::Error {
// TODO
// ~ }

/// Trait providing additional methods on `Result`.
pub trait WhiteResultExt<T> {
    /// Propagates an error, unless it's TooShort (returns None in that case).
    ///
    /// If that description is confusing, check out [src].
    ///
    /// # Examples
    ///
    /// Summing integers from a file with proper error handling.
    ///
    /// ```no_run
    /// # use whiteread::Reader;
    /// use whiteread::WhiteResultExt;
    /// # use std::fs::File;
    /// # use std::io::BufReader;
    /// # fn test() -> whiteread::Result<i64> {
    /// let f = try!( File::open("test.txt") );
    /// let mut i = Reader::new(BufReader::new(f));
    /// let mut s: i64 = 0;
    /// while let Some(x) = try!( i.continue_::<i64>().ok_or_none() ) { s += x }
    /// Ok(s)
    /// # }
    ///
    fn ok_or_none(self) -> Result<Option<T>>;
}

impl<T> WhiteResultExt<T> for Result<T> {
    fn ok_or_none(self) -> Result<Option<T>> {
        match self {
            Ok(x) => Ok(Some(x)),
            Err(TooShort) => Ok(None),
            Err(e) => Err(e),
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
        while let Some(x) = White::read(it).ok_or_none()? {
            v.push(x);
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
        while let Some(x) = White::read(it).ok_or_none()? {
            v.push(x);
            if v.len() == sz {
                return Ok(Lengthed(v));
            }
        }
        Err(TooShort)
    }
}

/// Wrapper for reading vector of numbers represented by a list ending with 0.
///
/// # Examples
/// ```
/// # use whiteread::{parse_string, Zeroed, Error};
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
pub fn parse_line<T: White>() -> Result<T> {
    let mut line = String::new();
    let n_bytes = ::std::io::stdin().read_line(&mut line)?;
    if n_bytes == 0 {
        return Err(TooShort);
    }
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
pub fn parse_string<T: White>(s: &str) -> Result<T> {
    let mut stream = SplitAsciiWhitespace { s: s };
    let value = White::read(&mut stream)?;

    if let Ok(Some(_)) = StrStream::next(&mut stream) {
        Err(Leftovers)
    } else {
        Ok(value)
    }
}

// Reader -------------------------------------------------------------------------------------

/// Wrapper for BufRead allowing easy parsing values from a Reader.
///
/// This struct contains line-buffer, which enables
/// scanf-like behavior (newline-agnostic parsing)
/// and also provides almost zero-allocation parsing.
///
/// # Examples
///
/// This code
///
/// ```no_run
/// # use whiteread::Reader;
/// let i = std::io::stdin();
/// let mut i = Reader::new(i.lock());
/// let (n, k): (i32, f64) = i.p();
/// ```
///
/// will accept both of following inputs:
///
/// ```text
/// 1
///
/// 2
/// ```
///
/// ```text
/// 1 2
/// ```
///
///
/// Overview of how various methods handle newlines:
///
/// ```
/// # use whiteread::{Reader,TooShort};
/// let data = std::io::Cursor::new(b"1 2\n\n3 4 5\n6 7\n8\n" as &[u8]);
/// let mut r = Reader::new(data);
/// assert_eq!(r.next_line().unwrap().trim(), "1 2");
/// assert_eq!(r.continue_().ok(), Some(1));
/// assert_eq!(r.continue_().ok(), Some( (2, 3) ));   // continue_line would return `TooShort` here
/// assert_eq!(r.continue_line().ok(), Some(4)); // finish_line would return `Leftovers` here
/// assert_eq!(r.start_line().ok(), Some(6));   // line would return `Leftovers` here
/// assert_eq!(r.line().ok(), Some(8));
/// // from now, everything will return Err(TooShort)
/// # match r.parse::<u8>() {
/// #     Err(TooShort) => (),
/// #     _ => panic!()
/// # }
/// #
/// # match r.line::<u8>() {
/// #     Err(TooShort) => (),
/// #     _ => panic!()
/// # }
/// #
/// # match r.next_line() {
/// #     Err(TooShort) => (),
/// #     _ => panic!()
/// # }
/// ```
pub struct Reader<B: BufRead> {
    buf: B,
    line: String,

    // We use 'static lifetime here, but it actually points into line's buffer.
    // We manualy check that after each mutation of line,
    // words are immediately updated.
    words: SplitAsciiWhitespace<'static>,
}

unsafe fn statify_mut<T>(x: &mut T) -> &'static mut T {
    &mut *(x as *mut _)
}

unsafe fn statify<T>(x: &T) -> &'static T {
    &*(x as *const _)
}

/// # Constructors
///
/// Note: There's also [`open`](fn.open.html) constructor, which is a freestanding function.
impl<B: BufRead> Reader<B> {
    /// Wraps a BufRead.
    ///
    /// Note that you don't have to pass an owned buffered reader, it could be also `&mut`.
    pub fn new(buf: B) -> Reader<B> {
        Reader {
            buf: buf,
            line: String::new(),
            words: "".split_ascii_whitespace(),
        }
    }
}

/// Opens a file, and wraps in Reader
///
/// Shortcut for creating a file, wrapping it in a BufReader and then in a Reader.
///
/// Note: this should be a static method on Reader, but currently it's
/// impossible to implement it that way (it requires equality constraints in where clauses).
///
/// # Examples
///
/// Read an integer from a file.
///
/// ```no_run
/// # use whiteread::open;
/// let x: u32 = open("number.txt").unwrap().parse().unwrap();
/// ```
pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Reader<io::BufReader<File>>> {
    let file = File::open(path)?;
    Ok(Reader::new(io::BufReader::new(file)))
}

/// # Line-agnostic parsing
///
/// Following methods parse some part of input into a White value.
///
/// ## Errors
///
/// These methods may return `TooShort`, `ParseError` or `IoError` error variant.
/// If they return other variants too, it is stated explicitely.
impl<B: BufRead> Reader<B> {
    /// Parses a White value without specialy treating newlines (just like `scanf` or `cin>>`)
    pub fn continue_<T: White>(&mut self) -> Result<T> {
        White::read(self)
    }

    /// Same as `continue_`.
    ///
    /// Using `continue_` over `parse` is preferred, as it conveys better
    /// which part of input will be parsed.
    pub fn parse<T: White>(&mut self) -> Result<T> {
        White::read(self)
    }

    /// Just .continue_().unwrap().
    ///
    /// Use it if you really value your time. ;)
    pub fn p<T: White>(&mut self) -> T {
        self.parse().unwrap()
    }

    /// Parses remaining part of reader into White value
    /// in a line-agnostic way.
    ///
    /// It could be used with `T=()`, to just check if we're at the EOF.
    ///
    /// ### Errors
    ///
    /// Additionaly to usual parse errors, this method may also return `Leftovers`.
    pub fn finish<T: White>(&mut self) -> Result<T> {
        let value = self.parse()?;
        if let Ok(Some(_)) = StrStream::next(&mut self.words) {
            Err(Leftovers)
        } else {
            Ok(value)
        }
    }
}
/// # Line-aware parsing
///
/// Following methods parse some part of input into a White value.
///
/// ## Errors
///
/// These methods may return `TooShort`, `ParseError` or `IoError` error variant.
/// If they return other variants too, it is stated explicitely.
impl<B: BufRead> Reader<B> {
    fn read_line(&mut self) -> io::Result<Option<()>> {
        self.words = "".split_ascii_whitespace(); // keep it safe in case of early returns
        self.line.clear();
        let n_bytes = self.buf.read_line(&mut self.line)?;
        self.words = unsafe { statify(&self.line).split_ascii_whitespace() };
        if n_bytes == 0 {
            return Ok(None);
        }
        Ok(Some(()))
    }

    /// Reads a new line from input and parses it into White value **as a whole**.
    ///
    /// The function is called just `line` for brevity and also to
    /// make it look different than global `read_line` to avoid mistakes.
    ///
    /// ### Errors
    ///
    /// Additionaly to usual parse errors, this method may also return `Leftovers`.
    pub fn line<T: White>(&mut self) -> Result<T> {
        if let None = self.read_line()? {
            return Err(TooShort);
        };
        self.finish_line()
    }

    /// Reads a new line from input and parses some part of it into White value.
    pub fn start_line<T: White>(&mut self) -> Result<T> {
        if let None = self.read_line()? {
            return Err(TooShort);
        };
        White::read(&mut self.words)
    }

    /// Parses some part of current line into White value.
    pub fn continue_line<T: White>(&mut self) -> Result<T> {
        White::read(&mut self.words)
    }

    /// Parses remaining part of current line into White value.
    ///
    /// It could be used with `T=()`, to just check if we're on the end of line.
    ///
    /// ### Errors
    ///
    /// Additionaly to usual parse errors, this method may also return `Leftovers`.
    pub fn finish_line<T: White>(&mut self) -> Result<T> {
        let value = White::read(&mut self.words)?;
        if let Ok(Some(_)) = StrStream::next(&mut self.words) {
            Err(Leftovers)
        } else {
            Ok(value)
        }
    }

}

/// # Additional methods
impl<B: BufRead> Reader<B> {
    /// Reads a new line and returns it.
    ///
    /// This function should be used when `White`-returning functions
    /// are insufficient or just to get a preview of a line.
    /// Note that line's content will not be considered consumed
    /// and will be available for `continue_` and `continue_line`.
    pub fn next_line(&mut self) -> Result<&str> {
        if let None = self.read_line()? {
            return Err(TooShort);
        }
        Ok(&self.line)
    }

    /// Gets underlying buffer back.
    pub fn unwrap(self) -> B {
        self.buf
    }
}

impl<B: BufRead> StrStream for Reader<B> {
    fn next(&mut self) -> io::Result<Option<&str>> {
        loop {
            // WA using statify, because of https://github.com/rust-lang/rfcs/issues/811

            match StrStream::next(unsafe { statify_mut(&mut self.words) })? {
                None => (),
                some => return Ok(some),
            }
            if let None = self.read_line()? {
                return Ok(None);
            };
        }
    }
}
