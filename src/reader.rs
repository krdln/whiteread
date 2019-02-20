//! This module defines the `Reader` struct.
//!
//! See the [`Reader`](struct.Reader.html) for docs.

use std::error::Error as StdError;
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;

use super::white;
use super::white::Error::*;
use super::White;

use super::stream::SplitAsciiWhitespace;
use super::stream::StrStream;

/// Wrapper for BufRead allowing easy parsing values from a Reader.
///
/// This struct contains line-buffer, which enables
/// scanf-like behavior (newline-agnostic parsing).
/// Newline-aware parsing is also supported.
///
/// `Reader` also provides almost zero-allocation parsing
/// (an allocation is needed to store the line-buffer).
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
/// # use whiteread::{Reader, TooShort};
/// # use whiteread::prelude::*;
/// let data = std::io::Cursor::new(
/// br"1 2
///
/// 3 4 5
/// 6 7
/// 8
/// " as &[u8]);
/// let mut r = Reader::new(data);
/// assert_eq!(r.next_line().unwrap().trim(), "1 2");
/// assert_eq!(r.continue_().ok(), Some(1));
/// assert_eq!(r.continue_().ok(), Some( (2, 3) ));   // continue_line would return `TooShort` here
/// assert_eq!(r.continue_line().ok(), Some(4)); // finish_line would return `Leftovers` here
/// assert_eq!(r.start_line().ok(), Some(6));   // line would return `Leftovers` here
/// assert_eq!(r.line().ok(), Some(8));
/// // from now, everything will return TooShort
/// # match r.parse::<u8>().map_err(|e| e.into_inner()) {
/// #     Err(TooShort) => (),
/// #     _ => panic!()
/// # }
/// #
/// # match r.line::<u8>().map_err(|e| e.into_inner()) {
/// #     Err(TooShort) => (),
/// #     _ => panic!()
/// # }
/// #
/// # match r.next_line().map_err(|e| e.into_inner()) {
/// #     Err(TooShort) => (),
/// #     _ => panic!()
/// # }
/// ```
pub struct Reader<B: io::BufRead> {
    buf: B,
    row: u64,
    line: String,
    col: usize,
}

unsafe fn erase_lifetime<'a, 'b, T: 'a + 'b>(x: &'a mut T) -> &'b mut T { &mut *(x as *mut _) }

/// # Constructors
impl<B: io::BufRead> Reader<B> {
    /// Wraps a BufRead.
    ///
    /// Note that you don't have to pass an owned buffered reader, it could be also `&mut`.
    pub fn new(buf: B) -> Reader<B> {
        Reader {
            buf: buf,
            row: 0,
            line: String::new(),
            col: 0,
        }
    }
}

impl Reader<io::BufReader<fs::File>> {
    /// Opens a file and wraps in Reader
    ///
    /// Shortcut for opening a file, wrapping it in a `BufReader` and then in a `Reader`.
    ///
    /// # Examples
    ///
    /// Read an integer from the beginning of file.
    ///
    /// ```no_run
    /// # use whiteread::Reader;
    /// let mut reader = Reader::open("number.txt").unwrap();
    /// let x: u32 = Reader::open("number.txt").unwrap().parse().unwrap();
    /// ```
    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Reader<io::BufReader<fs::File>>> {
        let file = fs::File::open(path)?;
        Ok(Reader::new(io::BufReader::new(file)))
    }
}

/// # Line-agnostic parsing
///
/// Following methods parse some part of input into a White value.
///
/// ## Errors
///
/// These methods may return
/// [`TooShort`, `ParseError` or `IoError`](../white/enum.Error.html) error variant.
/// If they return other variants too, it is stated explicitely.
impl<B: io::BufRead> Reader<B> {
    /// Parses a White value without specialy treating newlines (just like `scanf` or `cin>>`)
    pub fn continue_<T: White>(&mut self) -> BorrowedResult<T> {
        White::read(self).add_lineinfo(self)
    }

    /// Same as `continue_`.
    ///
    /// Using `continue_` over `parse` is preferred, as it conveys better
    /// which part of input will be parsed.
    pub fn parse<T: White>(&mut self) -> BorrowedResult<T> { White::read(self).add_lineinfo(self) }

    /// Just .continue_().unwrap().
    ///
    /// Use it if you really value your time. ;)
    pub fn p<T: White>(&mut self) -> T { self.parse().unwrap() }

    /// Parses remaining part of reader into White value
    /// in a line-agnostic way.
    ///
    /// It could be used with `T=()`, to just check if we're at the EOF.
    ///
    /// ### Errors
    ///
    /// Additionaly to usual parse errors, this method may also return
    /// [`Leftovers`](../white/enum.Error.html#variant.Leftovers).
    pub fn finish<T: White>(&mut self) -> BorrowedResult<T> {
        // safe -- WA for borrowck bug, should be fixed by NLL
        let value = unsafe { erase_lifetime(self) }.parse()?;
        if let Ok(Some(_)) = StrStream::next(self) {
            Err(Leftovers).add_lineinfo(self)
        } else {
            Ok(value)
        }
    }
}

#[test]
fn test_finish() {
    for input in &["1\n\n", "1", "1\n"] {
        let mut reader = Reader::new(io::BufReader::new(input.as_bytes()));
        let x: i32 = reader.finish().expect(&format!("failed at: {:?}", input));
        assert_eq!(x, 1);
    }
}

/// # Line-aware parsing
///
/// Following methods parse some part of input into a White value.
///
/// ## Errors
///
/// These methods may return
/// [`TooShort`, `ParseError` or `IoError`](../white/enum.Error.html) error variant.
/// If they return other variants too, it is stated explicitely.
impl<B: io::BufRead> Reader<B> {
    fn read_line(&mut self) -> io::Result<Option<()>> {
        self.row += 1;
        self.line.clear();
        self.col = 0;
        let n_bytes = self.buf.read_line(&mut self.line)?;
        if n_bytes == 0 {
            return Ok(None);
        }
        Ok(Some(()))
    }

    fn next_within_line(&mut self) -> Option<&str> {
        let mut splitter = SplitAsciiWhitespace::from_parts(&self.line, self.col);
        let ret = Iterator::next(&mut splitter);
        self.col = splitter.position();
        ret
    }

    /// Reads a new line from input and parses it into White value **as a whole**.
    ///
    /// The function is called just `line` for brevity and also to
    /// make it look different than global `read_line` to avoid mistakes.
    ///
    /// ### Errors
    ///
    /// Additionaly to usual parse errors, this method may also return `Leftovers`.
    pub fn line<T: White>(&mut self) -> BorrowedResult<T> {
        if let None = self.read_line()? {
            return Err(TooShort).add_lineinfo(self);
        };
        self.finish_line()
    }

    /// Reads a new line from input and parses some part of it into White value.
    pub fn start_line<T: White>(&mut self) -> BorrowedResult<T> {
        if let None = self.read_line()? {
            return Err(TooShort).add_lineinfo(self);
        };
        self.continue_line()
    }

    /// Parses some part of current line into White value.
    pub fn continue_line<T: White>(&mut self) -> BorrowedResult<T> {
        let result = {
            let mut splitter = SplitAsciiWhitespace::from_parts(&self.line, self.col);
            let result = White::read(&mut splitter);
            self.col = splitter.position();
            result
        };
        result.add_lineinfo(self)
    }

    /// Parses remaining part of current line into White value.
    ///
    /// It could be used with `T=()`, to just check if we're on the end of line.
    ///
    /// ### Errors
    ///
    /// Additionaly to usual parse errors, this method may also return
    /// [`Leftovers`](../white/enum.Error.html#variant.Leftovers).
    pub fn finish_line<T: White>(&mut self) -> BorrowedResult<T> {
        // safe -- WA for borrowck bug, should be fixed by NLL
        let value = unsafe { erase_lifetime(self) }.continue_line()?;
        if let Some(_) = self.next_within_line() {
            Err(Leftovers).add_lineinfo(self)
        } else {
            Ok(value)
        }
    }
}

/// # Additional methods
impl<B: io::BufRead> Reader<B> {
    /// Reads a new line and returns it.
    ///
    /// This function should be used when `White`-returning functions
    /// are insufficient or just to get a preview of a line.
    /// Note that line's content will not be considered consumed
    /// and will be available for `continue_` and `continue_line`.
    pub fn next_line(&mut self) -> BorrowedResult<&str> {
        if let None = self.read_line()? {
            return Err(TooShort).add_lineinfo(self);
        }
        Ok(&self.line)
    }

    /// Gets underlying buffer back.
    pub fn into_inner(self) -> B { self.buf }
}

impl<B: io::BufRead> StrStream for Reader<B> {
    fn next(&mut self) -> io::Result<Option<&str>> {
        loop {
            // safe -- WA for borrowck bug, should be fixed by NLL
            match unsafe { erase_lifetime(self) }.next_within_line() {
                None => (),
                some => return Ok(some),
            }

            if let None = self.read_line()? {
                return Ok(None);
            };
        }
    }
}

/// An error type containing a lineinfo.
///
/// This error is returned from a [`Reader`](struct.Reader.html) methods,
/// and it contains an information about location of the error (line and column).
///
/// You can display the lineinfo using the `Display` trait,
/// or call the [`pretty_unwrap`](trait.PrettyUnwrap.html#tymethod.pretty_unwrap).
///
/// The displayed error provides a line number and a column marker:
///
/// ```text
/// excessive input provided at
/// 1| 42 aaa
///         ^
/// ```
///
/// Note that when using `unwrap` the `Debug` trait will be used,
/// and the location won't be pretty-printed.
///
/// The *borrowed* in the name refers to the fact that it borrows the
/// reader that returned an error
/// (so it can display error location, while still being cheap to create).
/// The owned variant is called [`OwnedError`](struct.OwnedError.html).
///
/// Because of this borrowing, this error should be either handled
/// immediately or converted to `OwnedError` or `Box<Error>`
/// (the `try!` macro and `?` operator automatically perform such conversion).
///
/// Note: this type doesn't implement `std::error::Error`,
/// so that custom conversion into `Box<Error>` can be provided
/// (which first creates `OwnedError`).
///
/// # Examples
///
/// Explicit handling:
///
/// ```no_run
/// # use whiteread::Reader;
/// let mut reader = Reader::new(std::io::Cursor::new(b"123 aaa"));
/// match reader.continue_::<i32>() {
///     Ok(x) => println!("I've read {}", x),
///     Err(e) => println!("Something went wrong: {}", e),
/// }
/// ```
///
/// Implicit conversion to `Box<Error>` or `OwnedError`:
///
/// ```no_run
/// use std::error::Error;
/// use std::io::BufRead;
/// use whiteread::reader::{Reader, OwnedError};
///
/// fn read_numbers<B: BufRead>(reader: &mut Reader<B>) -> Result<Vec<i32>, Box<Error>> {
///     let numbers = reader.continue_()?;
///     Ok(numbers)
/// }
///
/// fn read_numbers_<B: BufRead>(reader: &mut Reader<B>) -> Result<Vec<i32>, OwnedError> {
///     let numbers = reader.continue_()?;
///     Ok(numbers)
/// }
/// ```
#[derive(Debug)]
pub struct BorrowedError<'line> {
    error: white::Error,
    line: &'line str,
    row: u64,
    col: usize,
}

/// An owned version of the error with lineinfo.
///
/// It can be created from the [`BorrowedError`](struct.BorrowedError.html)
/// using `.to_owned()` method `From::from` or automatically with `try!` or `?`.
///
/// This type, in contrary to `BorrowedError`, can be used as a return value
/// (ie. [`OwnedResult`](type.OwnedResult.html)). Because of that, it's also
/// exported as `ReaderError` in the crate's root.
///
/// See the [`BorrowedError`](struct.BorrowedError.html) for more docs.
#[derive(Debug)]
pub struct OwnedError {
    error: white::Error,
    line: Box<str>,
    row: u64,
    col: usize,
}

impl<'a> BorrowedError<'a> {
    /// Obtains an owned (`'static`) version of the error
    ///
    /// The conversion is also automatically performed by `?`
    pub fn to_owned(self) -> OwnedError {
        OwnedError {
            error: self.error,
            line: self.line.to_owned().into_boxed_str(),
            row: self.row,
            col: self.col,
        }
    }

    /// Obtains an underlying error, by stripping the location info.
    ///
    /// You can also use `.as_ref()` to get a reference to it.
    pub fn into_inner(self) -> white::Error { self.error }

    /// Obtains a location (line, column) of the error.
    ///
    /// ### Return value
    ///
    /// The tuple contains a 1-indexed number of line
    /// and a 1-indexed number of column.
    ///
    /// `None` is returned when the location info is not available,
    /// eg. when IO error happens.
    pub fn location(&self) -> Option<(u64, usize)> {
        if self.row > 0 {
            Some((self.row, self.col))
        } else {
            None
        }
    }
}

#[test]
fn test_location() {
    let mut reader = Reader::new(io::Cursor::new(b"\n\n\n\n a 2"));
    let error = reader.continue_::<u8>().unwrap_err();
    assert_eq!(error.location(), Some((5, 2)));
    let error = error.to_owned();
    assert_eq!(error.location(), Some((5, 2)));
}

impl OwnedError {
    /// Obtains an underlying error, by stripping the location info.
    ///
    /// You can also use `.as_ref()` to get a reference to it.
    pub fn into_inner(self) -> white::Error { self.error }

    /// Obtains a location (line, column) of the error.
    ///
    /// ### Return value
    ///
    /// The tuple contains a 1-indexed number of line
    /// and a 1-indexed number of column.
    ///
    /// `None` is returned when the location info is not available,
    /// eg. when IO error happens.
    pub fn location(&self) -> Option<(u64, usize)> {
        if self.row > 0 {
            Some((self.row, self.col))
        } else {
            None
        }
    }
}

impl StdError for OwnedError {
    fn description(&self) -> &str { self.error.description() }
    fn cause(&self) -> Option<&StdError> { Some(&self.error) }
}

impl<'a> AsRef<white::Error> for BorrowedError<'a> {
    fn as_ref(&self) -> &white::Error { &self.error }
}

impl AsRef<white::Error> for OwnedError {
    fn as_ref(&self) -> &white::Error { &self.error }
}

impl From<io::Error> for OwnedError {
    fn from(e: io::Error) -> OwnedError { BorrowedError::from(e).to_owned() }
}

impl<'a> From<BorrowedError<'a>> for OwnedError {
    fn from(e: BorrowedError<'a>) -> OwnedError { e.to_owned() }
}

impl<'a> From<BorrowedError<'a>> for Box<StdError> {
    fn from(e: BorrowedError<'a>) -> Box<StdError> { Box::from(e.to_owned()) }
}

impl<'a> From<BorrowedError<'a>> for Box<StdError + Send + Sync> {
    fn from(e: BorrowedError<'a>) -> Self { Box::from(e.to_owned()) }
}

impl<'a> From<io::Error> for BorrowedError<'a> {
    fn from(e: io::Error) -> BorrowedError<'a> {
        BorrowedError {
            error: white::IoError(e),
            row: 0,
            col: 0,
            line: "",
        }
    }
}

fn display(
    error: &white::Error,
    line: &str,
    row: u64,
    mut col: usize,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    write!(f, "{}", error)?;
    if row != 0 {
        #[allow(deprecated)] // Rust 1.15 doesn't have trim_end_matches yet
        let line = line.trim_right_matches(&['\n', '\r'][..]);

        if line.len() <= 120 {
            if col > line.len() {
                col = line.len()
            }
            if (error.is_parse_error() || error.is_leftovers()) && col > 0 {
                col -= 1;
            }

            writeln!(f, " at")?;
            let number = row.to_string();
            write!(f, "{}| ", number)?;
            writeln!(f, "{}", line)?;
            for _ in 0..number.len() + 2 {
                write!(f, " ")?;
            }
            for c in line[..col].chars() {
                if c <= b' ' as char {
                    write!(f, "{}", c)?;
                } else {
                    write!(f, " ")?;
                }
            }
            write!(f, "^")?;
        } else {
            write!(f, " at line {}, column {}", row, col + 1)?;
        }
    }
    Ok(())
}

impl<'a> fmt::Display for BorrowedError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        display(&self.error, self.line, self.row, self.col, f)
    }
}

impl fmt::Display for OwnedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        display(&self.error, &self.line, self.row, self.col, f)
    }
}

/// Result with `BorrowedError` as an error variant.
///
/// This type is also exported in the crate's root as `ReaderResult`,
/// because it's returned by many methods from the [`Reader`](struct.Reader.html).
///
/// See the [`BorrowedError`](struct.BorrowedError.html) for more docs.
///
/// The owned equivalent of this type is [`OwnedResult`](type.OwnedResult.html).
/// You can use [`to_owned`](trait.BorrowedResultExt.html#tymethod.to_owned)
/// to convert to it.
pub type BorrowedResult<'line, T> = ::std::result::Result<T, BorrowedError<'line>>;

/// Result with `OwnedError` as an error variant.
///
/// See the [`OwnedError`](struct.OwnedError.html) for more docs.
pub type OwnedResult<T> = ::std::result::Result<T, OwnedError>;

/// Trait providing additional methods on `BorrowedResult`.
///
/// This trait is included in prelude.
pub trait BorrowedResultExt<'a, T> {
    /// Propagates an error, unless it's TooShort (returns None in that case).
    ///
    /// # Examples
    ///
    /// Summing all integers from a file (until the end),
    /// with proper error handling.
    ///
    /// ```no_run
    /// use whiteread::{Reader, ReaderResult};
    /// use whiteread::prelude::*;
    ///
    /// fn sum_file() -> whiteread::ReaderResult<i64> {
    ///     let mut reader = Reader::open("numbers.txt")?;
    ///     let mut s: i64 = 0;
    ///     while let Some(x) = reader.continue_::<i64>().none_on_too_short()? {
    ///         s += x
    ///     }
    ///     Ok(s)
    /// }
    ///
    fn none_on_too_short(self) -> BorrowedResult<'a, Option<T>>;

    /// Converts the error variant from `BorrowedError` to `OwnedError`.
    ///
    /// See the [`BorrowedError`](struct.BorrowedError.html) and
    /// [`OwnedError`](struct.OwnedError.html) for more details.
    ///
    /// The conversion is also performed by the `From::from` implementation
    /// used by `try!` macro and the `?` (question mark) operator,
    /// so you should rarely need this method.
    fn to_owned(self) -> OwnedResult<T>;
}

/// Provides `pretty_unwrap` method that uses the `Display` trait.
pub trait PrettyUnwrap {
    type Target;

    /// Works like `unwrap`, but prints the error message
    /// to the stderr using the `Display` trait before panicking.
    ///
    /// Should be used instead of `unwrap` to nicely display
    /// errors from [`ReaderResult`](type.OwnedResult.html).
    fn pretty_unwrap(self) -> Self::Target;
}

impl<'a, T> BorrowedResultExt<'a, T> for BorrowedResult<'a, T> {
    fn none_on_too_short(self) -> BorrowedResult<'a, Option<T>> {
        match self {
            Ok(x) => Ok(Some(x)),
            Err(BorrowedError {
                error: TooShort, ..
            }) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn to_owned(self) -> OwnedResult<T> { self.map_err(BorrowedError::to_owned) }
}

impl<T, E> PrettyUnwrap for Result<T, E>
where
    E: fmt::Display,
{
    type Target = T;

    fn pretty_unwrap(self) -> T {
        match self {
            Ok(x) => x,
            Err(e) => {
                use self::io::Write;
                writeln!(io::stderr(), "{}", e).ok();
                panic!("PrettyUnwrap::pretty_unwrap failed");
            }
        }
    }
}

fn add_lineinfo<'line, B>(error: white::Error, reader: &'line Reader<B>) -> BorrowedError<'line>
where
    B: io::BufRead,
{
    BorrowedError {
        error: error,
        row: reader.row,
        col: reader.col,
        line: &reader.line,
    }
}

trait AddLineinfoExt<T> {
    fn add_lineinfo<'line, B>(self, reader: &'line Reader<B>) -> BorrowedResult<'line, T>
    where
        B: io::BufRead;
}

impl<T> AddLineinfoExt<T> for white::Result<T> {
    fn add_lineinfo<'a, B>(self, reader: &'a Reader<B>) -> BorrowedResult<'a, T>
    where
        B: io::BufRead,
    {
        self.map_err(|e| add_lineinfo(e, reader))
    }
}
