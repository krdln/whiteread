//! This module defines the `Reader` struct.

use std::io;
use std::fmt;
use std::path::Path;
use std::fs;

use super::white;
use super::white::Error::*;
use super::White;

use super::stream::StrStream;
use super::stream::SplitAsciiWhitespace;

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
/// # use whiteread::{Reader, TooShort};
/// # use whiteread::prelude::*;
/// let data = std::io::Cursor::new(b"1 2\n\n3 4 5\n6 7\n8\n" as &[u8]);
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

unsafe fn erase_lifetime<'a, 'b, T: 'a + 'b>(x: &'a mut T) -> &'b mut T {
    &mut *(x as *mut _)
}

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
    /// Shortcut for opening a file, wrapping it in a BufReader and then in a Reader.
    ///
    /// # Examples
    ///
    /// Read an integer from the beginning of file.
    ///
    /// ```no_run
    /// # use whiteread::Reader;
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
/// These methods may return `TooShort`, `ParseError` or `IoError` error variant.
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
    pub fn parse<T: White>(&mut self) -> BorrowedResult<T> {
        White::read(self).add_lineinfo(self)
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
    pub fn finish<T: White>(&mut self) -> BorrowedResult<T> {
        // safe -- WA for borrowck bug, should be fixed by NLL
        let value = unsafe { erase_lifetime(self) }.parse()?;
        if let Ok(()) = White::read(self) {
            Err(Leftovers).add_lineinfo(self)
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
    /// Additionaly to usual parse errors, this method may also return `Leftovers`.
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
    pub fn into_inner(self) -> B {
        self.buf
    }
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

#[derive(Debug)]
pub struct BorrowedError<'line> {
    pub error: white::Error,
    pub line: &'line str,
    pub row: u64,
    pub col: usize,
}

#[derive(Debug)]
pub struct OwnedError {
    error: white::Error,
    line: Box<str>,
    row: u64,
    col: usize,
}

impl<'a> BorrowedError<'a> {
    /// Obtains an owned ('static) version of the error
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

    pub fn into_inner(self) -> white::Error { self.error }
}

impl OwnedError {
    pub fn into_inner(self) -> white::Error { self.error }
}

impl<'a> AsRef<white::Error> for BorrowedError<'a> {
    fn as_ref(&self) -> &white::Error { &self.error }
}

impl AsRef<white::Error> for OwnedError {
    fn as_ref(&self) -> &white::Error { &self.error }
}

impl From<io::Error> for OwnedError {
    fn from(e: io::Error) -> OwnedError {
        BorrowedError::from(e).to_owned()
    }
}

impl<'a> From<BorrowedError<'a>> for OwnedError {
    fn from(e: BorrowedError<'a>) -> OwnedError {
        e.to_owned()
    }
}

impl<'a> From<io::Error> for BorrowedError<'a> {
    fn from(e: io::Error) -> BorrowedError<'a> {
        BorrowedError { error: white::IoError(e), row: 0, col: 0, line: "" }
    }
}

fn display(
    error: &white::Error,
    line: &str,
    row: u64,
    mut col: usize,
    f: &mut fmt::Formatter
) -> fmt::Result {
    write!(f, "{}", error)?;
    if row != 0 {
        let line = line.trim_right_matches(&['\n', '\r'][..]);
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
        for _ in 0 .. number.len() + 2 {
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

pub type BorrowedResult<'line, T> = ::std::result::Result<T, BorrowedError<'line>>;

pub type OwnedResult<T> = ::std::result::Result<T, OwnedError>;

/// Trait providing additional methods on `BorrowedResult`.
/// 
/// This trait is included in prelude.
pub trait BorrowedResultExt<'a, T> {
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
    /// # use whiteread::reader::BorrowedResultExt;
    /// # use std::fs::File;
    /// # use std::io::BufReader;
    /// # fn test() -> whiteread::ReaderResult<i64> {
    /// let f = try!( File::open("test.txt") );
    /// let mut i = Reader::new(BufReader::new(f));
    /// let mut s: i64 = 0;
    /// while let Some(x) = i.continue_::<i64>().none_on_too_short()? { s += x }
    /// Ok(s)
    /// # }
    ///
    fn none_on_too_short(self) -> BorrowedResult<'a, Option<T>>;

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
            Err(BorrowedError { error: TooShort, .. } ) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn to_owned(self) -> OwnedResult<T> {
        self.map_err(BorrowedError::to_owned)
    }
}

impl<T, E> PrettyUnwrap for Result<T, E>
where E: fmt::Display {
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
where B: io::BufRead {
    BorrowedError {
        error: error,
        row: reader.row,
        col: reader.col,
        line: &reader.line,
    }
}

trait AddLineinfoExt<T> {
    fn add_lineinfo<'line, B>(self, reader: &'line Reader<B>) -> BorrowedResult<'line, T>
    where B: io::BufRead;
}

impl<T> AddLineinfoExt<T> for white::Result<T> {
    fn add_lineinfo<'a, B>(self, reader: &'a Reader<B>) -> BorrowedResult<'a, T>
    where B: io::BufRead {
        self.map_err(|e| add_lineinfo(e, reader))
    }
}

