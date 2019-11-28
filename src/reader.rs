//! This module defines the [`Reader`] struct.
//!
//! See the [`Reader`] for docs.

use std::error::Error as StdError;
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;

use super::stream;
use super::stream::Error::*;
use super::stream::Progress;
use super::FromStream;

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
/// # use whiteread::Reader;
/// # use whiteread::stream::Error::TooShort;
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
/// #     Err(TooShort(_)) => (),
/// #     _ => panic!()
/// # }
/// #
/// # match r.line::<u8>().map_err(|e| e.into_inner()) {
/// #     Err(TooShort(_)) => (),
/// #     _ => panic!()
/// # }
/// #
/// # match r.next_line().map_err(|e| e.into_inner()) {
/// #     Err(TooShort(_)) => (),
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

impl Reader<io::Empty> {
    /// Creates a reader that parses just the given line
    pub(crate) fn single_line(row: u64, line: String) -> Reader<io::Empty> {
        Reader {
            buf: io::empty(),
            row,
            line,
            col: 0,
        }
    }
}

impl Reader<io::BufReader<io::Stdin>> {
    /// Wraps stdin in the reader making some assumptions
    ///
    /// This is a helper that allows constructing a Reader from [`io::stdin`](std::io::stdin) in
    /// one function.  The usual way to do it needs a separate binding for stdin, because of how
    /// [`StdinLock`](std::io::StdinLock) works:
    ///
    /// ```no_run
    /// # use whiteread::reader::Reader;
    /// let stdin = std::io::stdin();
    /// let mut reader = Reader::new(stdin.lock());
    /// ```
    ///
    /// # Examples
    ///
    /// This struct allows you to just call
    ///
    /// ```no_run
    /// # use whiteread::reader::Reader;
    /// let mut reader = Reader::from_stdin_naive();
    /// ```
    ///
    /// This is _almost_ equivalent to previous snippet, but:
    ///
    /// # Drawbacks
    ///
    /// This will construct stdin object with a separate buffer, in addition to the buffer that
    /// stdin already uses. This may cause:
    ///
    /// * unexpected behaviour when mixing `Reader` usage with
    /// * double-buffering, which _may_ affect performance. But on the normal usage, `StdinLock`
    ///   should just pass the read through and not buffer.
    ///
    /// So if you're not trying to get last percent of performance and you operate on stdin solely
    /// using the `Reader`, you're free to use this constructor.
    ///
    /// # See also
    ///
    /// * [`parse_stdin`](super::parse_stdin)
    pub fn from_stdin_naive() -> Reader<io::BufReader<io::Stdin>> {
        Reader::new(io::BufReader::new(io::stdin()))
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
    ///
    /// # See also
    ///
    /// * [`parse_file`](super::parse_file)
    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Reader<io::BufReader<fs::File>>> {
        let file = fs::File::open(path)?;
        Ok(Reader::new(io::BufReader::new(file)))
    }
}

/// # Line-agnostic parsing
///
/// Following methods parse some part of input into a FromStream value.
///
/// ## Errors
///
/// These methods may return
/// [`TooShort`, `ParseError` or `IoError`](crate::stream::Error) error variant.
/// If they return other variants too, it is stated explicitely.
impl<B: io::BufRead> Reader<B> {
    /// Parses a FromStream value without specialy treating newlines (just like `scanf` or `cin>>`)
    pub fn continue_<T: FromStream>(&mut self) -> Result<T> {
        FromStream::read(self).add_lineinfo_this_type(self)
    }

    /// Same as `continue_`.
    ///
    /// Using `continue_` over `parse` is preferred, as it conveys better
    /// which part of input will be parsed.
    pub fn parse<T: FromStream>(&mut self) -> Result<T> {
        FromStream::read(self).add_lineinfo_this_type(self)
    }

    /// Just .continue_().unwrap().
    ///
    /// Use it if you really value your time. ;)
    pub fn p<T: FromStream>(&mut self) -> T { self.parse().unwrap() }

    /// Parses remaining part of reader into FromStream value
    /// in a line-agnostic way.
    ///
    /// It could be used with `T=()`, to just check if we're at the EOF.
    ///
    /// ### Errors
    ///
    /// Additionaly to usual parse errors, this method may also return
    /// [`Leftovers`](crate::stream::Error::Leftovers).
    pub fn finish<T: FromStream>(&mut self) -> Result<T> {
        let value = self.parse()?;
        if let Ok(Some(_)) = StrStream::next(self) {
            Err(stream::Error::Leftovers).add_lineinfo_this_type(self)
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
/// Following methods parse some part of input into a FromStream value.
///
/// ## Errors
///
/// These methods may return
/// [`TooShort`, `ParseError` or `IoError`](crate::stream::Error) error variant.
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

    /// Reads a new line from input and parses it into FromStream value **as a whole**.
    ///
    /// The function is called just `line` for brevity and also to
    /// make it look different than global `read_line` to avoid mistakes.
    ///
    /// ### Errors
    ///
    /// Additionaly to usual parse errors, this method may also return `Leftovers`.
    pub fn line<T: FromStream>(&mut self) -> Result<T> {
        if let None = self.read_line()? {
            return Err(TooShort(Progress::Nothing)).add_lineinfo::<_, T>(self);
        };
        self.finish_line()
    }

    /// Reads a new line from input and parses some part of it into FromStream value.
    pub fn start_line<T: FromStream>(&mut self) -> Result<T> {
        if let None = self.read_line()? {
            return Err(TooShort(Progress::Nothing)).add_lineinfo::<_, T>(self);
        };
        self.continue_line()
    }

    /// Parses some part of current line into FromStream value.
    pub fn continue_line<T: FromStream>(&mut self) -> Result<T> {
        let result = {
            let mut splitter = SplitAsciiWhitespace::from_parts(&self.line, self.col);
            let result = FromStream::read(&mut splitter);
            self.col = splitter.position();
            result
        };
        result.add_lineinfo_this_type(self)
    }

    /// Parses remaining part of current line into FromStream value.
    ///
    /// It could be used with `T=()`, to just check if we're on the end of line.
    ///
    /// ### Errors
    ///
    /// Additionaly to usual parse errors, this method may also return
    /// [`Leftovers`](crate::stream::Error::Leftovers).
    pub fn finish_line<T: FromStream>(&mut self) -> Result<T> {
        // safe -- WA for borrowck bug, should be fixed by NLL + Polonius
        let value = unsafe { erase_lifetime(self) }.continue_line()?;
        if let Some(_) = self.next_within_line() {
            Err(Leftovers).add_lineinfo_this_type(self)
        } else {
            Ok(value)
        }
    }
}

/// # Additional methods
impl<B: io::BufRead> Reader<B> {
    /// Reads a new line and returns it.
    ///
    /// This function should be used when `FromStream`-returning functions
    /// are insufficient or just to get a preview of a line.
    /// Note that line's content will not be considered consumed
    /// and will be available for `continue_` and `continue_line`.
    pub fn next_line(&mut self) -> Result<&str> {
        if let None = self.read_line()? {
            return Err(TooShort(Progress::Nothing)).add_lineinfo::<_, ()>(self);
        }
        Ok(&self.line)
    }

    /// Gets underlying buffer back.
    pub fn into_inner(self) -> B { self.buf }
}

impl<B: io::BufRead> StrStream for Reader<B> {
    fn next(&mut self) -> io::Result<Option<&str>> {
        loop {
            // safe -- WA for borrowck bug, should be fixed by NLL + Polonius
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
/// This error is returned from a [`Reader`]'s methods,
/// and it contains information about location of the error (line and column).
///
/// The error message provides a line number and a column marker rendered underneath
/// the actual line:
///
/// ```text
/// excessive input provided at
/// 1 | 42 aaa
///          ^
/// ```
///
/// The lineinfo will be displayed when using `Display` (like in `println!("{}", e)`)
/// or `Debug` formatting (like in `unwrap`), although `Display` is preferred.
///
/// The pretty-printed lineinfo won't be available if [`FromStr.REQUEST_CHEAP_ERROR`] is set on
/// the returned type.
pub struct Error {
    error: stream::Error,
    /// 1-indexed row or 0 in case of an IO error
    // TODO: Use Option<NonZero> when dropping support for Rust 1.15
    row: u64,
    /// 1-indexed column
    col: usize,
    /// Rendered error message
    rendered: Option<Box<str>>,
}

impl Error {
    /// Obtains an underlying error, by stripping the location info.
    ///
    /// You can also use `.as_ref()` to get a reference to it.
    pub fn into_inner(self) -> stream::Error { self.error }

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
}

impl StdError for Error {
    fn description(&self) -> &str { self.error.description() }
    fn cause(&self) -> Option<&StdError> { Some(&self.error) }
}

impl AsRef<stream::Error> for Error {
    fn as_ref(&self) -> &stream::Error { &self.error }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error {
            error: stream::Error::IoError(e),
            row: 0,
            col: 0,
            rendered: None,
        }
    }
}

fn render_error_to_formatter<F: fmt::Write>(
    error: &stream::Error,
    line: &str,
    row: u64,
    mut col: usize,
    f: &mut F,
) -> fmt::Result {
    write!(f, "{}", error)?;

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
        write!(f, "{} | ", number)?;
        writeln!(f, "{}", line)?;
        for _ in 0..number.len() + 3 {
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

    writeln!(f, "")?;

    Ok(())
}

fn render_error(error: &stream::Error, line: &str, row: u64, col: usize) -> Box<str> {
    let mut output = String::new();
    render_error_to_formatter(error, line, row, col, &mut output).unwrap();
    output.into_boxed_str()
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.rendered {
            Some(ref rendered) => f.write_str(rendered),
            None => fmt::Debug::fmt(self, f),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let _ = f
            .debug_struct("Error")
            .field("error", &self.error)
            .field("row", &self.row)
            .field("col", &self.col);

        if let Some(ref rendered) = self.rendered {
            writeln!(f, ", rendered:")?;
            for _ in 0..79 {
                write!(f, "~")?;
            }
            writeln!(f, "")?;
            f.write_str(&rendered[..])?;
            for _ in 0..79 {
                write!(f, "~")?;
            }
            writeln!(f, "")?;
        }

        write!(f, "}}")?;

        Ok(())
    }
}

/// Result with `Error` as an error variant.
///
/// See the [`Error`] for more docs.
pub type Result<T> = ::std::result::Result<T, Error>;

fn add_lineinfo<B, T: FromStream>(error: stream::Error, reader: &Reader<B>) -> Error
where
    B: io::BufRead,
{
    let rendered = if reader.row != 0 && T::REQUEST_CHEAP_ERROR == false {
        Some(render_error(&error, &reader.line, reader.row, reader.col))
    } else {
        None
    };

    Error {
        rendered: rendered,
        error: error,
        row: reader.row,
        col: reader.col,
    }
}

trait AddLineinfoExt<R> {
    /// Adds lineinfo and conditionally renders an error based on T::REQUEST_CHEAP_ERROR
    ///
    /// Note that T may be different from R
    fn add_lineinfo<B, T: FromStream>(self, reader: &Reader<B>) -> Result<R>
    where
        B: io::BufRead;

    /// Adds lineinfo and conditionally renders an error based on R::REQUEST_CHEAP_ERROR
    fn add_lineinfo_this_type<B>(self, reader: &Reader<B>) -> Result<R>
    where
        B: io::BufRead,
        R: FromStream,
        Self: Sized,
    {
        self.add_lineinfo::<B, R>(reader)
    }
}

impl<R> AddLineinfoExt<R> for stream::Result<R> {
    fn add_lineinfo<B, T: FromStream>(self, reader: &Reader<B>) -> Result<R>
    where
        B: io::BufRead,
    {
        self.map_err(|e| add_lineinfo::<B, T>(e, reader))
    }
}

#[test]
fn error_message() {
    let mut r = Reader::new("\n1 2 3 four 5".as_bytes());
    let error = r.finish::<Vec<i8>>().unwrap_err();
    let expected = "parse error occured at
2 | 1 2 3 four 5
             ^\n";
    assert_eq!(error.to_string(), expected);
    assert!(format!("{:?}", error).contains(expected));
}

#[test]
fn error_message_leftovers() {
    let mut r = Reader::new("aa bb".as_bytes());
    let error = r.line::<String>().unwrap_err();
    let expected = "excessive input provided at
1 | aa bb
        ^\n";
    assert_eq!(error.to_string(), expected);
    assert!(format!("{:?}", error).contains(expected));
}

#[test]
fn error_message_too_short() {
    let mut r = Reader::new("".as_bytes());
    let error = r.finish::<(String, String)>().unwrap_err();
    let expected = "not enough input to start parsing a value at
1 | 
    ^\n";
    assert_eq!(error.to_string(), expected);
    assert!(format!("{:?}", error).contains(expected));
}
