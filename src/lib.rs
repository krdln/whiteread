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
//! use [`ok_or_none`](trait.WhiteResultExt.html#tymethod.ok_or_none)

use std::path::Path;
use std::fs::File;
use std::io::{self, BufRead};

pub mod stream;
pub use self::stream::*;

pub mod white;
pub use self::white::*;

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
    let mut stream = SplitAsciiWhitespace::new(s);
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
    pub fn into_inner(self) -> B {
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
