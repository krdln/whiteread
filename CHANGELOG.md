# Changelog

## 0.5.0 – 2019-06-15

* Removed most of reexport from crate root.
* Renamed `White` trait to `FromStream` and reorganized modules a little bit.
* Removed `reader::BorrowedError`. The intended usage of this struct was avoid
  allocations on a hot path (in a case errors are expected). You can now
  disable rendering errors using `WithCheapError` adapter, which should cause
  the `reader::Error` not to allocate.
* Removed `pretty_unwrap` and make the `Debug` display rendered errors by default.
* Split the `Error::TooShort` to differentiate between zero input and partial input.
* Implemented `FromStream` for `Option` that returns `None` on empty input.
* Added `Reader::from_stdin_naive`. This helper allows to avoid explitely calling
  and locking `io::stdin`, but has some small disadvantages (hence “naive”).
* Added rendered errors to `parse_line`.
* Added `parse_stdin` helper for parsing whole stdin.
* Bumped minimal Rust version to 1.18

## 0.4.4 – 2017-11-19

* Added a type annotation in a test (needed due to rust/pull/44287)

## 0.4.3 – 2017-05-24

* Added `Skip` and `SkipAll` to handle ignored values.
* Added `Zeroed` wrapper for parsing 0-terminated lists.
* More consistent API for `WhiteReader`:
    * Added `continue_` as a synonym to `parse` (to match `continue_line`)
    * Added `finish` (as a `finish_line` counterpart)
    * Renamed `unwrap` to `into_inner`
    * Moved `open` from standalone function to static method.
* Added `parse_file` helper.
* Ensured that the crate can be pasted into a module
  and added a binary – now `cargo run` generates a template
  with `mod whiteread`.
* Split crate into multiple modules.
* Added separate Error types for Reader, which can `Display`
  the error location in a nice way.
* Fix bug in reading empty vector using `Lengthed`.
* More impls for tuples (up to 6)

## 0.3.0 – 2016-06-10

* Added `SplitAsciiWhitespace`, a faster version of `SplitWhitespace`.
* Added `open` for opening files as a `WhiteReader`.

## 0.2.0 – 2015-06-04

* Added `Leftovers` error variant returned on excessive input.
* `WhiteReader` API changes:
    * Rename `parse_line` to `line` and added `start_line` and `finish_line`.
      So now you can *start*, *continue* or *finish* parsing a line,
      or parse the *line* as a whole.
    * Renamed the `&str`-returning `get_line` to `next_line`.

## 0.1.0 – 2015-06-03

* Initial release
