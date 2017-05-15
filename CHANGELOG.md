# Changelog

## 0.4.0 (upcoming)

* Added `Skip` and `SkipAll` to handle ignored values.
* Added `Zeroed` wrapper for parsing 0-terminated lists.
* More consistend API for `WhiteReader`:
    * Renamed `parse` to `continue` (to match `continue_line`)
    * Added `finish` (as a `finish_line` counterpart)

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
