# whiteread

[![Build Status](https://travis-ci.com/krdln/whiteread.svg?branch=master)](https://travis-ci.com/krdln/whiteread)

Yet another crate for easily reading values from strings or input.

It was made to mimic `cin >>` functionality
and to be usable for parsing text input in format used in algorithmic contests.

### [Documentation (0.5.0)](https://docs.rs/whiteread/0.5.0/whiteread/)

### [Crate](https://crates.io/crates/whiteread)

### [Changelog](CHANGELOG.md)

## Features:

* Function-based interface (as opposed to macro-based one).
* Simple: only whitespace can separate values, hence name.
  (so it's not a general solution for parsing arbitrary data).
* Parsing in newline-agnostic mode (just like `cin >>`).
  (Line-aware mode is also supported)
* Easy detection of end of input.
* Proper (`Result`, not panics) handling of errors.
* No unnecessary allocs and locks.
* "One-file" copy-pastable implementation with no dependencies.
  This crate uses modules, but you can use `cargo run` to generate
  a concatenated single-file template (see below).

## Examples

Reading an integer from stdin:

```rust
let x: i32 = parse_line()?;
```

Tuples and vectors (nest everything as you like)!

```rust
let tup: (i32, f64) = parse_string("  5  3.14 ")?;
let v: Vec<(String, u8)> = parse_string("one 1 two 2 three 3")?;
```

Wrapping `StdinLock` for non-line-based parsing...

```rust
let mut i = Reader::from_stdin_naive();

// (almost) equivalent to scanf("%d%d", &a, &b) or cin >> a >> b
let (a, b): (i32, i32) = i.parse()?;
```

...or just for speed (the line-buffer will be allocated just once):

```rust
while let Some((x, y)) = i.line::<Option<(usize, f32)>>()? {
	println!("{} {}", y, x);
}
```

Reading a file (can also use `Reader` for more control):

```rust
let number: i32 = parse_file("number.txt")?;
```

On failure, a rendered error will be provided by default, even when unwrapping, eg.:

```console
Error: excessive input provided at
6 | hello world 1 2 3
                ^
```

## Installation

`cargo add whiteread` or add this to your `Cargo.toml`:

```toml
[dependencies]
whiteread = "0.5.0"
```

Minimal supported Rust version is 1.18.

### Using in non-Cargo environment

If you want to use this crate where cargo is unavailable,
*whiteread* can be squished into single file. Here's how
to generate a template containing a *whiteread* module:

```sh
$ cargo install whiteread
$ whiteread-template > my_file.rs
```

Alternatively, you can clone this repository and just
`cargo run`.
