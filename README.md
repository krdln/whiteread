Yet another crate for easily reading values from strings or input.

It was made to mimic `cin >>` functionality
and to be usable for parsing text input in format used in algorithmic contests.

### [Documentation (0.4.0)](https://docs.rs/whiteread/0.4.0/whiteread/)

### [Crate](https://crates.io/crates/whiteread)

### [Changelog](CHANGELOG.md)

# Features:

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

# Examples

Reading an integer from stdin:

```rust
let x: i32 = parse_line().unwrap();
```

Tuples and vectors (nest everything as you like)!

```rust
let tup: (i32, f64) = parse_string("  5  3.14 ").unwrap();
let v: Vec<(String, u8)> = parse_string("one 1 two 2 three 3").unwrap();
```

Wrapping `StdinLock` for non-line-based parsing...

```rust
let i = std::io::stdin();
let mut i = Reader::new(i.lock());

// (almost) equivalent to scanf("%d%d", &a, &b) or cin >> a >> b
let (a, b): (i32, i32) = i.parse().unwrap();
```

...or just for speed:

```rust
while let Ok((x, y)) = i.line::<(usize, f32)>() {
	println!("{} {}", y, x);
}
```

Reading a file (can also use `Reader` for more control):

```rust
let number: i32 = parse_file("number.txt").unwrap();
```

# Installation

`cargo add whiteread` or add this to your `Cargo.toml`:

```toml
[dependencies]
whiteread = "0.4.0"
```

## Using in non-Cargo environment

If you want to use this crate where cargo is unavailable,
*whiteread* can be squished into single file. Here's how
to generate a template containing a *whiteread* module:

```sh
$ cargo install whiteread
$ whiteread-template > my_file.rs
```

Alternatively, you can clone this repository and just
`cargo run`.
