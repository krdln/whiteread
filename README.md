Yet another crate for easily reading values from strings or input.

It was made to mimic `cin >>` functionality
and to be usable for parsing text input in format used in algorithmic contests.

# Features:

* Function-based interface (as opposed to macro-based one).
* Simple: only whitespace can separate values, hence name.
  (so it's not a general solution for parsing arbitrary data).
* Parsing in newline-agnostic mode (just like `cin >>`).
* Easy detection of end of input.
* Proper (`Result`, not panics) handling of errors⁰.
* No unnecessary allocs and locks.
* One-file copy-pastable implementation with no dependencies.

----
⁰) I wanted to just panic for simplicity, but then realized that one `unwrap()`
doesn't hurt too much. But if you really want to force panics, we got you covered too!

# [Documentation](http://krdln.github.io/whiteread/whiteread/index.html)

# [Crate](https://crates.io/crates/whiteread)

# Examples

Reading an integer from stdin:

```rust
let x: i32 = parse_line().unwrap();
```

Tuples and vectors (nest everything as you like)!

```rust
let tup: (i32, f64) = parse_string("  5  3.14  leftovers are ignored");
let v: Vec<(String, u8)> = parse_string("one 1 two 2 three 3");
```

Wrapping `StdinLock` for non-line-based parsing...

```rust
let i = std::io::stdin();
let mut i = WhiteRead::new(i.lock());

// (almost) equivalent to scanf("%d%d", &a, &b) or cin >> a >> b
let (a, b): (i32, i32) = i.parse().unwrap();
```

...or just for speed:

```rust
while let Ok((x, y)) = i.parse_line::<(uint, f32)>() {
	println!("{} {}", y, x);
}
```
