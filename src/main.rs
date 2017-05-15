use std::io;
use std::io::prelude::*;

fn main() {
    let out = io::stdout();
    write_template(out.lock()).unwrap();
}

fn write_template<W: Write>(mut w: W) -> io::Result<()> {
    let source = include_str!("lib.rs");

    write!(w, "{}", &r"
use whiteread as w;

fn main() {
    let input = std::io::stdin();
    let input = input.lock();
    let mut input = w::Reader::new(input);
    
    let _x: i32 = input.line().unwrap();
}

#[allow(dead_code)]
mod whiteread {
    // From https://github.com/krdln/whiteread on MIT license
"[1..])?;

    for line in source.lines() {
        if line.trim().is_empty() || line.trim().starts_with("//") {
            continue;
        }
        writeln!(w, "    {}", line)?;
    }

    writeln!(w, "}}")?;

    w.flush()
}

#[test]
fn test_template() {
    extern crate tempfile;
    use std::process::Command;

    let mut source_file = tempfile::NamedTempFile::new().unwrap();
    let output_file = tempfile::NamedTempFile::new().unwrap();

    write_template(io::BufWriter::new(&mut source_file)).unwrap();

    let status = Command::new("rustc")
        .arg(source_file.path())
        .args(&["--crate-name", "template", "-o"])
        .arg(output_file.path())
        .status()
        .unwrap();
    assert!(status.success());
}
