use std::io;
use std::io::prelude::*;

fn main() {
    let out = io::stdout();
    write_template(out.lock()).unwrap();
}

fn write_module<W: Write>(w: &mut W, ident: u32, publicity: &str, name: &str) -> io::Result<()> {
    for _ in 0..ident {
        write!(w, "    ")?
    }
    writeln!(w, "{}mod {} {{", publicity, name)?;

    let source = match name {
        "whiteread" => include_str!("lib.rs"),
        "stream" => include_str!("stream.rs"),
        "adapters" => include_str!("adapters.rs"),
        "reader" => include_str!("reader.rs"),
        x => panic!("whiteread-template: unknown module {}", x),
    };

    let mut lines = source.lines();
    while let Some(line) = lines.next() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }

        if trimmed == "#[test]" {
            let ident = ident_len(line);

            // Skip function declaration
            while ident_len(lines.next().unwrap()) == ident {}

            // Skip function body
            loop {
                let line = lines.next().unwrap();
                if ident_len(line) == ident && line.trim() == "}" {
                    break;
                }
            }

            continue;
        }

        if (trimmed.starts_with("mod") || trimmed.starts_with("pub mod")) && trimmed.ends_with(";")
        {
            let name = trimmed
                .split("mod")
                .nth(1)
                .unwrap()
                .split(";")
                .nth(0)
                .unwrap()
                .trim();
            let publicity = trimmed.split("mod").nth(0).unwrap();
            write_module(w, ident + 1, publicity, name)?;
        } else {
            for _ in 0..ident + 1 {
                write!(w, "    ")?
            }
            writeln!(w, "{}", line)?;
        }
    }

    for _ in 0..ident {
        write!(w, "    ")?
    }
    writeln!(w, "}}")?;

    Ok(())
}

fn ident_len(line: &str) -> usize {
    if line.trim() == "" {
        return usize::max_value();
    }
    line.chars().take_while(|c| c.is_whitespace()).count()
}

fn write_template<W: Write>(mut w: W) -> io::Result<()> {
    write!(
        w,
        "{}",
        &r"
use whiteread as w;

fn run() -> w::reader::Result<()> {
    let input = std::io::stdin();
    let input = input.lock();
    let mut input = w::Reader::new(input);

    let _x: i32 = input.line()?;

    Ok(())
}

fn main() {
    run().unwrap()
}

// From https://github.com/krdln/whiteread on MIT license
#[allow(dead_code)]
"[1..]
    )?;

    write_module(&mut w, 0, "", "whiteread")?;

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
