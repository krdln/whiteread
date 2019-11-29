extern crate whiteread;
use whiteread::adapters::Lengthed;
use whiteread::Reader;

fn main() {
    let mut i = Reader::from_stdin_naive();

    println!(
        "Type a number n and then n pairs of numbers.\n\
         Try inserting newlines in random places."
    );
    let Lengthed(v): Lengthed<(i32, i32)> = i.p();
    println!("pairs: {:?}", v);

    let rest: Vec<String> = i.finish_line().unwrap();
    println!("rest of line: {:?}", rest);
}
