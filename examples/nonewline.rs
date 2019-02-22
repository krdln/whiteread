extern crate whiteread;
use whiteread::adapters::Lengthed;
use whiteread::Reader;

fn main() {
    let i = std::io::stdin();
    let mut i = Reader::new(i.lock());

    println!(
        "Type a number n and then n pairs of numbers.\n\
         Try inserting newlines in random places."
    );
    let Lengthed(v): Lengthed<(i32, i32)> = i.p();
    println!("pairs: {:?}", v);

    let rest: Vec<String> = i.finish_line().unwrap();
    println!("rest of line: {:?}", rest);
}
