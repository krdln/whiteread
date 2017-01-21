extern crate whiteread;
use whiteread::{WhiteReader, Lengthed};

fn main() {
    let i = std::io::stdin();
    let mut i = WhiteReader::new(i.lock());

    println!("Type n and n pairs. Try inserting newlines in random places.");
    let Lengthed(v): Lengthed<(i32, i32)> = i.p();
    println!("pairs {:?}", v);

    let rest: Vec<String> = i.continue_line().unwrap();
    println!("rest {:?}", rest);
}
