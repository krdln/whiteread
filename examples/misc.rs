extern crate whiteread;
use whiteread::{WhiteReader, parse_string, Lenghted, White};

fn main() {
	// parse_string function
	
		// single values (like .parse(), but with implicit unwrap;
		// (None is only for nonexistent values, format is assumed to be always correct))
		assert_eq!(parse_string("3.5").ok(), Some( 3.5f32 ));
		
		// tuples (up to three) and strings
		assert_eq!(parse_string("1 foo 2").ok(), Some( (1, "foo".to_string(), 2) ));
		
		// nested tuples
		assert_eq!(parse_string("1 2 3 4").ok(), Some( ((1,2), (3,4)) ));
		assert_eq!(parse_string("1 2 3 4").ok(), Some( (1, (2,3,4)) ));
		
		// Vec<T> is read till the end
		assert_eq!(parse_string("10 11 20 21").ok(), Some( vec![(10, 11), (20, 21)] ));
		
		// Lenghted<T> wraps Vec<T> and is prefixed by length
		let data = "42 hejka  3 1 2 3  2 4 5  1 6";
		let foo : ((i32, String), Vec<Lenghted<i32>>) = parse_string(data).unwrap();
		println!("{} parsed as:\n{:?}\n", data, foo);
		println!("Now give me pairs: (end with ^D)");
	
	// reader example
	let i = std::io::stdin();
	let mut i = WhiteReader::new(i.lock());
	
	while let Ok((x, y)) = i.parse_line::<(f32, f32)>() {
		println!("{} * {} = {}", x, y, x*y);
	}
	
	// using iterator directly
	for s in ["1 string sss", "2 vec 1 2 3", "3 ??? bla bla"].iter() {
		let mut words = s.split_whitespace();
		let (x, name): (u8, String) = White::read(&mut words).unwrap();
		print!("example nr {}: {}: ", x, name);
		
		if &name == "string" {
			println!("{:?}", String::read(&mut words).unwrap());
		} else if &name == "vec" {
			println!("{:?}", <Vec<u16> as White>::read(&mut words).unwrap()); // try whithout "as" :P
		} else { println!("something"); }
	}
}
