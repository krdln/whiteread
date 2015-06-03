extern crate whiteread;

fn read() -> Vec<Vec<u32>> {    
    let i = std::io::stdin();
    let mut i = whiteread::WhiteReader::new(i.lock());
    
    // reading a graph in a format commonly used in algorithmic contests
    let (verts, edges): (usize, usize) = i.parse_line().unwrap();
    
    let mut g = vec![vec![]; verts + 1];
    for _ in 0..edges {
        let (a, b) = i.parse_line().unwrap();
        g[a as usize].push(b);
        g[b as usize].push(a);
    }
    
    g
}

fn main() {
	println!("{:?}", &read()[1..])
}
