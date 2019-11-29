extern crate whiteread;

use whiteread::reader;

fn read() -> reader::Result<Vec<Vec<u32>>> {
    let mut i = reader::Reader::from_stdin_naive();

    // reading a graph in a format commonly used in algorithmic contests
    let (verts, edges): (usize, usize) = i.line()?;

    let mut g = vec![vec![]; verts + 1];
    for _ in 0..edges {
        let (a, b) = i.line()?;
        g[a as usize].push(b);
        g[b as usize].push(a);
    }

    Ok(g)
}

fn main() {
    match read() {
        Ok(graph) => println!("{:#?}", &graph[1..]),
        Err(e) => println!("Error: {}", e),
    }
}
