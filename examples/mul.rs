extern crate toypqsnark;
use toypqsnark::field::FE;

fn main() {
    let v = FE::from_words(1234567, 2345678, 3456789, 4567890);
    let mut a = Vec::new();
    a.resize(1, v);
    for i in 0 .. 1_000_000_000 / a.len() {
        for aa in &mut a {
            *aa = aa.square();
        }
    }
    for aa in &a {
        println!("{:?}", aa.to_words());
    }
}
