extern crate toypqsnark;
use toypqsnark::field::FE;

fn main() {
    let mut rcon = "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89"
        .parse::<FE>()
        .unwrap(); // fractional part of pi
    for _ in 0..128 {
        println!("    FE::from_words{:?},", rcon.to_words());
        rcon = rcon.square();
    }
}
