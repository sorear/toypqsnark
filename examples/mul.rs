extern crate toypqsnark;
use toypqsnark::field::FE;
use toypqsnark::hash;
use toypqsnark::fft;

fn main() {
    let k = std::env::args().nth(1).unwrap().parse::<usize>().unwrap();

    let mut poly = Vec::new();
    poly.resize(1 << k, FE::zero());

    for fe in hash::testdata(1 << 15, 1000) {
        poly[fe.to_words().0 as usize & ((1 << k) - 1)] = fe;
    }

    let beta = hash::testdata(k, 0);

    let start = std::time::Instant::now();
    fft::additive_fft(&mut poly, 1 << k, &beta);
    println!(
        "{:?} --- {}",
        std::time::Instant::now().duration_since(start),
        poly[0].to_words().0 & 1
    );
}
