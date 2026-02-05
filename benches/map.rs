use divan::{Bencher, black_box};

fn main() {
    divan::main();
}

fn data(len: u32, distinct: u32) -> Vec<u32> {
    (0..len)
        .map(|mut x| {
            x ^= x << 13;
            x ^= x >> 17;
            (x << 5) % distinct
        })
        .collect()
}

#[divan::bench(args = [
    (100, 10),
    (100, 100),
    (1_000, 100),
    (1_000, 1_000),
    (10_000, 1_000),
    (10_000, 10_000),
])]
fn vec(b: Bencher, (len, distinct): (u32, u32)) {
    let data = black_box(data(len, distinct));
    b.bench(|| {
        let mut vec = vec![];
        for n in &data {
            let mut found = false;
            for (k, v) in &mut vec {
                if *k == n {
                    *v += 1;
                    found = true;
                    break;
                }
            }
            if !found {
                vec.push((n, 1));
            }
        }
        black_box(vec);
    });
}

#[divan::bench(args = [
    (100, 10),
    (100, 100),
    (1_000, 100),
    (1_000, 1_000),
    (10_000, 1_000),
    (10_000, 10_000),
])]
fn std_map(b: Bencher, (len, distinct): (u32, u32)) {
    let data = black_box(data(len, distinct));
    b.bench(|| {
        let mut map = std::collections::HashMap::new();
        for n in &data {
            match map.get_mut(n) {
                Some(v) => *v += 1,
                None => {
                    map.insert(*n, 1);
                }
            }
        }
        black_box(map);
    });
}

#[divan::bench(args = [
    (100, 10),
    (100, 100),
    (1_000, 100),
    (1_000, 1_000),
    (10_000, 1_000),
    (10_000, 10_000),
])]
fn map(b: Bencher, (len, distinct): (u32, u32)) {
    let data = black_box(data(len, distinct));
    b.bench(|| {
        let mut map = hash::HashMap::default();
        for n in &data {
            match map.get(*n) {
                Some(v) => map.insert(*n, v + 1),
                None => map.insert(*n, 1),
            };
        }
        black_box(map);
    });
}
