use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pythia_hft_orderbook::{OrderBook, Side};

fn bench_insert_bid(c: &mut Criterion) {
    c.bench_function("insert bid (empty book)", |b| {
        b.iter(|| {
            let mut book = OrderBook::new(1);
            book.insert(black_box(1), black_box(100), black_box(10), Side::Bid);
        })
    });

    c.bench_function("insert bid (100 levels)", |b| {
        let mut book = OrderBook::new(1);
        for i in 0..100 {
            book.insert(i, 1000 - i as i64, 10, Side::Bid);
        }
        b.iter(|| {
            let mut book_clone = OrderBook::new(1);
            // Rebuild to avoid growing forever
            for i in 0..100 {
                book_clone.insert(i, 1000 - i as i64, 10, Side::Bid);
            }
            book_clone.insert(black_box(999), black_box(500), black_box(10), Side::Bid);
        })
    });
}

fn bench_crossing_fill(c: &mut Criterion) {
    c.bench_function("crossing fill (single level)", |b| {
        b.iter(|| {
            let mut book = OrderBook::new(1);
            book.insert(1, 100, 100, Side::Ask);
            book.insert(2, black_box(100), black_box(50), Side::Bid);
        })
    });
}

fn bench_cancel(c: &mut Criterion) {
    c.bench_function("cancel (50 orders)", |b| {
        b.iter(|| {
            let mut book = OrderBook::new(1);
            for i in 0..50 {
                book.insert(i, 100 + i as i64, 10, Side::Bid);
            }
            book.cancel(black_box(25));
        })
    });
}

criterion_group!(benches, bench_insert_bid, bench_crossing_fill, bench_cancel);
criterion_main!(benches);
