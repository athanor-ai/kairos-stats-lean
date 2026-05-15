use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pythia_hft_riskgate::{risk_check, TradeOrder};

fn bench_risk_check(c: &mut Criterion) {
    let order = TradeOrder { qty: 100 };
    c.bench_function("risk_check (allow)", |b| {
        b.iter(|| risk_check(black_box(50), black_box(&order), black_box(1000)))
    });

    let big_order = TradeOrder { qty: 5000 };
    c.bench_function("risk_check (block)", |b| {
        b.iter(|| risk_check(black_box(50), black_box(&big_order), black_box(1000)))
    });

    c.bench_function("risk_check (worst case: near limit)", |b| {
        let near_limit_order = TradeOrder { qty: 999 };
        b.iter(|| risk_check(black_box(0), black_box(&near_limit_order), black_box(1000)))
    });
}

criterion_group!(benches, bench_risk_check);
criterion_main!(benches);
