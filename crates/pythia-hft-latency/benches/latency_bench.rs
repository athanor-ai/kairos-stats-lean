use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pythia_hft_latency::{Pipeline, Stage, batch_rounds};

fn bench_pipeline_wcet(c: &mut Criterion) {
    let p = Pipeline::new(vec![
        Stage::new("decode", 50, 30),
        Stage::new("lookup", 100, 80),
        Stage::new("match", 200, 50),
        Stage::new("risk", 30, 20),
        Stage::new("send", 80, 60),
    ]);
    c.bench_function("pipeline_wcet_5stage", |b| {
        b.iter(|| black_box(&p).total_wcet_ns())
    });
}

fn bench_batch_rounds(c: &mut Criterion) {
    c.bench_function("batch_rounds", |b| {
        b.iter(|| batch_rounds(black_box(10000), black_box(64)))
    });
}

criterion_group!(benches, bench_pipeline_wcet, bench_batch_rounds);
criterion_main!(benches);
