use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pythia_hft_fixedpoint_strong::TrackedFP;

const SCALE: u32 = 65536;

fn bench_tracked_add(c: &mut Criterion) {
    let a = TrackedFP::from_real(100.5, SCALE);
    let b = TrackedFP::from_real(200.7, SCALE);
    c.bench_function("tracked_add", |bencher| {
        bencher.iter(|| black_box(a).add(black_box(b)))
    });
}

fn bench_tracked_mul(c: &mut Criterion) {
    let a = TrackedFP::from_real(3.14, SCALE);
    let b = TrackedFP::from_real(2.71, SCALE);
    c.bench_function("tracked_mul", |bencher| {
        bencher.iter(|| black_box(a).mul(black_box(b)))
    });
}

fn bench_safe_cmp(c: &mut Criterion) {
    let a = TrackedFP::from_real(100.0, SCALE);
    let b = TrackedFP::from_real(200.0, SCALE);
    c.bench_function("safe_cmp", |bencher| {
        bencher.iter(|| black_box(a).safe_cmp(black_box(&b)))
    });
}

fn bench_pipeline_10_stage(c: &mut Criterion) {
    c.bench_function("pipeline_10_add", |bencher| {
        bencher.iter(|| {
            let mut acc = TrackedFP::from_real(0.0, SCALE);
            for i in 1..=10 {
                acc = acc.add(TrackedFP::from_real(i as f64 * 0.1, SCALE));
            }
            black_box(acc)
        })
    });
}

criterion_group!(benches, bench_tracked_add, bench_tracked_mul, bench_safe_cmp, bench_pipeline_10_stage);
criterion_main!(benches);
