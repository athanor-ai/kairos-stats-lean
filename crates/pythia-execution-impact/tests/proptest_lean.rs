use proptest::prelude::*;
use pythia_execution_impact::*;

proptest! {
    /// Lean: impactSq_pos: strictly positive when all inputs > 0
    #[test]
    fn prop_impact_sq_pos(
        sigma_sq in 0.001_f64..100.0,
        q in 0.001_f64..1e6,
        v in 0.001_f64..1e9,
    ) {
        let result = impact_sq(sigma_sq, q, v);
        prop_assert!(result > 0.0,
            "impact_sq({sigma_sq}, {q}, {v}) = {result} <= 0");
    }

    /// Lean: impactSq_mono_quantity: monotone in Q for sigma_sq >= 0, V > 0
    #[test]
    fn prop_mono_quantity(
        sigma_sq in 0.0_f64..100.0,
        q1 in 0.0_f64..1e6,
        delta in 0.0_f64..1e6,
        v in 0.001_f64..1e9,
    ) {
        let q2 = q1 + delta;
        let i1 = impact_sq(sigma_sq, q1, v);
        let i2 = impact_sq(sigma_sq, q2, v);
        prop_assert!(i1 <= i2 + 1e-12,
            "mono_quantity failed: i1={i1} > i2={i2} for Q1={q1}, Q2={q2}");
    }

    /// Lean: impactSq_linear_quantity: additive in Q
    #[test]
    fn prop_linear_quantity(
        sigma_sq in -100.0_f64..100.0,
        q1 in -1e4_f64..1e4,
        q2 in -1e4_f64..1e4,
        v in 0.001_f64..1e6,
    ) {
        let combined = impact_sq(sigma_sq, q1 + q2, v);
        let sum = impact_sq(sigma_sq, q1, v) + impact_sq(sigma_sq, q2, v);
        prop_assert!((combined - sum).abs() < 1e-8,
            "linear_quantity failed: combined={combined}, sum={sum}");
    }

    /// Lean: impactSq_scale: scaling sigma_sq by c scales result by c
    #[test]
    fn prop_scale(
        c in -100.0_f64..100.0,
        sigma_sq in -100.0_f64..100.0,
        q in -1e4_f64..1e4,
        v in 0.001_f64..1e6,
    ) {
        let scaled = impact_sq(c * sigma_sq, q, v);
        let base = c * impact_sq(sigma_sq, q, v);
        prop_assert!((scaled - base).abs() < 1e-8,
            "scale failed: scaled={scaled}, base={base}");
    }
}
