//! Property-based tests for tail risk Euler decomposition.
//!
//! Provenance: verified against Lean spec `Pythia.Finance.Risk.TailRiskDecomp`.
//! Each proptest corresponds to a Lean theorem proven in the formal spec.

use proptest::prelude::*;
use pythia_risk_tailrisk::*;

proptest! {
    /// Lean: `esDecomp_sum_eq_total` -- contributions sum to total ES
    #[test]
    fn decomp_sums_to_total(
        w1 in 0.0f64..1.0,
        w2 in 0.0f64..1.0,
        w3 in 0.0f64..1.0,
        m1 in 0.0f64..0.2,
        m2 in 0.0f64..0.2,
        m3 in 0.0f64..0.2
    ) {
        let w = vec![w1, w2, w3];
        let m = vec![m1, m2, m3];
        let contrib = es_contributions(&w, &m);
        let total_contrib = es_total(&contrib);
        let total_decomp = es_decomp(&w, &m);
        prop_assert!((total_contrib - total_decomp).abs() < 1e-12);
    }

    /// Lean: `esContrib_le_total` -- each nonneg contribution bounded by total
    #[test]
    fn each_contrib_le_total(
        w1 in 0.0f64..1.0,
        w2 in 0.0f64..1.0,
        w3 in 0.0f64..1.0,
        m1 in 0.0f64..0.2,
        m2 in 0.0f64..0.2,
        m3 in 0.0f64..0.2
    ) {
        let w = vec![w1, w2, w3];
        let m = vec![m1, m2, m3];
        let contrib = es_contributions(&w, &m);
        let total = es_total(&contrib);
        for c in &contrib {
            prop_assert!(*c <= total + 1e-12);
        }
    }

    /// Lean: `esDecomp_scale` -- scaling weights scales ES proportionally
    #[test]
    fn scaling_homogeneity(
        c in 0.0f64..10.0,
        w1 in 0.0f64..1.0,
        w2 in 0.0f64..1.0,
        m1 in 0.0f64..0.2,
        m2 in 0.0f64..0.2
    ) {
        let w = vec![w1, w2];
        let m = vec![m1, m2];
        let scaled_w: Vec<f64> = w.iter().map(|wi| c * wi).collect();
        let es_scaled = es_decomp(&scaled_w, &m);
        let es_original = es_decomp(&w, &m);
        prop_assert!((es_scaled - c * es_original).abs() < 1e-10,
            "es_decomp(c*w, m) = {} != c * es_decomp(w, m) = {}", es_scaled, c * es_original);
    }

    /// Lean: `esContrib_frac_sum_one` -- fractional contributions sum to 1
    #[test]
    fn frac_sum_one(
        w1 in 0.01f64..1.0,
        w2 in 0.01f64..1.0,
        w3 in 0.01f64..1.0,
        m1 in 0.01f64..0.2,
        m2 in 0.01f64..0.2,
        m3 in 0.01f64..0.2
    ) {
        let w = vec![w1, w2, w3];
        let m = vec![m1, m2, m3];
        let contrib = es_contributions(&w, &m);
        if let Some(fracs) = es_frac_contributions(&contrib) {
            let sum: f64 = fracs.iter().sum();
            prop_assert!((sum - 1.0).abs() < 1e-10,
                "Fractional contributions sum to {} != 1.0", sum);
        }
    }
}
