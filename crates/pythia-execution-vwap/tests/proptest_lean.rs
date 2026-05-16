//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_execution_vwap::*;

proptest! {
    /// Lean: `vwap_ge_min` — VWAP ≥ min price
    #[test]
    fn vwap_ge_min(p1 in 50.0f64..150.0, p2 in 50.0f64..150.0, v1 in 1.0f64..1000.0, v2 in 1.0f64..1000.0) {
        let min_p = p1.min(p2);
        let v = vwap(&[p1, p2], &[v1, v2]);
        prop_assert!(v >= min_p - 1e-10);
    }

    /// Lean: `vwap_ge_min` (dual) — VWAP ≤ max price
    #[test]
    fn vwap_le_max(p1 in 50.0f64..150.0, p2 in 50.0f64..150.0, v1 in 1.0f64..1000.0, v2 in 1.0f64..1000.0) {
        let max_p = p1.max(p2);
        let v = vwap(&[p1, p2], &[v1, v2]);
        prop_assert!(v <= max_p + 1e-10);
    }

    /// Lean: `participation_matches_vwap`
    #[test]
    fn participation_matches(p1 in 50.0f64..150.0, p2 in 50.0f64..150.0, v1 in 1.0f64..1000.0, v2 in 1.0f64..1000.0, alpha in 0.01f64..1.0) {
        let market = vwap(&[p1, p2], &[v1, v2]);
        let ours = participation_vwap(&[p1, p2], &[v1, v2], alpha);
        prop_assert!((market - ours).abs() < 1e-8);
    }
}
