use proptest::prelude::*;
use pythia_credit_merton::*;

proptest! {
    /// Lean: distanceToDefault_pos: DD > 0 when log_VD > 0, drift >= 0, sigma > 0, sqrt_T > 0
    #[test]
    fn prop_dd_positive(
        log_vd in 0.01_f64..2.0,
        drift_adj in 0.0_f64..0.2,
        t in 0.1_f64..5.0,
        sigma in 0.05_f64..1.0,
        sqrt_t in 0.1_f64..3.0,
    ) {
        let dd = distance_to_default(log_vd, drift_adj, t, sigma, sqrt_t);
        prop_assert!(dd > -1e-12,
            "DD should be positive: dd={dd}");
    }

    /// Lean: distanceToDefault_mono_logVD: DD monotone in log(V/D)
    #[test]
    fn prop_dd_mono_log_vd(
        l1 in -2.0_f64..2.0,
        delta in 0.0_f64..2.0,
        drift_adj in -0.1_f64..0.2,
        t in 0.1_f64..5.0,
        sigma in 0.05_f64..1.0,
        sqrt_t in 0.1_f64..3.0,
    ) {
        let l2 = l1 + delta;
        let dd1 = distance_to_default(l1, drift_adj, t, sigma, sqrt_t);
        let dd2 = distance_to_default(l2, drift_adj, t, sigma, sqrt_t);
        prop_assert!(dd1 <= dd2 + 1e-10,
            "DD not monotone: dd1={dd1}, dd2={dd2}");
    }

    /// Lean: equityAtMaturity_nonneg: equity >= 0 always (limited liability)
    #[test]
    fn prop_equity_nonneg(
        v in 0.0_f64..1000.0,
        d in 0.0_f64..1000.0,
    ) {
        let eq = equity_at_maturity(v, d);
        prop_assert!(eq >= -1e-15,
            "equity negative: eq={eq}");
    }

    /// Lean: equityAtMaturity_solvent + insolvent: matches max(V-D, 0) exactly
    #[test]
    fn prop_equity_matches_call(
        v in 0.0_f64..500.0,
        d in 0.0_f64..500.0,
    ) {
        let eq = equity_at_maturity(v, d);
        let expected = (v - d).max(0.0);
        prop_assert!((eq - expected).abs() < 1e-12,
            "equity mismatch: eq={eq}, expected={expected}");
    }
}
