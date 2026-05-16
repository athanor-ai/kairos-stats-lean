//! Provenance: VERIFIED — the Lean proofs in
//! `Pythia.Finance.Portfolio.InformationRatio` use `div_pos`, `sub_pos`,
//! `sub_div`, `mul_div_mul_left`, and `ring` to establish all results
//! non-tautologically. These proptests exercise the same invariants in Rust.

use proptest::prelude::*;
use pythia_portfolio_info_ratio::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `informationRatio_scale_invariant`
    /// For any alpha > 0, IR(alpha*R_p, alpha*R_b, alpha*sigma_a) == IR(R_p, R_b, sigma_a).
    #[test]
    fn prop_scale_invariance(
        r_p in -1000.0..1000.0f64,
        r_b in -1000.0..1000.0f64,
        sigma_a in 0.001..1000.0f64,
        alpha in 0.001..1000.0f64,
    ) {
        let base = information_ratio(r_p, r_b, sigma_a);
        let scaled = information_ratio_scaled(alpha, r_p, r_b, sigma_a);
        prop_assert!((base - scaled).abs() < EPS * (1.0 + base.abs()),
            "scale invariance violated: base={}, scaled={}", base, scaled);
    }

    /// Lean: `informationRatio_diff_eq_active`
    /// IR(R_p) - IR(R_q) = (R_p - R_q) / sigma_a.
    #[test]
    fn prop_diff_eq_active(
        r_p in -1000.0..1000.0f64,
        r_q in -1000.0..1000.0f64,
        r_b in -1000.0..1000.0f64,
        sigma_a in 0.001..1000.0f64,
    ) {
        let (diff_ir, expected) = information_ratio_diff(r_p, r_q, r_b, sigma_a);
        prop_assert!((diff_ir - expected).abs() < EPS * (1.0 + expected.abs()),
            "diff identity violated: diff_ir={}, expected={}", diff_ir, expected);
    }

    /// Lean: `informationRatio_pos`
    /// Positive active return and positive tracking error => positive IR.
    #[test]
    fn prop_positive_when_outperforming(
        active in 0.001..1000.0f64,
        sigma_a in 0.001..1000.0f64,
        r_b in -500.0..500.0f64,
    ) {
        let r_p = r_b + active;
        let ir = information_ratio(r_p, r_b, sigma_a);
        prop_assert!(ir > 0.0, "expected positive IR, got {}", ir);
        prop_assert!(information_ratio_is_positive(r_p, r_b, sigma_a));
    }

    /// Structural: IR is 1/sigma_a-Lipschitz in R_p.
    /// |IR(R_p) - IR(R_q)| = |R_p - R_q| / sigma_a.
    #[test]
    fn prop_lipschitz_in_portfolio_return(
        r_p in -1000.0..1000.0f64,
        r_q in -1000.0..1000.0f64,
        r_b in -1000.0..1000.0f64,
        sigma_a in 0.001..1000.0f64,
    ) {
        let ir_p = information_ratio(r_p, r_b, sigma_a);
        let ir_q = information_ratio(r_q, r_b, sigma_a);
        let lip = (r_p - r_q).abs() / sigma_a;
        prop_assert!((ir_p - ir_q).abs() < lip + EPS,
            "Lipschitz violated: |IR_p - IR_q|={}, bound={}", (ir_p - ir_q).abs(), lip);
    }
}
