//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (ring, add_nonneg, mul_nonneg, sq_nonneg).

use proptest::prelude::*;
use pythia_portfolio_efficient_frontier::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `portfolioReturn_at_zero` + `portfolioReturn_at_one` — boundary cases
    #[test]
    fn prop_return_boundaries(mu1 in -100.0..100.0f64, mu2 in -100.0..100.0f64) {
        prop_assert!((portfolio_return(0.0, mu1, mu2) - mu2).abs() < EPS);
        prop_assert!((portfolio_return(1.0, mu1, mu2) - mu1).abs() < EPS);
    }

    /// Lean: `portfolioReturn_linear` — return equals affine form
    #[test]
    fn prop_return_linear(w in -2.0..2.0f64, mu1 in -100.0..100.0f64, mu2 in -100.0..100.0f64) {
        let r = portfolio_return(w, mu1, mu2);
        let r_lin = portfolio_return_linear(w, mu1, mu2);
        prop_assert!((r - r_lin).abs() < EPS * (1.0 + r.abs()),
            "linear form mismatch: r={}, r_lin={}", r, r_lin);
    }

    /// Lean: `portfolioVar_nonneg_uncorrelated` — nonneg variance for zero cov
    #[test]
    fn prop_var_nonneg_uncorrelated(w in -5.0..5.0f64, v1 in 0.0..100.0f64, v2 in 0.0..100.0f64) {
        let v = portfolio_var(w, v1, v2, 0.0);
        prop_assert!(v >= -EPS,
            "variance should be nonneg: w={}, v1={}, v2={}, got v={}", w, v1, v2, v);
    }

    /// Lean: `portfolioVar_at_zero` + `portfolioVar_at_one` — boundary cases
    #[test]
    fn prop_var_boundaries(v1 in 0.0..100.0f64, v2 in 0.0..100.0f64, cov in -50.0..50.0f64) {
        prop_assert!((portfolio_var(0.0, v1, v2, cov) - v2).abs() < EPS);
        prop_assert!((portfolio_var(1.0, v1, v2, cov) - v1).abs() < EPS);
    }
}
