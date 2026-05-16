//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (ring, add_nonneg, mul_nonneg, sq_nonneg reasoning).

use proptest::prelude::*;
use pythia_portfolio_efficient::*;

proptest! {
    /// Lean: `portfolioReturn_linear`
    /// Portfolio return is an affine interpolation: mu2 + w*(mu1 - mu2).
    #[test]
    fn return_affine(w in -2.0f64..3.0, mu1 in -1.0f64..1.0, mu2 in -1.0f64..1.0) {
        prop_assert!(check_return_linear(w, mu1, mu2, 1e-10));
    }

    /// Lean: `portfolioVar_nonneg_uncorrelated`
    /// Zero covariance + non-negative variances => nonneg portfolio variance.
    #[test]
    fn var_nonneg_uncorrelated(w in -2.0f64..3.0, v1 in 0.0f64..1.0, v2 in 0.0f64..1.0) {
        prop_assert!(check_var_nonneg_uncorrelated(w, v1, v2));
    }

    /// Lean: `portfolioReturn_at_zero` + `portfolioReturn_at_one` (boundary)
    /// At w=0 return is mu2, at w=1 return is mu1.
    #[test]
    fn return_boundaries(mu1 in -1.0f64..1.0, mu2 in -1.0f64..1.0) {
        prop_assert!((portfolio_return(0.0, mu1, mu2) - mu2).abs() < 1e-12);
        prop_assert!((portfolio_return(1.0, mu1, mu2) - mu1).abs() < 1e-12);
    }

    /// Lean: `portfolioVar_at_zero` + `portfolioVar_at_one` (boundary)
    /// At w=0 variance is v2, at w=1 variance is v1.
    #[test]
    fn var_boundaries(v1 in 0.0f64..1.0, v2 in 0.0f64..1.0, cov in -0.5f64..0.5) {
        prop_assert!((portfolio_var(0.0, v1, v2, cov) - v2).abs() < 1e-12);
        prop_assert!((portfolio_var(1.0, v1, v2, cov) - v1).abs() < 1e-12);
    }
}
