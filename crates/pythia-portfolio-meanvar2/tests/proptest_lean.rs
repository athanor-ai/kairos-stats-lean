//! Property-based tests for mean-variance utility with diversification.
//!
//! Provenance: verified against Lean spec `Pythia.Finance.MeanVarianceUtility`.
//! Each proptest corresponds to a Lean theorem proven in the formal spec.

use proptest::prelude::*;
use pythia_portfolio_meanvar2::*;

proptest! {
    /// Lean: `mvUtility_zero_variance` -- zero variance gives U = mu
    #[test]
    fn zero_variance_gives_mean(
        gamma in 0.01f64..10.0,
        mu in -1.0f64..1.0
    ) {
        let u = mv_utility(gamma, mu, 0.0);
        prop_assert!((u - mu).abs() < 1e-12,
            "U({}, {}, 0) = {} != {}", gamma, mu, u, mu);
    }

    /// Lean: `mvUtility_le_mean` -- utility bounded above by the mean
    #[test]
    fn utility_bounded_by_mean(
        gamma in 0.01f64..10.0,
        mu in -1.0f64..1.0,
        sigma_sq in 0.0f64..1.0
    ) {
        let u = mv_utility(gamma, mu, sigma_sq);
        prop_assert!(u <= mu + 1e-12,
            "U({}, {}, {}) = {} > mu = {}", gamma, mu, sigma_sq, u, mu);
    }

    /// Lean: `mvUtility_mono_return` -- monotone in expected return
    #[test]
    fn monotone_in_return(
        gamma in 0.01f64..10.0,
        mu1 in -1.0f64..1.0,
        mu2 in -1.0f64..1.0,
        sigma_sq in 0.0f64..1.0
    ) {
        let u1 = mv_utility(gamma, mu1, sigma_sq);
        let u2 = mv_utility(gamma, mu2, sigma_sq);
        if mu1 <= mu2 {
            prop_assert!(u1 <= u2 + 1e-12);
        } else {
            prop_assert!(u2 <= u1 + 1e-12);
        }
    }

    /// Lean: `mvUtility_antitone_variance` -- antitone in variance
    #[test]
    fn antitone_in_variance(
        gamma in 0.01f64..10.0,
        mu in -1.0f64..1.0,
        s1 in 0.0f64..1.0,
        s2 in 0.0f64..1.0
    ) {
        let u1 = mv_utility(gamma, mu, s1);
        let u2 = mv_utility(gamma, mu, s2);
        if s1 <= s2 {
            prop_assert!(u2 <= u1 + 1e-12,
                "U(sig={}) = {} > U(sig={}) = {}", s2, u2, s1, u1);
        }
    }
}
