//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (linarith, mul_nonneg, div_nonneg reasoning).

use proptest::prelude::*;
use pythia_portfolio_risk_adjusted::*;

proptest! {
    /// Lean: `excessReturn_pos_iff` — positive excess iff rf < mu
    #[test]
    fn prop_excess_return_sign(mu in -1000.0..1000.0f64, rf in -1000.0..1000.0f64) {
        let er = excess_return(mu, rf);
        if rf < mu {
            prop_assert!(er > 0.0, "expected positive excess return, got {}", er);
        } else if rf > mu {
            prop_assert!(er < 0.0, "expected negative excess return, got {}", er);
        } else {
            prop_assert!(er.abs() < 1e-10, "expected zero excess return, got {}", er);
        }
    }

    /// Lean: `certaintyEquiv_le_mean` — CE <= mu for nonneg gamma and sigma_sq
    #[test]
    fn prop_ce_le_mean(mu in -1000.0..1000.0f64, gamma in 0.0..100.0f64, sigma_sq in 0.0..100.0f64) {
        let ce = certainty_equiv(mu, gamma, sigma_sq);
        prop_assert!(ce <= mu + 1e-10,
            "CE should not exceed mu: ce={}, mu={}", ce, mu);
    }

    /// Lean: `certaintyEquiv_mono_return` — monotone in mu
    #[test]
    fn prop_ce_mono_return(mu1 in -1000.0..1000.0f64, delta in 0.0..1000.0f64, gamma in -100.0..100.0f64, sigma_sq in 0.0..100.0f64) {
        let mu2 = mu1 + delta;
        let ce1 = certainty_equiv(mu1, gamma, sigma_sq);
        let ce2 = certainty_equiv(mu2, gamma, sigma_sq);
        prop_assert!(ce1 <= ce2 + 1e-10,
            "monotonicity violated: ce1={}, ce2={}", ce1, ce2);
    }

    /// Lean: `certaintyEquiv_antitone_risk` — antitone in gamma for nonneg sigma_sq
    #[test]
    fn prop_ce_antitone_risk(mu in -1000.0..1000.0f64, g1 in 0.0..100.0f64, delta in 0.0..100.0f64, sigma_sq in 0.0..100.0f64) {
        let g2 = g1 + delta;
        let ce1 = certainty_equiv(mu, g1, sigma_sq);
        let ce2 = certainty_equiv(mu, g2, sigma_sq);
        prop_assert!(ce2 <= ce1 + 1e-10,
            "antitone violated: ce(g1={})={}, ce(g2={})={}", g1, ce1, g2, ce2);
    }
}
