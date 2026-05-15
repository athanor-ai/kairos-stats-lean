//! # Sortino Ratio (algebraic form)
//!
//! Rust port of `Pythia.Finance.Portfolio.SortinoRatio`.
//!
//! The Sortino ratio refines the Sharpe ratio by replacing total
//! volatility with the *downside deviation* `sigma_d`:
//!
//! ```text
//! Sortino(mu, rf, sigma_d) = (mu - rf) / sigma_d
//! ```
//!
//! ## Lean theorems mirrored
//!
//! - [`sortinoRatio`] — definition `(mu - rf) / sigma_d`
//! - [`sortinoRatio_pos`] — positive when `rf < mu` and `0 < sigma_d`
//! - [`sortinoRatio_mono_excess`] — monotone in excess return
//! - [`sortinoRatio_scale_invariant`] — invariant under positive rescaling

/// Compute the Sortino ratio: `(mu - rf) / sigma_d`.
///
/// Corresponds to Lean `Pythia.Finance.sortinoRatio`.
///
/// `sigma_d` is the downside deviation (not total volatility).
/// Returns `f64::NAN` when `sigma_d == 0.0` per IEEE 754.
#[inline]
pub fn sortino_ratio(mu: f64, rf: f64, sigma_d: f64) -> f64 {
    (mu - rf) / sigma_d
}

/// Returns `true` when the Sortino ratio is strictly positive.
///
/// Corresponds to Lean `sortinoRatio_pos`: requires `rf < mu` and `0 < sigma_d`.
#[inline]
pub fn sortino_ratio_is_positive(mu: f64, rf: f64, sigma_d: f64) -> bool {
    rf < mu && sigma_d > 0.0
}

/// Checks monotonicity in excess return: for fixed positive `sigma_d`,
/// if `excess1 <= excess2` then `sortino1 <= sortino2`.
///
/// Corresponds to Lean `sortinoRatio_mono_excess`.
#[inline]
pub fn sortino_ratio_mono_excess(excess1: f64, excess2: f64, sigma_d: f64) -> bool {
    if sigma_d <= 0.0 {
        return false; // precondition not met
    }
    if excess1 <= excess2 {
        (excess1 / sigma_d) <= (excess2 / sigma_d)
    } else {
        false
    }
}

/// Scale-invariance: `sortino(alpha*mu, alpha*rf, alpha*sigma_d) == sortino(mu, rf, sigma_d)`
/// for `alpha > 0`.
///
/// Corresponds to Lean `sortinoRatio_scale_invariant`.
#[inline]
pub fn sortino_ratio_scaled(alpha: f64, mu: f64, rf: f64, sigma_d: f64) -> f64 {
    sortino_ratio(alpha * mu, alpha * rf, alpha * sigma_d)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Test basic computation: sortino_ratio(0.12, 0.03, 0.10) = 0.09/0.10
    #[test]
    fn test_basic_computation() {
        let result = sortino_ratio(0.12, 0.03, 0.10);
        let expected = 0.09 / 0.10;
        assert!((result - expected).abs() < EPS);
    }

    /// Lean: `sortinoRatio_pos` — positive when rf < mu and sigma_d > 0
    #[test]
    fn test_positivity() {
        let r = sortino_ratio(0.15, 0.03, 0.08);
        assert!(r > 0.0);
        assert!(sortino_ratio_is_positive(0.15, 0.03, 0.08));
    }

    /// Lean: `sortinoRatio_pos` — negative when mu < rf
    #[test]
    fn test_negative_excess() {
        let r = sortino_ratio(0.01, 0.05, 0.10);
        assert!(r < 0.0);
        assert!(!sortino_ratio_is_positive(0.01, 0.05, 0.10));
    }

    /// Lean: `sortinoRatio_scale_invariant`
    #[test]
    fn test_scale_invariance() {
        let base = sortino_ratio(0.10, 0.02, 0.07);
        let scaled = sortino_ratio_scaled(5.0, 0.10, 0.02, 0.07);
        assert!((base - scaled).abs() < EPS);
    }

    /// Lean: `sortinoRatio_mono_excess` — monotonicity check
    #[test]
    fn test_monotone_excess() {
        let sigma_d = 0.12;
        let s1 = sortino_ratio(0.05, 0.02, sigma_d); // excess = 0.03
        let s2 = sortino_ratio(0.10, 0.02, sigma_d); // excess = 0.08
        assert!(s1 < s2);
        assert!(sortino_ratio_mono_excess(0.03, 0.08, sigma_d));
    }

    /// Sortino >= Sharpe when sigma_d < sigma (conceptual sanity check)
    #[test]
    fn test_sortino_ge_sharpe_when_downside_smaller() {
        let mu = 0.12;
        let rf = 0.03;
        let sigma_total = 0.20;
        let sigma_d = 0.12; // downside deviation typically <= total vol
        let sharpe = (mu - rf) / sigma_total;
        let sortino = sortino_ratio(mu, rf, sigma_d);
        assert!(sortino >= sharpe);
    }
}
