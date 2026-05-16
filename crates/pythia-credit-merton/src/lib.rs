//! Merton Structural Credit Model
//!
//! Implements the algebraic kernel from:
//! Pythia/Finance/Credit/MertonCredit.lean
//!
//! DD = (log(V/D) + (mu - sigma^2/2)*T) / (sigma * sqrt(T))
//! Equity at maturity = max(V - D, 0)

/// Distance to default in the Merton model.
///   DD = (log_VD + drift_adj * T) / (sigma * sqrt_T)
pub fn distance_to_default(log_vd: f64, drift_adj: f64, t: f64, sigma: f64, sqrt_t: f64) -> f64 {
    (log_vd + drift_adj * t) / (sigma * sqrt_t)
}

/// Equity value at maturity: max(V - D, 0) (European call payoff).
pub fn equity_at_maturity(v: f64, d: f64) -> f64 {
    (v - d).max(0.0)
}

/// Full distance-to-default from raw inputs (convenience).
///   DD = (ln(V/D) + (mu - sigma^2/2)*T) / (sigma * sqrt(T))
pub fn distance_to_default_full(v: f64, d: f64, mu: f64, sigma: f64, t: f64) -> f64 {
    let log_vd = (v / d).ln();
    let drift_adj = mu - sigma * sigma / 2.0;
    let sqrt_t = t.sqrt();
    distance_to_default(log_vd, drift_adj, t, sigma, sqrt_t)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: distanceToDefault_pos: DD > 0 when log(V/D) > 0, drift >= 0, vol > 0
    #[test]
    fn test_dd_positive() {
        let log_vd = 0.2; // V > D
        let drift_adj = 0.03;
        let t = 1.0;
        let sigma = 0.25;
        let sqrt_t = 1.0;
        let dd = distance_to_default(log_vd, drift_adj, t, sigma, sqrt_t);
        assert!(dd > 0.0);
    }

    /// Lean: distanceToDefault_mono_logVD: higher log(V/D) => higher DD
    #[test]
    fn test_dd_mono_log_vd() {
        let drift_adj = 0.02;
        let t = 1.0;
        let sigma = 0.3;
        let sqrt_t = 1.0;
        let dd1 = distance_to_default(0.1, drift_adj, t, sigma, sqrt_t);
        let dd2 = distance_to_default(0.3, drift_adj, t, sigma, sqrt_t);
        assert!(dd1 <= dd2);
    }

    /// Lean: equityAtMaturity_nonneg: equity >= 0 always (limited liability)
    #[test]
    fn test_equity_nonneg() {
        assert!(equity_at_maturity(80.0, 100.0) >= 0.0);
        assert!(equity_at_maturity(100.0, 100.0) >= 0.0);
        assert!(equity_at_maturity(120.0, 100.0) >= 0.0);
    }

    /// Lean: equityAtMaturity_solvent: when V >= D, equity = V - D
    #[test]
    fn test_equity_solvent() {
        let v = 150.0;
        let d = 100.0;
        let equity = equity_at_maturity(v, d);
        assert!((equity - (v - d)).abs() < 1e-12);
    }

    /// Lean: equityAtMaturity_insolvent: when V <= D, equity = 0
    #[test]
    fn test_equity_insolvent() {
        let v = 80.0;
        let d = 100.0;
        let equity = equity_at_maturity(v, d);
        assert!((equity).abs() < 1e-12);
    }

    /// Full DD computation: known values
    #[test]
    fn test_dd_full_computation() {
        let v = 150.0;
        let d = 100.0;
        let mu = 0.08;
        let sigma = 0.25;
        let t = 1.0;
        let dd = distance_to_default_full(v, d, mu, sigma, t);
        // DD = (ln(150/100) + (0.08 - 0.0625)*1) / (0.25 * 1)
        //    = (0.4055 + 0.0175) / 0.25 = 1.692
        assert!(dd > 1.5 && dd < 2.0);
    }
}
