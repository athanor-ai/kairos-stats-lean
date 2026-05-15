//! # pythia-finance-backtest
//!
//! Backtest validity checks to prevent overfitting.
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.BacktestValidity`)
//!
//! - **Bonferroni correction**: per-test threshold = α/n (`bonferroni_threshold_pos`)
//! - **Multiple testing penalty antitone in n** (`bonferroni_antitone`)
//! - **Deflated Sharpe adjustment nonneg** (`deflation_adjustment_nonneg`)
//! - **Overfit penalty**: IS Sharpe ≥ OOS Sharpe (`overfit_penalty_expected`)

/// Bonferroni-corrected significance threshold.
///
/// # Lean: `bonferroni_threshold_pos`, `bonferroni_antitone`
#[inline(always)]
pub fn bonferroni_threshold(alpha: f64, n_strategies: usize) -> f64 {
    assert!(n_strategies > 0);
    alpha / n_strategies as f64
}

/// Deflated Sharpe ratio: adjusts for multiple testing.
///
/// DSR = observed_sharpe - sqrt(2 * ln(n)) * vol_sharpe
///
/// # Lean: `deflation_adjustment_nonneg`
pub fn deflated_sharpe(observed_sharpe: f64, n_strategies: usize, vol_sharpe: f64) -> f64 {
    let adjustment = (2.0 * (n_strategies as f64).ln()).sqrt() * vol_sharpe;
    observed_sharpe - adjustment
}

/// Minimum track record length: (z_alpha / sharpe)^2.
///
/// # Lean: `min_track_record`
pub fn min_track_record(z_alpha: f64, target_sharpe: f64) -> f64 {
    assert!(target_sharpe > 0.0);
    (z_alpha / target_sharpe).powi(2)
}

/// Overfit penalty: in-sample Sharpe minus out-of-sample Sharpe.
///
/// # Lean: `overfit_penalty_expected`
#[inline(always)]
pub fn overfit_penalty(sharpe_is: f64, sharpe_oos: f64) -> f64 {
    sharpe_is - sharpe_oos
}

/// Full backtest validation report.
#[derive(Debug)]
pub struct BacktestReport {
    pub observed_sharpe: f64,
    pub deflated_sharpe: f64,
    pub bonferroni_threshold: f64,
    pub min_observations: f64,
    pub is_significant: bool,
}

pub fn validate_backtest(
    observed_sharpe: f64,
    n_strategies: usize,
    vol_sharpe: f64,
    alpha: f64,
    z_alpha: f64,
) -> BacktestReport {
    let dsr = deflated_sharpe(observed_sharpe, n_strategies, vol_sharpe);
    let threshold = bonferroni_threshold(alpha, n_strategies);
    let min_obs = min_track_record(z_alpha, observed_sharpe.max(0.01));
    BacktestReport {
        observed_sharpe,
        deflated_sharpe: dsr,
        bonferroni_threshold: threshold,
        min_observations: min_obs,
        is_significant: dsr > 0.0 && observed_sharpe > 0.0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bonferroni_decreases_with_n() {
        let t1 = bonferroni_threshold(0.05, 1);
        let t10 = bonferroni_threshold(0.05, 10);
        let t100 = bonferroni_threshold(0.05, 100);
        assert!(t1 > t10);
        assert!(t10 > t100);
    }

    #[test]
    fn deflated_sharpe_below_observed() {
        let dsr = deflated_sharpe(1.5, 100, 0.3);
        assert!(dsr < 1.5);
    }

    #[test]
    fn min_track_record_increases_with_precision() {
        let loose = min_track_record(1.96, 1.0);
        let tight = min_track_record(1.96, 0.5);
        assert!(tight > loose);
    }

    #[test]
    fn overfit_penalty_nonneg_when_is_gt_oos() {
        assert!(overfit_penalty(1.5, 0.8) >= 0.0);
    }

    #[test]
    fn full_validation() {
        let report = validate_backtest(1.2, 50, 0.3, 0.05, 1.96);
        assert!(report.bonferroni_threshold < 0.05);
        assert!(report.deflated_sharpe < report.observed_sharpe);
    }
}
