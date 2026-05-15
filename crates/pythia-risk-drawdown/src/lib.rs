//! # pythia-risk-drawdown
//!
//! Verified maximum drawdown algebraic identities.
//!
//! ## Lean specification (`Pythia.Finance.Risk.MaxDrawdown`)
//!
//! - **Drawdown** (`drawdown`): peak - value
//! - **Non-negativity** (`drawdown_nonneg`): 0 <= drawdown when value <= peak
//! - **Zero at peak** (`drawdown_zero_at_peak`): drawdown(peak, peak) = 0
//! - **Antitone in value** (`drawdown_mono_value`): lower value => larger drawdown
//! - **Monotone in peak** (`drawdown_mono_peak`): higher peak => larger drawdown
//! - **Relative drawdown** (`drawdownRatio`): (peak - value) / peak
//! - **Ratio at most 1** (`drawdownRatio_le_one`): ratio in [0,1] under natural conditions
//! - **Ratio non-negative** (`drawdownRatio_nonneg`): ratio >= 0

/// Drawdown: peak - value. The decline from the running maximum.
/// # Lean: `drawdown`
#[inline(always)]
pub fn drawdown(peak: f64, value: f64) -> f64 {
    peak - value
}

/// Relative drawdown: (peak - value) / peak.
/// The decline as a fraction of the peak value.
/// # Lean: `drawdownRatio`
#[inline(always)]
pub fn drawdown_ratio(peak: f64, value: f64) -> f64 {
    drawdown(peak, value) / peak
}

/// Maximum drawdown over a time series of portfolio values.
/// Returns the largest peak-to-trough decline.
pub fn max_drawdown(values: &[f64]) -> f64 {
    if values.is_empty() {
        return 0.0;
    }
    let mut peak = values[0];
    let mut max_dd = 0.0f64;
    for &v in values {
        if v > peak {
            peak = v;
        }
        let dd = drawdown(peak, v);
        if dd > max_dd {
            max_dd = dd;
        }
    }
    max_dd
}

/// Maximum relative drawdown over a time series of portfolio values.
/// Returns the largest peak-to-trough decline as a fraction of the peak.
pub fn max_drawdown_ratio(values: &[f64]) -> f64 {
    if values.is_empty() {
        return 0.0;
    }
    let mut peak = values[0];
    let mut max_ddr = 0.0f64;
    for &v in values {
        if v > peak {
            peak = v;
        }
        if peak > 0.0 {
            let ddr = drawdown_ratio(peak, v);
            if ddr > max_ddr {
                max_ddr = ddr;
            }
        }
    }
    max_ddr
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: `drawdown_nonneg`
    #[test]
    fn test_drawdown_nonneg() {
        assert!(drawdown(100.0, 90.0) >= 0.0);
        assert!(drawdown(100.0, 100.0) >= 0.0);
    }

    /// Lean: `drawdown_zero_at_peak`
    #[test]
    fn test_drawdown_zero_at_peak() {
        assert_eq!(drawdown(100.0, 100.0), 0.0);
        assert_eq!(drawdown(42.5, 42.5), 0.0);
    }

    /// Lean: `drawdown_mono_value` -- lower value => larger drawdown
    #[test]
    fn test_drawdown_antitone_in_value() {
        let peak = 100.0;
        assert!(drawdown(peak, 80.0) >= drawdown(peak, 90.0));
    }

    /// Lean: `drawdown_mono_peak` -- higher peak => larger drawdown
    #[test]
    fn test_drawdown_monotone_in_peak() {
        let value = 80.0;
        assert!(drawdown(110.0, value) >= drawdown(100.0, value));
    }

    /// Lean: `drawdownRatio_le_one` and `drawdownRatio_nonneg`
    #[test]
    fn test_drawdown_ratio_bounds() {
        let ratio = drawdown_ratio(100.0, 60.0);
        assert!(ratio >= 0.0);
        assert!(ratio <= 1.0);
        assert!((ratio - 0.4).abs() < 1e-12);
    }

    /// max_drawdown on a concrete series
    #[test]
    fn test_max_drawdown_series() {
        let values = vec![100.0, 110.0, 105.0, 90.0, 95.0, 120.0, 100.0];
        // peak 110 -> trough 90 = dd 20; peak 120 -> trough 100 = dd 20
        let mdd = max_drawdown(&values);
        assert!((mdd - 20.0).abs() < 1e-12);
    }
}
