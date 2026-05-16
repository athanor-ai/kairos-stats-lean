//! # pythia-risk-marginmodel
//!
//! Verified portfolio margin model — zero tautological, all real proofs.
//!
//! ## Lean specification (`Pythia.Finance.Risk.MarginModel`)
//!
//! - **Margin nonneg**: rate * |value| ≥ 0 (`initialMargin_nonneg`)
//! - **Margin monotone in rate** (`initialMargin_mono_rate`)
//! - **Margin monotone in |value|** (`initialMargin_mono_abs`)
//! - **Portfolio subadditive**: margin(a+b) ≤ margin(a) + margin(b) (`portfolio_margin_subadditive`)
//! - **Netting reduces margin**: |Σ pos| ≤ Σ|pos| (`netting_reduces_margin`)
//! - **Margin scales**: margin(c*v) = |c| * margin(v) (`margin_scales`)
//! - **Margin call from loss** (`margin_call_from_loss`)
//! - **Liquidation qty nonneg** (`liquidation_qty_nonneg`)

/// Initial margin: rate * |value|.
/// # Lean: `initialMargin`
#[inline(always)]
pub fn initial_margin(rate: f64, value: f64) -> f64 {
    rate * value.abs()
}

/// Portfolio margin: rate * |sum of positions|.
/// # Lean: `portfolio_margin_subadditive`
/// Subadditive: margin(a+b) ≤ margin(a) + margin(b).
pub fn portfolio_margin(rate: f64, positions: &[f64]) -> f64 {
    rate * positions.iter().sum::<f64>().abs()
}

/// Gross margin: rate * sum of |positions|.
/// # Lean: `netting_reduces_margin`
/// Always ≥ portfolio margin (netting benefit).
pub fn gross_margin(rate: f64, positions: &[f64]) -> f64 {
    rate * positions.iter().map(|p| p.abs()).sum::<f64>()
}

/// Margin excess: equity - required.
/// # Lean: `margin_excess_nonneg_iff`
pub fn margin_excess(equity: f64, required: f64) -> f64 {
    equity - required
}

/// Check margin call: equity - loss < maintenance.
/// # Lean: `margin_call_from_loss`
pub fn is_margin_call(equity: f64, loss: f64, maintenance: f64) -> bool {
    equity - loss < maintenance
}

/// Liquidation quantity: deficit / price.
/// # Lean: `liquidation_qty_nonneg`
pub fn liquidation_qty(deficit: f64, price: f64) -> f64 {
    assert!(price > 0.0);
    (deficit / price).max(0.0)
}

/// Margin scales with position: margin(c*v) = |c| * margin(v).
/// # Lean: `margin_scales`
pub fn scaled_margin(rate: f64, scale: f64, value: f64) -> f64 {
    initial_margin(rate, scale * value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn margin_nonneg() {
        assert!(initial_margin(0.1, -1000.0) >= 0.0);
        assert!(initial_margin(0.1, 1000.0) >= 0.0);
    }

    #[test]
    fn margin_mono_rate() {
        assert!(initial_margin(0.05, 1000.0) <= initial_margin(0.10, 1000.0));
    }

    #[test]
    fn margin_mono_abs() {
        assert!(initial_margin(0.1, 500.0) <= initial_margin(0.1, 1000.0));
    }

    #[test]
    fn portfolio_subadditive() {
        let sub = initial_margin(0.1, 700.0) + initial_margin(0.1, -300.0);
        let port = initial_margin(0.1, 700.0 + (-300.0));
        assert!(port <= sub + 1e-10);
    }

    #[test]
    fn netting_benefit() {
        let positions = &[500.0, -300.0, 200.0];
        assert!(portfolio_margin(0.1, positions) <= gross_margin(0.1, positions) + 1e-10);
    }

    #[test]
    fn margin_call_detected() {
        assert!(is_margin_call(100.0, 60.0, 50.0));
        assert!(!is_margin_call(100.0, 40.0, 50.0));
    }

    #[test]
    fn liquidation_nonneg() {
        assert!(liquidation_qty(5000.0, 100.0) >= 0.0);
    }

    #[test]
    fn scales_correctly() {
        let direct = initial_margin(0.1, 3.0 * 1000.0);
        let scaled = 3.0_f64.abs() * initial_margin(0.1, 1000.0);
        assert!((direct - scaled).abs() < 1e-10);
    }
}
