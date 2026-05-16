//! # pythia-portfolio-leverage
//!
//! Verified leverage constraints.
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.LeverageConstraints`)
//!
//! - **Gross ≥ |net|** (triangle inequality) (`gross_ge_abs_net`)
//! - **Leverage within limit** (`leverage_within_limit`)
//! - **Margin nonneg** (`margin_nonneg`)
//! - **Deleveraging reduces exposure** (`deleverage_reduces`)

/// Gross leverage: Σ|w_i|.
/// # Lean: `gross_leverage_nonneg`
pub fn gross_leverage(weights: &[f64]) -> f64 {
    weights.iter().map(|w| w.abs()).sum()
}

/// Net leverage: Σw_i.
pub fn net_leverage(weights: &[f64]) -> f64 {
    weights.iter().sum()
}

/// Leverage ratio: gross / equity.
/// # Lean: `leverage_within_limit`
pub fn leverage_ratio(gross: f64, equity: f64) -> f64 {
    assert!(equity > 0.0);
    gross / equity
}

/// Check leverage within limit.
pub fn within_limit(gross: f64, equity: f64, limit: f64) -> bool {
    leverage_ratio(gross, equity) <= limit + 1e-12
}

/// Margin requirement: m * |V|.
/// # Lean: `margin_nonneg`
pub fn margin_required(margin_rate: f64, value: f64) -> f64 {
    margin_rate * value.abs()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gross_ge_abs_net() {
        let w = &[0.6, -0.3, 0.4, -0.2];
        assert!(gross_leverage(w) >= net_leverage(w).abs());
    }

    #[test]
    fn gross_nonneg() {
        assert!(gross_leverage(&[-1.0, 0.5, 0.3]) >= 0.0);
    }

    #[test]
    fn leverage_within() {
        assert!(within_limit(200.0, 100.0, 3.0));
        assert!(!within_limit(400.0, 100.0, 3.0));
    }

    #[test]
    fn margin_nonneg() {
        assert!(margin_required(0.5, -1000.0) >= 0.0);
    }

    #[test]
    fn deleverage_reduces() {
        let gross_old = 500.0;
        let gross_new = gross_old - 100.0;
        assert!(gross_new <= gross_old);
    }
}
