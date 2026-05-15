//! # pythia-portfolio-attribution
//!
//! Verified multi-period Brinson performance attribution.
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.PerformanceAttribution`)
//!
//! - **Active return** (`active_return`): portfolio minus benchmark
//! - **BHB decomposition** (`bhb_exact`): allocation + selection + interaction = active
//! - **Geometric linking** (`geometric_link`): (1+r1)(1+r2) - 1 = r1 + r2 + r1*r2
//! - **Geometric exceeds arithmetic** (`geometric_exceeds_arithmetic`): cross-term positive for positive returns
//! - **Residual is difference** (`residual_is_difference`): residual = total - explained
//! - **Currency effect additive** (`currency_effect_additive`): r_total = r_local + r_fx
//! - **Positive alpha** (`positive_alpha`): r_p > r_b implies active > 0

/// Active return: portfolio return minus benchmark return.
/// # Lean: `active_return`
#[inline(always)]
pub fn active_return(r_p: f64, r_b: f64) -> f64 {
    r_p - r_b
}

/// BHB attribution decomposition components.
/// Returns `(allocation, selection, interaction)` given sector weights and returns.
///
/// - allocation = (w_p - w_b) * r_b
/// - selection  = w_b * (r_p - r_b)
/// - interaction = (w_p - w_b) * (r_p - r_b)
///
/// # Lean: `bhb_exact`
#[inline(always)]
pub fn bhb_decompose(w_p: f64, w_b: f64, r_p: f64, r_b: f64) -> (f64, f64, f64) {
    let allocation = (w_p - w_b) * r_b;
    let selection = w_b * (r_p - r_b);
    let interaction = (w_p - w_b) * (r_p - r_b);
    (allocation, selection, interaction)
}

/// Geometric linking of two period returns.
/// Two-period compounded return: (1 + r1) * (1 + r2) - 1.
/// # Lean: `geometric_link`
#[inline(always)]
pub fn geometric_link(r1: f64, r2: f64) -> f64 {
    (1.0 + r1) * (1.0 + r2) - 1.0
}

/// Arithmetic linking (simple sum) of two period returns.
#[inline(always)]
pub fn arithmetic_link(r1: f64, r2: f64) -> f64 {
    r1 + r2
}

/// Attribution residual: total return minus explained return.
/// # Lean: `residual_is_difference`
#[inline(always)]
pub fn residual(total: f64, explained: f64) -> f64 {
    total - explained
}

/// Currency-adjusted total return (first-order approximation).
/// # Lean: `currency_effect_additive`
#[inline(always)]
pub fn currency_adjusted_return(r_local: f64, r_fx: f64) -> f64 {
    r_local + r_fx
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: `active_return`
    #[test]
    fn test_active_return() {
        let ar = active_return(0.08, 0.05);
        assert!((ar - 0.03).abs() < 1e-12);
    }

    /// Lean: `bhb_exact` -- allocation + selection + interaction = active
    #[test]
    fn test_bhb_sums_to_active() {
        let (w_p, w_b, r_p, r_b) = (0.60, 0.50, 0.12, 0.08);
        let (alloc, sel, inter) = bhb_decompose(w_p, w_b, r_p, r_b);
        let active = w_p * r_p - w_b * r_b;
        assert!((alloc + sel + inter - active).abs() < 1e-12);
    }

    /// Lean: `geometric_link` -- identity r1 + r2 + r1*r2
    #[test]
    fn test_geometric_link_identity() {
        let (r1, r2) = (0.05, 0.03);
        let geo = geometric_link(r1, r2);
        let expected = r1 + r2 + r1 * r2;
        assert!((geo - expected).abs() < 1e-12);
    }

    /// Lean: `geometric_exceeds_arithmetic` -- cross term positive
    #[test]
    fn test_geometric_exceeds_arithmetic() {
        let (r1, r2) = (0.05, 0.03);
        assert!(geometric_link(r1, r2) > arithmetic_link(r1, r2));
    }

    /// Lean: `residual_is_difference`
    #[test]
    fn test_residual() {
        let r = residual(0.10, 0.09);
        assert!((r - 0.01).abs() < 1e-12);
    }

    /// Lean: `positive_alpha` -- r_p > r_b implies active > 0
    #[test]
    fn test_positive_alpha() {
        assert!(active_return(0.10, 0.07) > 0.0);
        assert!(active_return(0.05, 0.05) == 0.0);
        assert!(active_return(0.03, 0.07) < 0.0);
    }
}
