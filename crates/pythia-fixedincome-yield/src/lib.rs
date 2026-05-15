//! # pythia-fixedincome-yield
//!
//! Yield curve no-arbitrage validation for fixed-income desks.
//!
//! ## Lean specification (`Pythia.Finance.FixedIncome.YieldCurveConstraints`)
//!
//! - **Discount factor in (0,1]** (`discount_factor_bounded`)
//! - **Discount monotone decreasing** (`discount_monotone`)
//! - **Forward rate nonneg from discount ordering** (`discrete_forward_nonneg`)
//! - **Convexity nonneg** (`convexity_nonneg`)
//! - **Convexity benefit**: C/2 * dy² ≥ 0 (`convexity_benefit`)
//! - **Key rate durations sum to total** (`key_rate_sum`)

/// A discount factor curve point.
#[derive(Debug, Clone, Copy)]
pub struct DiscountPoint {
    pub maturity: f64,
    pub discount: f64,
}

/// Validate a discount curve for no-arbitrage.
pub fn validate_curve(points: &[DiscountPoint]) -> CurveValidity {
    for p in points {
        if p.discount <= 0.0 || p.discount > 1.0 + 1e-12 {
            return CurveValidity::Invalid("discount factor outside (0,1]");
        }
    }
    for w in points.windows(2) {
        if w[0].maturity < w[1].maturity && w[0].discount < w[1].discount - 1e-12 {
            return CurveValidity::Invalid("discount factors not monotone decreasing");
        }
    }
    CurveValidity::Valid
}

#[derive(Debug, PartialEq, Eq)]
pub enum CurveValidity {
    Valid,
    Invalid(&'static str),
}

/// Discrete forward rate between two maturities.
///
/// # Lean: `discrete_forward_nonneg`
/// Nonneg when D1 ≥ D2 and dT > 0.
pub fn forward_rate(d1: f64, d2: f64, dt: f64) -> f64 {
    (d1 / d2 - 1.0) / dt
}

/// Duration-convexity price approximation: dP/P ≈ -D*dy + C/2*dy².
///
/// # Lean: `convexity_benefit`
/// The convexity term C/2*dy² is always nonneg.
pub fn price_change_approx(duration: f64, convexity: f64, dy: f64) -> f64 {
    -duration * dy + convexity / 2.0 * dy * dy
}

/// Convexity benefit: the nonneg second-order term.
#[inline(always)]
pub fn convexity_benefit(convexity: f64, dy: f64) -> f64 {
    convexity / 2.0 * dy * dy
}

/// Check key rate durations sum to total.
///
/// # Lean: `key_rate_sum`
pub fn check_key_rate_sum(krds: &[f64], total_duration: f64, tol: f64) -> bool {
    (krds.iter().sum::<f64>() - total_duration).abs() < tol
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_curve() {
        let curve = vec![
            DiscountPoint { maturity: 0.0, discount: 1.0 },
            DiscountPoint { maturity: 1.0, discount: 0.95 },
            DiscountPoint { maturity: 2.0, discount: 0.90 },
        ];
        assert_eq!(validate_curve(&curve), CurveValidity::Valid);
    }

    #[test]
    fn invalid_non_monotone() {
        let curve = vec![
            DiscountPoint { maturity: 0.0, discount: 0.90 },
            DiscountPoint { maturity: 1.0, discount: 0.95 },
        ];
        assert_ne!(validate_curve(&curve), CurveValidity::Valid);
    }

    #[test]
    fn forward_rate_nonneg() {
        let f = forward_rate(0.95, 0.90, 1.0);
        assert!(f >= 0.0);
    }

    #[test]
    fn convexity_benefit_nonneg() {
        assert!(convexity_benefit(50.0, 0.01) >= 0.0);
        assert!(convexity_benefit(50.0, -0.01) >= 0.0);
    }

    #[test]
    fn key_rate_sum() {
        assert!(check_key_rate_sum(&[1.0, 2.0, 3.5], 6.5, 1e-10));
    }
}
