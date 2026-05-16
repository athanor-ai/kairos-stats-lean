//! # pythia-fixedincome-vasicek
//!
//! Verified Vasicek zero-coupon bond price (affine term-structure closed form).
//!
//! ## Lean specification (`Pythia.Finance.FixedIncome.VasicekBondPrice`)
//!
//! - **At-zero-r0**: `vasicekBondPrice_at_zero_r0` — P(A, B, 0) = A
//! - **At-zero-B**: `vasicekBondPrice_at_zero_B` — P(A, 0, r0) = A
//! - **Linear-log**: `vasicekBondPrice_linear_log` — log P = log A - B*r0 (for A > 0)

/// Vasicek zero-coupon bond price: A * exp(-B * r0).
///
/// # Lean: `vasicekBondPrice`
#[inline(always)]
pub fn vasicek_bond_price(a: f64, b: f64, r0: f64) -> f64 {
    a * (-b * r0).exp()
}

/// B(T) coefficient in the Vasicek model: (1 - exp(-a*T)) / a.
///
/// For the full model parameterisation (not used in the algebraic kernel
/// but useful for integration tests).
#[inline(always)]
pub fn vasicek_b(a: f64, t: f64) -> f64 {
    if a.abs() < 1e-15 {
        t // limit as a -> 0
    } else {
        (1.0 - (-a * t).exp()) / a
    }
}

/// Log of bond price: log(A) - B * r0.
///
/// # Lean: `vasicekBondPrice_linear_log`
#[inline(always)]
pub fn vasicek_log_price(a: f64, b: f64, r0: f64) -> f64 {
    a.ln() - b * r0
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Lean: `vasicekBondPrice_at_zero_r0` — P(A, B, 0) = A
    #[test]
    fn test_at_zero_r0() {
        let a = 0.95;
        let b = 1.5;
        let price = vasicek_bond_price(a, b, 0.0);
        assert!((price - a).abs() < EPS);
    }

    /// Lean: `vasicekBondPrice_at_zero_B` — P(A, 0, r0) = A
    #[test]
    fn test_at_zero_b() {
        let a = 0.92;
        let r0 = 0.05;
        let price = vasicek_bond_price(a, 0.0, r0);
        assert!((price - a).abs() < EPS);
    }

    /// Lean: `vasicekBondPrice_linear_log` — log P = log A - B*r0
    #[test]
    fn test_linear_log() {
        let a = 0.98;
        let b = 2.0;
        let r0 = 0.03;
        let price = vasicek_bond_price(a, b, r0);
        let log_price = price.ln();
        let expected = a.ln() - b * r0;
        assert!((log_price - expected).abs() < EPS);
    }

    /// Bond price is positive when A > 0 (exp is always positive)
    #[test]
    fn test_positive_price() {
        let a = 0.90;
        let b = 1.0;
        let r0 = 0.10;
        assert!(vasicek_bond_price(a, b, r0) > 0.0);
    }

    /// B(T) approaches T as a -> 0
    #[test]
    fn test_b_limit() {
        let t = 5.0;
        let b_val = vasicek_b(1e-16, t);
        assert!((b_val - t).abs() < EPS);
    }

    /// Price decreases as r0 increases (for positive B)
    #[test]
    fn test_price_decreasing_in_r0() {
        let a = 0.95;
        let b = 1.5;
        let p1 = vasicek_bond_price(a, b, 0.03);
        let p2 = vasicek_bond_price(a, b, 0.05);
        assert!(p1 > p2);
    }
}
