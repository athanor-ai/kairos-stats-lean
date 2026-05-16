//! # pythia-fixedincome-bond
//!
//! Verified zero-coupon bond price-yield relationship under continuous compounding.
//!
//! ## Lean specification (`Pythia.Finance.FixedIncome.BondPriceYield`)
//!
//! - **Positivity**: `bondPrice FV y T > 0` when `FV > 0`
//! - **Zero maturity**: `bondPrice FV y 0 = FV`
//! - **Antitone in yield**: higher yield -> lower price (FV > 0, T >= 0)
//! - **Monotone in face**: higher face value -> higher price
//! - **Zero yield**: `bondPrice FV 0 T = FV`

/// Zero-coupon bond price: `P = FV * exp(-y * T)`.
///
/// # Lean: `bondPrice`
#[inline(always)]
pub fn bond_price(face_value: f64, yield_rate: f64, maturity: f64) -> f64 {
    face_value * (-yield_rate * maturity).exp()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn price_positive_for_positive_face() {
        let p = bond_price(1000.0, 0.05, 5.0);
        assert!(p > 0.0);
    }

    #[test]
    fn zero_maturity_gives_face_value() {
        let fv = 1000.0;
        let p = bond_price(fv, 0.05, 0.0);
        assert!((p - fv).abs() < 1e-12);
    }

    #[test]
    fn zero_yield_gives_face_value() {
        let fv = 1000.0;
        let p = bond_price(fv, 0.0, 10.0);
        assert!((p - fv).abs() < 1e-12);
    }

    #[test]
    fn antitone_in_yield() {
        let fv = 1000.0;
        let t = 5.0;
        let p_low = bond_price(fv, 0.03, t);
        let p_high = bond_price(fv, 0.08, t);
        assert!(p_high < p_low);
    }

    #[test]
    fn monotone_in_face_value() {
        let y = 0.05;
        let t = 5.0;
        let p1 = bond_price(500.0, y, t);
        let p2 = bond_price(1000.0, y, t);
        assert!(p1 <= p2);
    }

    #[test]
    fn known_value_sanity() {
        // FV=100, y=0.1, T=1 => 100 * exp(-0.1) ~ 90.4837
        let p = bond_price(100.0, 0.1, 1.0);
        assert!((p - 90.48374180359595).abs() < 1e-8);
    }
}
