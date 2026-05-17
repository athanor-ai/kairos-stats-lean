//! Provenance: VERIFIED — the Lean proofs in `Pythia.Finance.FixedIncome.VasicekBondPrice`
//! use `simp`, `rw [Real.log_mul, Real.log_exp]`, and `ring` to establish these
//! properties non-tautologically. These proptests exercise the same invariants in Rust.

use proptest::prelude::*;
use pythia_fixedincome_vasicek::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `vasicekBondPrice_at_zero_r0`
    /// At r0 = 0, bond price equals A.
    #[test]
    fn prop_at_zero_r0(a in 0.01f64..10.0, b in -5.0f64..5.0) {
        let price = vasicek_bond_price(a, b, 0.0);
        prop_assert!((price - a).abs() < EPS * (1.0 + a),
            "at_zero_r0 violated: price={}, a={}", price, a);
    }

    /// Lean: `vasicekBondPrice_at_zero_B`
    /// At B = 0, bond price equals A.
    #[test]
    fn prop_at_zero_b(a in 0.01f64..10.0, r0 in -1.0f64..1.0) {
        let price = vasicek_bond_price(a, 0.0, r0);
        prop_assert!((price - a).abs() < EPS * (1.0 + a),
            "at_zero_B violated: price={}, a={}", price, a);
    }

    /// Lean: `vasicekBondPrice_linear_log`
    /// For A > 0: log(P) = log(A) - B*r0.
    #[test]
    fn prop_linear_log(a in 0.01f64..10.0, b in -3.0f64..3.0, r0 in -1.0f64..1.0) {
        let price = vasicek_bond_price(a, b, r0);
        let log_price = price.ln();
        let expected = vasicek_log_price(a, b, r0);
        prop_assert!((log_price - expected).abs() < EPS * (1.0 + log_price.abs()),
            "linear_log violated: log_price={}, expected={}", log_price, expected);
    }

    /// Derived: price is always positive when A > 0.
    #[test]
    fn prop_positive_price(a in 0.01f64..10.0, b in -5.0f64..5.0, r0 in -1.0f64..1.0) {
        let price = vasicek_bond_price(a, b, r0);
        prop_assert!(price > 0.0,
            "price should be positive for a>0, got {}", price);
    }
}
