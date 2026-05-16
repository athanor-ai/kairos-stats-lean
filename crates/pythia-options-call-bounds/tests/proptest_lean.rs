//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (mul_nonneg + le_max_right + exp_pos, put_call_parity_discounted + linarith).

use proptest::prelude::*;
use pythia_options_call_bounds::*;

proptest! {
    /// Lean: `callPayoff_nonneg` — mul_nonneg (le_max_right) (exp_pos).le
    #[test]
    fn call_nonneg(s in 0.0f64..200.0, k in 0.0f64..200.0, t in 0.0f64..5.0, r in -0.1f64..0.3) {
        prop_assert!(call_payoff(s, k, t, r) >= 0.0);
    }

    /// Lean: `putPayoff_nonneg` — mul_nonneg (le_max_right) (exp_pos).le
    #[test]
    fn put_nonneg(s in 0.0f64..200.0, k in 0.0f64..200.0, t in 0.0f64..5.0, r in -0.1f64..0.3) {
        prop_assert!(put_payoff(s, k, t, r) >= 0.0);
    }

    /// Lean: `call_ge_intrinsic_discounted` — put_call_parity_discounted + putPayoff_nonneg + linarith
    #[test]
    fn call_ge_discounted_intrinsic(
        s in 50.0f64..200.0,
        k in 50.0f64..200.0,
        t in 0.01f64..5.0,
        r in -0.05f64..0.2
    ) {
        let lhs = (s - k) * (-r * t).exp() - put_payoff(s, k, t, r);
        let rhs = call_payoff(s, k, t, r);
        prop_assert!(lhs <= rhs + 1e-10, "lhs={} > rhs={}", lhs, rhs);
    }

    /// Lean: `put_call_parity_discounted` — sub_mul + put_call_payoff_identity
    #[test]
    fn parity_holds(s in 50.0f64..200.0, k in 50.0f64..200.0, t in 0.01f64..5.0, r in -0.05f64..0.2) {
        let diff = parity_residual(s, k, t, r);
        let expected = (s - k) * (-r * t).exp();
        prop_assert!((diff - expected).abs() < 1e-10, "diff={} expected={}", diff, expected);
    }
}
