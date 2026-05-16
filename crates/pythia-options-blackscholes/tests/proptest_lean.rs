//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_options_blackscholes::*;

proptest! {
    /// Lean: `bsCall_zero_time` — as T -> 0+, call approaches max(S-K, 0).
    /// We test with very small T to approximate the zero-time limit.
    #[test]
    fn zero_time_limit(
        s in 50.0f64..200.0,
        k in 50.0f64..200.0,
        r in 0.0f64..0.1,
        sigma in 0.01f64..0.5
    ) {
        let t = 1e-8;
        let price = bs_call_full(s, k, t, r, sigma);
        let intrinsic = (s - k).max(0.0);
        prop_assert!(
            (price - intrinsic).abs() < 0.01,
            "at T~0, call ({}) should equal intrinsic ({})", price, intrinsic
        );
    }

    /// Lean: `bsCall_linear_S` — shifting S by dS shifts call by approximately dS * Phi(d1).
    /// Delta property: d(call)/dS = Phi(d1).
    #[test]
    fn linearity_in_s(
        s in 80.0f64..150.0,
        k in 80.0f64..150.0,
        t in 0.1f64..2.0,
        r in 0.0f64..0.1,
        sigma in 0.05f64..0.5
    ) {
        let ds = 0.01; // small shift
        let price1 = bs_call_full(s, k, t, r, sigma);
        let price2 = bs_call_full(s + ds, k, t, r, sigma);
        let d1 = compute_d1(s, k, t, r, sigma);
        let delta = phi(d1);
        let expected_shift = ds * delta;
        let actual_shift = price2 - price1;
        // Allow relative tolerance because the approximation is first-order
        prop_assert!(
            (actual_shift - expected_shift).abs() < 0.001,
            "shift ({}) should be close to ds*Phi(d1) ({})", actual_shift, expected_shift
        );
    }

    /// Lean: `bsCall_strict_pos_under_unit_Phi` — deep ITM calls always positive
    #[test]
    fn deep_itm_positivity(
        k in 50.0f64..150.0,
        t in 0.1f64..3.0,
        r in 0.0f64..0.1,
        sigma in 0.05f64..0.5
    ) {
        // S = 3*K ensures deep ITM
        let s = 3.0 * k;
        prop_assert!(check_deep_itm_positive(s, k, t, r, sigma));
    }

    /// Lean: `bsCall_zero_rate` — at r=0, call = S*Phi(d1) - K*Phi(d2) (no discount).
    #[test]
    fn zero_rate_no_discount(
        s in 50.0f64..200.0,
        k in 50.0f64..200.0,
        t in 0.1f64..2.0,
        sigma in 0.05f64..0.5
    ) {
        let r = 0.0;
        let price = bs_call_full(s, k, t, r, sigma);
        // At r=0, exp(-rT) = 1, so call = S*Phi(d1) - K*Phi(d2)
        let d1 = compute_d1(s, k, t, r, sigma);
        let d2 = d1 - sigma * t.sqrt();
        let expected = s * phi(d1) - k * phi(d2);
        prop_assert!(
            (price - expected).abs() < 1e-10,
            "at r=0, call ({}) should equal S*Phi(d1)-K*Phi(d2) ({})", price, expected
        );
    }
}
