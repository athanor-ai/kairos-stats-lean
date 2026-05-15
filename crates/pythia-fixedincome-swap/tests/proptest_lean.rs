use proptest::prelude::*;
use pythia_fixedincome_swap::*;

proptest! {
    /// Lean: `fixed_leg_nonneg`
    #[test]
    fn fixed_nonneg(c in 0.0f64..0.1, d1 in 0.0f64..1.0, d2 in 0.0f64..1.0, d3 in 0.0f64..1.0) {
        prop_assert!(fixed_leg_pv(c, &[d1, d2, d3]) >= -1e-15);
    }

    /// Lean: `floating_leg_bounded`
    #[test]
    fn floating_bounded(d_tn in 0.01f64..1.0) {
        let fl = floating_leg_pv(d_tn);
        prop_assert!(fl >= -1e-12);
        prop_assert!(fl <= 1.0 + 1e-12);
    }

    /// Lean: `par_swap_zero_value` — par rate zeroes NPV
    #[test]
    fn par_zeroes_npv(d_tn in 0.5f64..0.99, annuity in 0.1f64..10.0) {
        let c = par_rate(d_tn, annuity);
        let npv = payer_value(floating_leg_pv(d_tn), c, annuity);
        prop_assert!(npv.abs() < 1e-10);
    }

    /// Lean: `payer_antitone_rate`
    #[test]
    fn payer_antitone(pv_float in 0.0f64..0.5, c1 in 0.01f64..0.05, extra in 0.0f64..0.05, ann in 0.1f64..10.0) {
        prop_assert!(payer_value(pv_float, c1 + extra, ann) <= payer_value(pv_float, c1, ann) + 1e-12);
    }
}
