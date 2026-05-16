use proptest::prelude::*;
use pythia_options_crr::*;

proptest! {
    /// Lean: crrStepPrice_equal_payoffs: when Vu = Vd = V, price = exp(-r*dt)*V
    #[test]
    fn prop_equal_payoffs(
        r in -1.0_f64..1.0,
        dt in 0.01_f64..2.0,
        q in 0.0_f64..1.0,
        v in -100.0_f64..100.0,
    ) {
        let price = crr_step_price(r, dt, q, v, v);
        let expected = (-r * dt).exp() * v;
        prop_assert!((price - expected).abs() < 1e-10,
            "equal_payoffs failed: price={price}, expected={expected}");
    }

    /// Lean: crrStepPrice_zero_rate: at r=0, price = q*Vu + (1-q)*Vd
    #[test]
    fn prop_zero_rate(
        dt in 0.01_f64..5.0,
        q in 0.0_f64..1.0,
        vu in -100.0_f64..100.0,
        vd in -100.0_f64..100.0,
    ) {
        let price = crr_step_price(0.0, dt, q, vu, vd);
        let expected = q * vu + (1.0 - q) * vd;
        prop_assert!((price - expected).abs() < 1e-10,
            "zero_rate failed: price={price}, expected={expected}");
    }

    /// Lean: crrStepPrice_linear_payoff: linearity in payoff pair
    #[test]
    fn prop_linear_payoff(
        r in -0.5_f64..0.5,
        dt in 0.01_f64..2.0,
        q in 0.0_f64..1.0,
        alpha in -10.0_f64..10.0,
        vu in -50.0_f64..50.0,
        vd in -50.0_f64..50.0,
    ) {
        let scaled = crr_step_price(r, dt, q, alpha * vu, alpha * vd);
        let base = alpha * crr_step_price(r, dt, q, vu, vd);
        prop_assert!((scaled - base).abs() < 1e-8,
            "linear_payoff failed: scaled={scaled}, base={base}");
    }

    /// Lean: crrRiskNeutralProb_nonneg + le_one: q in [0,1] under no-arb
    #[test]
    fn prop_risk_neutral_prob_in_unit(
        r in 0.0_f64..0.2,
        dt in 0.01_f64..2.0,
        spread in 0.05_f64..0.5,
    ) {
        let ert = (r * dt).exp();
        let d = ert - spread * 0.5;
        let u = ert + spread * 0.5;
        let q = crr_risk_neutral_prob(r, dt, u, d);
        prop_assert!(q >= -1e-12 && q <= 1.0 + 1e-12,
            "q={q} out of [0,1] for r={r}, dt={dt}, u={u}, d={d}");
    }
}
