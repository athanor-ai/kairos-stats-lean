use proptest::prelude::*;
use pythia_options_volpnl::*;

proptest! {
    /// Lean: `daily_gamma_pnl_pos` — nonneg when realized ≥ implied
    #[test]
    fn gamma_pnl_nonneg(gamma in 0.0f64..0.1, s_sq in 1000.0f64..100000.0, implied in 0.01f64..0.5, excess in 0.0f64..0.3, dt in 0.001f64..0.01) {
        let realized = implied + excess;
        prop_assert!(daily_gamma_pnl(gamma, s_sq, realized * realized, implied * implied, dt) >= -1e-15);
    }

    /// Lean: `vega_pnl_nonneg` — long vega + vol rise = profit
    #[test]
    fn vega_nonneg(vega in 0.0f64..5000.0, dv in 0.0f64..0.1) {
        prop_assert!(vega_pnl(vega, dv) >= -1e-15);
    }

    /// Lean: `vol_arb_breakeven`
    #[test]
    fn breakeven(implied in 0.1f64..0.5, excess in 0.01f64..0.3) {
        prop_assert!(vol_arb_profit(implied + excess, implied) > 0.0);
    }

    /// Lean: `cumulative_vol_pnl_nonneg`
    #[test]
    fn cumulative_nonneg(d1 in 0.0f64..10.0, d2 in 0.0f64..10.0, d3 in 0.0f64..10.0) {
        prop_assert!(cumulative_pnl(&[d1, d2, d3]) >= 0.0);
    }
}
