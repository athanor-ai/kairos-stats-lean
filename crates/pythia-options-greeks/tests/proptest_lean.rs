use proptest::prelude::*;
use pythia_options_greeks::*;

proptest! {
    /// Lean: `call_delta_bounded` — valid call delta always passes
    #[test]
    fn valid_call_passes(delta in 0.0f64..=1.0, gamma in 0.0f64..1.0, vega in 0.0f64..1.0) {
        let g = Greeks { delta, gamma, vega, theta: -0.01 };
        prop_assert_eq!(g.validate_call(), Validity::Valid);
    }

    /// Lean: `put_delta_bounded` — valid put delta always passes
    #[test]
    fn valid_put_passes(delta in -1.0f64..=0.0, gamma in 0.0f64..1.0, vega in 0.0f64..1.0) {
        let g = Greeks { delta, gamma, vega, theta: -0.01 };
        prop_assert_eq!(g.validate_put(), Validity::Valid);
    }

    /// Lean: `delta_parity` — call_delta - put_delta = 1
    #[test]
    fn delta_parity_holds(call_delta in 0.0f64..1.0) {
        let put_delta = call_delta - 1.0;
        prop_assert!(check_delta_parity(call_delta, put_delta, 1e-10));
    }

    /// Lean: `gamma_parity` — call gamma = put gamma
    #[test]
    fn gamma_parity_holds(gamma in 0.0f64..1.0) {
        prop_assert!(check_gamma_parity(gamma, gamma, 1e-10));
    }

    /// Lean: `greeks_pde_check` — PDE consistency
    #[test]
    fn pde_consistent(
        sigma in 0.01f64..1.0, spot in 10.0f64..500.0,
        gamma in 0.001f64..0.1, rate in 0.001f64..0.1, delta in 0.0f64..1.0
    ) {
        let gamma_term = 0.5 * sigma * sigma * spot * spot * gamma;
        let delta_carry = rate * spot * delta;
        let theta = -gamma_term - delta_carry + rate * 10.0;
        let option_price = 10.0;
        prop_assert!(check_bs_pde(theta, sigma, spot, gamma, rate, delta, option_price, 1e-8));
    }
}
