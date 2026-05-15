//! Property tests for portfolio optimality, mirroring Lean spec `Pythia.Finance.PortfolioOptimality`.

use proptest::prelude::*;
use pythia_finance_portfolio::MeanVarianceOptimizer;

/// Strategy: generate a valid optimizer where cov < (v1+v2)/2 (strictly convex).
fn arb_convex_opt() -> impl Strategy<Value = MeanVarianceOptimizer> {
    (0.01f64..1.0, 0.01f64..1.0, -0.5f64..0.5, -0.2f64..0.3, -0.2f64..0.3).prop_filter_map(
        "need strict convexity",
        |(v1, v2, rho, r1, r2)| {
            // cov = rho * sqrt(v1*v2), with |rho| < 1 this guarantees cov < (v1+v2)/2
            let cov = rho * (v1 * v2).sqrt();
            let o = MeanVarianceOptimizer::new(v1, v2, cov, r1, r2);
            if o.is_strictly_convex() { Some(o) } else { None }
        },
    )
}

proptest! {
    /// Lean: `optimalWeight_foc` — FOC = 0 at the optimal weight.
    #[test]
    fn prop_foc_zero_at_optimal(opt in arb_convex_opt()) {
        let w = opt.optimal_weight().unwrap();
        let foc = opt.foc(w);
        prop_assert!(foc.abs() < 1e-9, "FOC not zero: foc={}", foc);
    }

    /// Lean: `mvObjective_second_deriv_pos` — second derivative is positive for convex problems.
    #[test]
    fn prop_second_deriv_pos(opt in arb_convex_opt()) {
        prop_assert!(opt.second_deriv() > 0.0);
    }

    /// Lean: `diversification_benefit` — equal-weight variance <= average individual variances.
    #[test]
    fn prop_diversification(opt in arb_convex_opt()) {
        prop_assert!(opt.diversification_benefit(), "diversification violated for v1={}, v2={}, cov={}", opt.v1, opt.v2, opt.cov);
    }

    /// Lean: `portfolioReturn_affine` — return is affine: check at 0, 1, and convex combination.
    #[test]
    fn prop_return_affine(
        opt in arb_convex_opt(),
        w1 in 0.0f64..1.0,
        w2 in 0.0f64..1.0,
        alpha in 0.0f64..1.0,
    ) {
        let w_mix = alpha * w1 + (1.0 - alpha) * w2;
        let r_mix = opt.portfolio_return(w_mix);
        let r_affine = alpha * opt.portfolio_return(w1) + (1.0 - alpha) * opt.portfolio_return(w2);
        prop_assert!((r_mix - r_affine).abs() < 1e-10, "affinity: |{} - {}|", r_mix, r_affine);
    }
}
