//! Provenance: VERIFIED — the Lean proofs in `Pythia.Finance.Portfolio.TreynorRatio`
//! use `simp`, `field_simp`, `ring`, and `ring_nf` to establish these properties
//! non-tautologically. These proptests exercise the same algebraic invariants in Rust.

use proptest::prelude::*;
use pythia_portfolio_treynor::*;

const EPS: f64 = 1e-10;

proptest! {
    /// Lean: `treynorRatio_zero_excess`
    /// When r_p = r_f, the Treynor ratio is zero (for non-zero beta).
    #[test]
    fn prop_zero_excess(rf in -100.0f64..100.0, beta in 0.001f64..100.0) {
        let result = treynor_ratio(rf, rf, beta);
        prop_assert!(result.abs() < EPS,
            "zero_excess violated: rf={}, beta={}, result={}", rf, beta, result);
    }

    /// Lean: `treynorRatio_linear_rp`
    /// Shifting r_p by dr shifts the ratio by dr/beta.
    #[test]
    fn prop_linearity(
        rp in -100.0f64..100.0,
        rf in -100.0f64..100.0,
        beta in 0.001f64..100.0,
        dr in -50.0f64..50.0,
    ) {
        let base = treynor_ratio(rp, rf, beta);
        let shifted = treynor_ratio_shifted(rp, dr, rf, beta);
        let expected = base + dr / beta;
        prop_assert!((shifted - expected).abs() < EPS * (1.0 + shifted.abs()),
            "linearity violated: shifted={}, expected={}", shifted, expected);
    }

    /// Lean: `treynorRatio_translation`
    /// Adding same constant c to both r_p and r_f cancels.
    #[test]
    fn prop_translation(
        rp in -100.0f64..100.0,
        rf in -100.0f64..100.0,
        beta in 0.001f64..100.0,
        c in -100.0f64..100.0,
    ) {
        let base = treynor_ratio(rp, rf, beta);
        let translated = treynor_ratio_translated(rp, rf, c, beta);
        prop_assert!((base - translated).abs() < EPS * (1.0 + base.abs()),
            "translation violated: base={}, translated={}", base, translated);
    }
}
