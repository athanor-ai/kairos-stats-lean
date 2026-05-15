use proptest::prelude::*;
use pythia_risk_drawdown::*;

proptest! {
    /// Lean: `drawdown_nonneg` -- drawdown >= 0 when value <= peak
    #[test]
    fn drawdown_nonneg(peak in 0.0f64..1000.0, gap in 0.0f64..1000.0) {
        let value = peak - gap.min(peak); // ensures value <= peak
        prop_assert!(drawdown(peak, value) >= -1e-15);
    }

    /// Lean: `drawdown_zero_at_peak` -- drawdown(x, x) = 0 for all x
    #[test]
    fn drawdown_zero_at_peak(x in -1000.0f64..1000.0) {
        prop_assert!((drawdown(x, x)).abs() < 1e-15);
    }

    /// Lean: `drawdown_mono_value` -- antitone in value (v1 <= v2 => dd(peak,v2) <= dd(peak,v1))
    #[test]
    fn drawdown_antitone_value(
        peak in 0.0f64..1000.0,
        v1 in 0.0f64..1000.0,
        delta in 0.0f64..500.0,
    ) {
        let v2 = v1 + delta;
        prop_assert!(drawdown(peak, v2) <= drawdown(peak, v1) + 1e-12);
    }

    /// Lean: `drawdownRatio_le_one` and `drawdownRatio_nonneg` -- ratio in [0,1]
    #[test]
    fn drawdown_ratio_in_unit(peak in 1.0f64..1000.0, frac in 0.0f64..1.0) {
        let value = peak * frac; // 0 <= value <= peak
        let ratio = drawdown_ratio(peak, value);
        prop_assert!(ratio >= -1e-12, "ratio {} < 0", ratio);
        prop_assert!(ratio <= 1.0 + 1e-12, "ratio {} > 1", ratio);
    }
}
