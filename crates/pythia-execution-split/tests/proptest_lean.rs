use proptest::prelude::*;
use pythia_execution_split::*;

proptest! {
    /// Lean: `equal_split_optimal` — equal split achieves the lower bound
    #[test]
    fn equal_achieves_bound(total in 1.0f64..10000.0, n in 1usize..20) {
        let children = equal_split(total, n);
        let ss = sum_of_squares(&children);
        let bound = impact_lower_bound(total, n);
        prop_assert!((ss - bound).abs() < 1e-4);
    }

    /// Lean: `split_reduces_impact` — any nonneg split has sum_sq ≤ total²
    #[test]
    fn split_reduces(c1 in 0.0f64..500.0, c2 in 0.0f64..500.0) {
        let total = c1 + c2;
        prop_assert!(split_reduces_impact(&[c1, c2], total));
    }

    /// Lean: `equal_split_optimal` — any split ≥ equal split bound
    #[test]
    fn any_above_bound(c1 in 0.0f64..1000.0, c2 in 0.0f64..1000.0, c3 in 0.0f64..1000.0) {
        let total = c1 + c2 + c3;
        let ss = sum_of_squares(&[c1, c2, c3]);
        let bound = impact_lower_bound(total, 3);
        prop_assert!(ss >= bound - 1e-6);
    }

    /// Lean: `hidden_nonneg`
    #[test]
    fn hidden_nonneg(total in 1.0f64..10000.0, frac in 0.0f64..1.0) {
        let display = total * frac;
        prop_assert!(iceberg_hidden(total, display) >= -1e-10);
    }
}
