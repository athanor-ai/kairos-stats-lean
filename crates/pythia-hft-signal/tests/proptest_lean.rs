//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_hft_signal::SignalCombiner;

proptest! {
    /// Lean: `combinedSignal_bounded` — convex weights + bounded signals → bounded output
    #[test]
    fn bounded_output(
        w1 in 0.0f64..1.0, w2_frac in 0.0f64..1.0,
        s1 in -10.0f64..10.0, s2 in -10.0f64..10.0, s3 in -10.0f64..10.0
    ) {
        let w2 = (1.0 - w1) * w2_frac;
        let w3 = 1.0 - w1 - w2;
        if w3 >= 0.0 {
            let c = SignalCombiner::new(vec![w1, w2, w3]);
            let result = c.combine(&[s1, s2, s3]);
            prop_assert!(result.abs() <= 10.0 + 1e-10,
                "combined {} exceeds bound 10", result);
        }
    }

    /// Lean: `combinedSignal_single` — unit weight extracts one signal
    #[test]
    fn single_extraction(idx in 0usize..4, vals in prop::array::uniform4(-100.0f64..100.0)) {
        let mut w = vec![0.0; 4];
        w[idx] = 1.0;
        let c = SignalCombiner::new(w);
        let result = c.combine(&vals);
        prop_assert!((result - vals[idx]).abs() < 1e-10);
    }

    /// Lean: `combinedSignal_zero_weights`
    #[test]
    fn zero_weights_zero(s1 in -100.0f64..100.0, s2 in -100.0f64..100.0) {
        let c = SignalCombiner { weights: vec![0.0, 0.0] };
        prop_assert_eq!(c.combine(&[s1, s2]), 0.0);
    }
}
