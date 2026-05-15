//! # pythia-hft-signal
//!
//! Verified alpha signal combination with proven output bounds.
//!
//! ## Lean specification (`Pythia.Finance.HFT.SignalCombination`)
//!
//! - **Output bounded**: convex weights + bounded inputs → bounded output (`combinedSignal_bounded`)
//! - **Zero weights → zero signal** (`combinedSignal_zero_weights`)
//! - **Single extraction**: weight-1 on one signal recovers it (`combinedSignal_single`)

/// A weighted signal combiner with proven output bounds.
///
/// Given N component signals each in [-B, B] and non-negative weights
/// summing to 1, the combined signal is guaranteed to be in [-B, B].
#[derive(Debug, Clone)]
pub struct SignalCombiner {
    pub weights: Vec<f64>,
}

impl SignalCombiner {
    /// Create a combiner from weights. Weights must be non-negative and sum to 1.
    pub fn new(weights: Vec<f64>) -> Self {
        debug_assert!(weights.iter().all(|&w| w >= 0.0), "weights must be non-negative");
        debug_assert!((weights.iter().sum::<f64>() - 1.0).abs() < 1e-9, "weights must sum to 1");
        Self { weights }
    }

    /// Equal-weight combiner for n signals.
    pub fn equal(n: usize) -> Self {
        assert!(n > 0);
        Self { weights: vec![1.0 / n as f64; n] }
    }

    /// Number of signals.
    pub fn len(&self) -> usize {
        self.weights.len()
    }

    pub fn is_empty(&self) -> bool {
        self.weights.is_empty()
    }

    /// Combine signals. Returns the weighted sum.
    ///
    /// # Lean theorem: `combinedSignal_bounded`
    /// If each `|signal[i]| ≤ B` and weights are convex, `|result| ≤ B`.
    #[inline]
    pub fn combine(&self, signals: &[f64]) -> f64 {
        assert_eq!(self.weights.len(), signals.len());
        self.weights.iter().zip(signals).map(|(w, s)| w * s).sum()
    }

    /// Combine with proven bound check.
    /// Returns `(combined_value, is_within_bound)`.
    #[inline]
    pub fn combine_bounded(&self, signals: &[f64], bound: f64) -> (f64, bool) {
        let val = self.combine(signals);
        (val, val.abs() <= bound)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_weight_averages() {
        let c = SignalCombiner::equal(3);
        let result = c.combine(&[3.0, 6.0, 9.0]);
        assert!((result - 6.0).abs() < 1e-10);
    }

    #[test]
    fn bounded_output() {
        let c = SignalCombiner::new(vec![0.3, 0.5, 0.2]);
        let result = c.combine(&[1.0, -1.0, 1.0]);
        assert!(result.abs() <= 1.0);
    }

    #[test]
    fn zero_weights_zero_signal() {
        let c = SignalCombiner { weights: vec![0.0, 0.0, 0.0] };
        assert_eq!(c.combine(&[100.0, -50.0, 25.0]), 0.0);
    }

    #[test]
    fn single_extraction() {
        let c = SignalCombiner::new(vec![0.0, 1.0, 0.0]);
        assert_eq!(c.combine(&[10.0, 42.0, 99.0]), 42.0);
    }
}
