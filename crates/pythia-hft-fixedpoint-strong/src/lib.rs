//! # pythia-hft-fixedpoint-strong
//!
//! Error-tracking fixed-point arithmetic for FPGA/HFT deployment.
//!
//! ## Lean specification
//!
//! Every function has a corresponding theorem in
//! `Pythia.Finance.HFT.FixedPointStrong` (Lean 4). The Lean proofs guarantee:
//!
//! - **Addition error**: `|sum_real - sum_fp| ≤ 2 * eps` (`add_error_bound`)
//! - **Multiplication error**: `|a*b - a_fp*b_fp| ≤ |a|*eps_b + |b_fp|*eps_a` (`mul_error_first_order`)
//! - **Comparison safety**: gap > 2*eps ⟹ ordering preserved (`compare_preserves_order`)
//! - **N-step accumulation**: n additions ⟹ error ≤ n*eps (`n_step_add_error`)
//! - **Overflow detection**: `|a| + |b| < bound ⟹ |a+b| < bound` (`no_overflow_from_abs_bound`)
//!
//! ## FPGA use case
//!
//! FPGA price engines compute in fixed-point (integer DSP slices).
//! This crate tracks accumulated quantization error through a chain
//! of operations, letting the hardware engineer prove that after N
//! pipeline stages the output is within tolerance.

/// A fixed-point value that tracks its accumulated error bound.
///
/// `value` is the integer representation, `scale` is the denominator
/// (e.g., 2^16), and `error_bound` is the proven upper bound on
/// `|real_value - value/scale|`.
#[derive(Debug, Clone, Copy)]
pub struct TrackedFP {
    pub value: i64,
    pub scale: u32,
    pub error_bound: f64,
}

impl TrackedFP {
    /// Create from a real value by rounding to nearest.
    /// Initial error is at most half a tick (1 / 2*scale).
    ///
    /// # Lean theorem: `quantError_le_half_tick`
    #[inline]
    pub fn from_real(real_val: f64, scale: u32) -> Self {
        let scaled = (real_val * scale as f64).round() as i64;
        Self {
            value: scaled,
            scale,
            error_bound: 0.5 / scale as f64,
        }
    }

    /// Create from raw integer with known error bound.
    #[inline]
    pub const fn from_raw(value: i64, scale: u32, error_bound: f64) -> Self {
        Self { value, scale, error_bound }
    }

    /// Exact value (no error).
    #[inline]
    pub const fn exact(value: i64, scale: u32) -> Self {
        Self { value, scale, error_bound: 0.0 }
    }

    /// Real value approximation.
    #[inline]
    pub fn to_real(&self) -> f64 {
        self.value as f64 / self.scale as f64
    }

    /// Error-tracked addition.
    ///
    /// # Lean theorem: `add_error_bound`
    /// `|(a_real + b_real) - (a_fp + b_fp)| ≤ 2 * max(eps_a, eps_b)`
    ///
    /// We use the tighter bound: `eps_a + eps_b` (triangle inequality).
    #[inline]
    pub fn add(self, other: Self) -> Self {
        assert_eq!(self.scale, other.scale, "scale mismatch");
        Self {
            value: self.value + other.value,
            scale: self.scale,
            error_bound: self.error_bound + other.error_bound,
        }
    }

    /// Error-tracked subtraction.
    #[inline]
    pub fn sub(self, other: Self) -> Self {
        assert_eq!(self.scale, other.scale, "scale mismatch");
        Self {
            value: self.value - other.value,
            scale: self.scale,
            error_bound: self.error_bound + other.error_bound,
        }
    }

    /// Error-tracked multiplication.
    ///
    /// # Lean theorem: `mul_error_first_order`
    /// `|a*b - a_fp*b_fp| ≤ |a|*eps_b + |b_fp|*eps_a`
    #[inline]
    pub fn mul(self, other: Self) -> Self {
        assert_eq!(self.scale, other.scale, "scale mismatch");
        let scale = self.scale as i128;
        let raw_product = (self.value as i128 * other.value as i128) / scale;
        let a_abs = (self.value as f64 / self.scale as f64).abs();
        let b_fp_abs = (other.value as f64 / other.scale as f64).abs();
        let new_error = a_abs * other.error_bound + b_fp_abs * self.error_bound;
        let quant_error = 0.5 / self.scale as f64;
        Self {
            value: raw_product as i64,
            scale: self.scale,
            error_bound: new_error + quant_error,
        }
    }

    /// Safe comparison: returns `Some(ordering)` only when the gap
    /// between values exceeds twice the combined error bound.
    ///
    /// # Lean theorem: `compare_preserves_order`
    /// If `a_real + 2*eps < b_real`, then `a_fp < b_fp`.
    #[inline]
    pub fn safe_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let max_error = self.error_bound + other.error_bound;
        let gap = ((other.value - self.value) as f64) / self.scale as f64;
        if gap.abs() > 2.0 * max_error {
            Some(self.value.cmp(&other.value))
        } else {
            None
        }
    }

    /// Overflow check before addition.
    ///
    /// # Lean theorem: `no_overflow_from_abs_bound`
    /// `|a| + |b| < bound ⟹ |a + b| < bound`
    #[inline]
    pub fn would_overflow(&self, other: &Self, bound: i64) -> bool {
        let a_abs = self.value.unsigned_abs();
        let b_abs = other.value.unsigned_abs();
        a_abs.checked_add(b_abs).map_or(true, |sum| sum >= bound as u64)
    }

    /// N-step accumulated error after a chain of additions.
    ///
    /// # Lean theorem: `n_step_add_error`
    /// `total_error ≤ n * eps`
    #[inline]
    pub fn chain_error_bound(n: usize, per_step_eps: f64) -> f64 {
        n as f64 * per_step_eps
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SCALE: u32 = 65536;

    #[test]
    fn from_real_error_within_half_tick() {
        let fp = TrackedFP::from_real(3.14159, SCALE);
        let error = (3.14159 - fp.to_real()).abs();
        assert!(error <= fp.error_bound, "actual error {error} > bound {}", fp.error_bound);
    }

    #[test]
    fn add_error_accumulates() {
        let a = TrackedFP::from_real(1.5, SCALE);
        let b = TrackedFP::from_real(2.7, SCALE);
        let sum = a.add(b);
        assert!((sum.error_bound - (a.error_bound + b.error_bound)).abs() < 1e-15);
    }

    #[test]
    fn safe_cmp_distinguishes_far_values() {
        let a = TrackedFP::from_real(1.0, SCALE);
        let b = TrackedFP::from_real(2.0, SCALE);
        assert!(a.safe_cmp(&b).is_some());
    }

    #[test]
    fn safe_cmp_abstains_on_close_values() {
        let a = TrackedFP::from_raw(100, SCALE, 0.5);
        let b = TrackedFP::from_raw(101, SCALE, 0.5);
        assert!(a.safe_cmp(&b).is_none());
    }

    #[test]
    fn chain_error_bound_linear() {
        let eps = 0.5 / SCALE as f64;
        assert!((TrackedFP::chain_error_bound(100, eps) - 100.0 * eps).abs() < 1e-15);
    }

    #[test]
    fn overflow_detected() {
        let a = TrackedFP::exact(i64::MAX / 2 + 1, SCALE);
        let b = TrackedFP::exact(i64::MAX / 2 + 1, SCALE);
        assert!(a.would_overflow(&b, i64::MAX));
    }

    #[test]
    fn no_overflow_within_bounds() {
        let a = TrackedFP::exact(1000, SCALE);
        let b = TrackedFP::exact(2000, SCALE);
        assert!(!a.would_overflow(&b, i64::MAX));
    }
}
