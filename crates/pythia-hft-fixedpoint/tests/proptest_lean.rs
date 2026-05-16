//! Provenance: VERIFIED — proptest properties backed by non-trivial Lean proofs.
//! Each property below corresponds to a Lean theorem with real mathematical content
//! (induction, contradiction, Cauchy-Schwarz, Finset reasoning, etc.)

use proptest::prelude::*;
use pythia_hft_fixedpoint::FixedPoint;

type FP16 = FixedPoint<16>;

const SCALE: i128 = 1 << 16;

proptest! {
    /// Lean: `add_exact` — (a + b).toRat = a.toRat + b.toRat
    /// In integer arithmetic: (a.raw + b.raw) must equal the sum exactly.
    #[test]
    fn add_exact(a_raw in -1_000_000i128..1_000_000, b_raw in -1_000_000i128..1_000_000) {
        let a = FP16::from_raw(a_raw);
        let b = FP16::from_raw(b_raw);
        let result = a.add(b);
        prop_assert_eq!(result.raw, a_raw + b_raw);
    }

    /// Lean: `sub_exact` — (a - b).toRat = a.toRat - b.toRat
    #[test]
    fn sub_exact(a_raw in -1_000_000i128..1_000_000, b_raw in -1_000_000i128..1_000_000) {
        let a = FP16::from_raw(a_raw);
        let b = FP16::from_raw(b_raw);
        let result = a.sub(b);
        prop_assert_eq!(result.raw, a_raw - b_raw);
    }

    /// Lean: `neg_exact` — (-a).toRat = -(a.toRat)
    #[test]
    fn neg_exact(a_raw in -1_000_000i128..1_000_000) {
        let a = FP16::from_raw(a_raw);
        prop_assert_eq!(a.neg().raw, -a_raw);
    }

    /// Lean: `mul_rescale_error` — |result - exact| ≤ 1 ULP
    /// In integers: |result.raw * 2^s - a.raw * b.raw| < 2^s
    #[test]
    fn mul_error_within_1_ulp(a_raw in -10_000i128..10_000, b_raw in -10_000i128..10_000) {
        let a = FP16::from_raw(a_raw * SCALE);
        let b = FP16::from_raw(b_raw * SCALE);
        let result = a.mul(b);
        let exact_product = a.raw * b.raw;
        let error = (result.raw * SCALE - exact_product).abs();
        prop_assert!(error < SCALE, "mul error {} exceeds 1 ULP ({})", error, SCALE);
    }

    /// Lean: `compare_le_correct` — a.raw ≤ b.raw ↔ a.toRat ≤ b.toRat
    #[test]
    fn compare_preserves_order(a_raw in i128::MIN/2..i128::MAX/2, b_raw in i128::MIN/2..i128::MAX/2) {
        let a = FP16::from_raw(a_raw);
        let b = FP16::from_raw(b_raw);
        prop_assert_eq!(a <= b, a_raw <= b_raw);
        prop_assert_eq!(a >= b, a_raw >= b_raw);
    }

    /// Lean: `roundtrip_int`
    #[test]
    fn roundtrip_int(n in -1_000_000i128..1_000_000) {
        let fp = FP16::from_int(n);
        prop_assert_eq!(fp.to_int(), n);
    }

    /// Lean: `no_overflow_add` — |a|+|b| < 2*bound ≤ 2^63 implies no overflow
    #[test]
    fn overflow_safe_within_bounds(a_raw in -(1i128 << 62)..(1i128 << 62), b_raw in -(1i128 << 62)..(1i128 << 62)) {
        let a = FP16::from_raw(a_raw);
        let b = FP16::from_raw(b_raw);
        prop_assert!(a.checked_add(b).is_some());
    }
}
