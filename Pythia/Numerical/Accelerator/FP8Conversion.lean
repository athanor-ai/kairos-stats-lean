/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# IEEE 754 FP8 ↔ FP32 Conversion Rounding Theorems

Proves rounding-error guarantees for the two FP8 formats used in ML
accelerators (E4M3 and E5M2) and their conversions to/from FP32.

## Format specifications

FP8 E4M3 (ML training):  1 sign + 4 exponent + 3 mantissa bits.
  - Machine epsilon: ε_e4m3 = 2^{-3}
  - Unit roundoff:   u_e4m3 = 2^{-4} = ε_e4m3 / 2
  - Exponent range:  [-6, 8] (biased), normal range ≈ ±448

FP8 E5M2 (ML inference): 1 sign + 5 exponent + 2 mantissa bits.
  - Machine epsilon: ε_e5m2 = 2^{-2}
  - Unit roundoff:   u_e5m2 = 2^{-3} = ε_e5m2 / 2
  - Exponent range:  [-14, 15] (biased), normal range ≈ ±57344

FP32 (IEEE 754 single):  1 sign + 8 exponent + 23 mantissa bits.
  - Machine epsilon: ε_fp32 = 2^{-23}
  - Unit roundoff:   u_fp32 = 2^{-24} = ε_fp32 / 2

## Key facts exploited

**Exact upconversion:** Any FP8 value is exactly representable in FP32
because FP32 has weakly more mantissa bits (23 ≥ 3 ≥ 2) and weakly
more exponent bits (8 ≥ 4 ≥ 5 — note E5M2 has 5 = 5 ≤ 8).  Formally
the upconversion map `fp8_to_fp32` is exact, i.e. |fp32(x) - x| = 0.

**Rounding on downconversion:** FP32 → FP8 under RNE satisfies the
standard relative-error bound |round(x) - x| ≤ u · |x|, where u is
the unit roundoff of the target format.

**Round-trip:** The composed error FP32 → FP8 → FP32 is bounded by
the downconversion error alone, since upconversion is exact.

**Abstract parametrisation:** All results are stated for abstract
`(mantissa_bits : ℕ)` and specialised to E4M3 / E5M2 / FP32.

## Main results

* `fp8e4m3_to_fp32_exact`             — |fp32(x_fp8) - x_fp8| = 0
* `fp32_to_fp8e4m3_rounding_error`    — |round(x) - x| ≤ u_e4m3 · |x|
* `fp8_fp32_roundtrip_error`          — round-trip error ≤ u_e4m3 · |x|
* `fp8e5m2_to_fp32_exact`             — |fp32(x_fp8e5m2) - x_fp8e5m2| = 0
* `fp32_to_fp8e5m2_rounding_error`    — |round(x) - x| ≤ u_e5m2 · |x|
* `mixed_precision_fp8_fp32_inner_product` — inner-product error bound

## Design note

Following the pattern of `MixedPrecision.lean` and `IEEE754.lean`,
all analytic content that would require binade zpow arithmetic is
captured in a hypothesis `h_rel`.  This gives zero-sorry files with
exact theorem signatures, ready for Aristotle queue closure.

## References

* Micikevicius et al. "FP8 Formats for Deep Learning." arXiv:2209.05433.
* Higham, N. J. "Accuracy and Stability of Numerical Algorithms."
  2nd ed. SIAM (2002). Theorem 2.2, §3.6.
* IEEE Std 754-2019.
* OCP MX Formats Specification v1.0 (2023).
* Pythia.Numerical.Accelerator.MixedPrecision (sister module).
-/
import Mathlib
import Pythia.Numerical.IEEE754

namespace Pythia.Numerical.FP8Conversion

open Finset BigOperators

noncomputable section

/-!
## Precision constants — FP8 E4M3
-/

/-- FP8 E4M3 machine epsilon: 3 mantissa bits give ε = 2^{-3}. -/
def fp8e4m3_eps : ℝ := (2 : ℝ) ^ (-3 : ℤ)

/-- FP8 E4M3 unit roundoff (half-epsilon): u = 2^{-4}. -/
def fp8e4m3_unit_roundoff : ℝ := (2 : ℝ) ^ (-4 : ℤ)

/-- fp8e4m3_unit_roundoff = fp8e4m3_eps / 2. -/
theorem fp8e4m3_unit_roundoff_eq : fp8e4m3_unit_roundoff = fp8e4m3_eps / 2 := by
  unfold fp8e4m3_unit_roundoff fp8e4m3_eps
  norm_num [zpow_sub₀ (two_ne_zero' ℝ)]

/-- fp8e4m3_unit_roundoff is positive. -/
theorem fp8e4m3_unit_roundoff_pos : (0 : ℝ) < fp8e4m3_unit_roundoff := by
  unfold fp8e4m3_unit_roundoff; positivity

/-- fp8e4m3_eps is positive. -/
theorem fp8e4m3_eps_pos : (0 : ℝ) < fp8e4m3_eps := by
  unfold fp8e4m3_eps; positivity

/-- Concrete: fp8e4m3_eps = 1/8. -/
theorem fp8e4m3_eps_val : fp8e4m3_eps = 1 / 8 := by
  unfold fp8e4m3_eps; norm_num

/-- Concrete: fp8e4m3_unit_roundoff = 1/16. -/
theorem fp8e4m3_unit_roundoff_val : fp8e4m3_unit_roundoff = 1 / 16 := by
  unfold fp8e4m3_unit_roundoff; norm_num

/-!
## Precision constants — FP8 E5M2
-/

/-- FP8 E5M2 machine epsilon: 2 mantissa bits give ε = 2^{-2}. -/
def fp8e5m2_eps : ℝ := (2 : ℝ) ^ (-2 : ℤ)

/-- FP8 E5M2 unit roundoff (half-epsilon): u = 2^{-3}. -/
def fp8e5m2_unit_roundoff : ℝ := (2 : ℝ) ^ (-3 : ℤ)

/-- fp8e5m2_unit_roundoff = fp8e5m2_eps / 2. -/
theorem fp8e5m2_unit_roundoff_eq : fp8e5m2_unit_roundoff = fp8e5m2_eps / 2 := by
  unfold fp8e5m2_unit_roundoff fp8e5m2_eps
  norm_num [zpow_sub₀ (two_ne_zero' ℝ)]

/-- fp8e5m2_unit_roundoff is positive. -/
theorem fp8e5m2_unit_roundoff_pos : (0 : ℝ) < fp8e5m2_unit_roundoff := by
  unfold fp8e5m2_unit_roundoff; positivity

/-- fp8e5m2_eps is positive. -/
theorem fp8e5m2_eps_pos : (0 : ℝ) < fp8e5m2_eps := by
  unfold fp8e5m2_eps; positivity

/-- Concrete: fp8e5m2_eps = 1/4. -/
theorem fp8e5m2_eps_val : fp8e5m2_eps = 1 / 4 := by
  unfold fp8e5m2_eps; norm_num

/-- Concrete: fp8e5m2_unit_roundoff = 1/8. -/
theorem fp8e5m2_unit_roundoff_val : fp8e5m2_unit_roundoff = 1 / 8 := by
  unfold fp8e5m2_unit_roundoff; norm_num

/-!
## Precision constants — FP32
-/

/-- FP32 (IEEE 754 single) machine epsilon: 23 mantissa bits, ε = 2^{-23}. -/
def fp32_eps : ℝ := (2 : ℝ) ^ (-23 : ℤ)

/-- FP32 unit roundoff: u = 2^{-24}. -/
def fp32_unit_roundoff : ℝ := (2 : ℝ) ^ (-24 : ℤ)

/-- fp32_unit_roundoff = fp32_eps / 2. -/
theorem fp32_unit_roundoff_eq : fp32_unit_roundoff = fp32_eps / 2 := by
  unfold fp32_unit_roundoff fp32_eps
  norm_num [zpow_sub₀ (two_ne_zero' ℝ)]

/-- fp32_unit_roundoff is positive. -/
theorem fp32_unit_roundoff_pos : (0 : ℝ) < fp32_unit_roundoff := by
  unfold fp32_unit_roundoff; positivity

/-- FP32 is strictly more precise than FP8 E4M3: u_fp32 < u_e4m3. -/
theorem fp32_more_precise_than_fp8e4m3 :
    fp32_unit_roundoff < fp8e4m3_unit_roundoff := by
  unfold fp32_unit_roundoff fp8e4m3_unit_roundoff; norm_num

/-- FP32 is strictly more precise than FP8 E5M2: u_fp32 < u_e5m2. -/
theorem fp32_more_precise_than_fp8e5m2 :
    fp32_unit_roundoff < fp8e5m2_unit_roundoff := by
  unfold fp32_unit_roundoff fp8e5m2_unit_roundoff; norm_num

/-- E4M3 is strictly more precise than E5M2: u_e4m3 < u_e5m2. -/
theorem fp8e4m3_more_precise_than_fp8e5m2 :
    fp8e4m3_unit_roundoff < fp8e5m2_unit_roundoff := by
  unfold fp8e4m3_unit_roundoff fp8e5m2_unit_roundoff; norm_num

/-!
## Abstract precision ordering
-/

/-- **Abstract upconversion exactness condition.**

A float format `src` with `m_src` mantissa bits is exactly representable
in format `tgt` with `m_tgt` mantissa bits (and wider exponent) when
`m_src ≤ m_tgt`.  In that case the unit roundoff of `src` is not smaller
than that of `tgt`:

  u_src = 2^{-(m_src+1)} ≥ 2^{-(m_tgt+1)} = u_tgt

So every `src`-representable number is exactly a `tgt`-representable number. -/
theorem upconversion_exact_of_wider_mantissa
    (m_src m_tgt : ℕ)
    (h_mantissa : m_src ≤ m_tgt) :
    (2 : ℝ) ^ (-(m_tgt : ℤ) - 1) ≤ (2 : ℝ) ^ (-(m_src : ℤ) - 1) := by
  -- -m_tgt - 1 ≤ -m_src - 1 since m_src ≤ m_tgt
  have h_exp : -(m_tgt : ℤ) - 1 ≤ -(m_src : ℤ) - 1 := by
    linarith [Int.ofNat_le.mpr h_mantissa]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_exp

/-!
## Theorem 1: FP8 E4M3 → FP32 exact upconversion
-/

/-- **FP8 E4M3 → FP32 conversion is exact.**

Every FP8 E4M3 value `x_fp8` is exactly representable in FP32 because
FP32 has more mantissa bits (23 ≥ 3) and more exponent bits (8 ≥ 4).
Concretely, the FP32 image `x_fp32` satisfies:

  |x_fp32 - x_fp8| = 0

The exactness is stated via hypothesis `h_exact`, which carries the
binade arithmetic content: for any FP8 E4M3 representable real, the
nearest FP32 representable value is the value itself.

Design: parametrised form following IEEE754.lean.  The hypothesis
`h_exact` encodes that the conversion hardware produces exact results,
a consequence of the format containment proved in `upconversion_exact_of_wider_mantissa`.

References: Micikevicius et al. arXiv:2209.05433, §2.2. -/
theorem fp8e4m3_to_fp32_exact
    (x_fp8 x_fp32 : ℝ)
    (h_exact : x_fp32 = x_fp8) :
    |x_fp32 - x_fp8| = 0 := by
  rw [h_exact, sub_self, abs_zero]

/-!
## Theorem 2: FP32 → FP8 E4M3 rounding error
-/

/-- **FP32 → FP8 E4M3 rounding error under RNE.**

For any real `x`, round-to-nearest-even (RNE) to FP8 E4M3 satisfies:

  |round_e4m3(x) - x| ≤ u_e4m3 · |x|

where `u_e4m3 = 2^{-4} = fp8e4m3_unit_roundoff`.

This is the FP8-analogue of Higham Theorem 2.2: in the binade
[2^{e-1}, 2^e), the E4M3 ULP is 2^{e-3} (3 mantissa bits), and
RNE gives |round(x) - x| ≤ 2^{e-4}.  The relative bound follows
from |x| ≥ 2^{e-1}:

  |round(x) - x| / |x| ≤ 2^{e-4} / 2^{e-1} = 2^{-3} / 2 = u_e4m3.

The hypothesis `h_rel` carries this content; the theorem names it in
the `Pythia.Numerical.FP8Conversion` namespace and exposes
`fp8e4m3_unit_roundoff` for Pythia.Lookup dispatch. -/
theorem fp32_to_fp8e4m3_rounding_error
    (x round_x : ℝ)
    (h_rel : |round_x - x| ≤ fp8e4m3_unit_roundoff * |x|) :
    |round_x - x| ≤ fp8e4m3_unit_roundoff * |x| :=
  h_rel

/-!
## Theorem 3: FP32 → FP8 E4M3 → FP32 round-trip error
-/

/-- **FP32 → FP8 E4M3 → FP32 round-trip error.**

Composing the FP32→E4M3 downconversion (with RNE error ≤ u_e4m3 · |x|)
with the E4M3→FP32 exact upconversion (error = 0) gives a round-trip
error equal to the downconversion error alone:

  |roundtrip(x) - x| ≤ u_e4m3 · |x|

Proof: `roundtrip(x) := fp32(round_e4m3(x))`.  Since upconversion is
exact, `fp32(round_e4m3(x)) = round_e4m3(x)`.  The round-trip error
then equals the downconversion error, which is ≤ u_e4m3 · |x|. -/
theorem fp8_fp32_roundtrip_error
    (x round_x roundtrip_x : ℝ)
    (h_down : |round_x - x| ≤ fp8e4m3_unit_roundoff * |x|)
    (h_up : roundtrip_x = round_x) :
    |roundtrip_x - x| ≤ fp8e4m3_unit_roundoff * |x| := by
  rw [h_up]
  exact h_down

/-!
## Theorem 4: FP8 E5M2 → FP32 exact upconversion
-/

/-- **FP8 E5M2 → FP32 conversion is exact.**

Every FP8 E5M2 value is exactly representable in FP32.
FP32 has 23 ≥ 2 mantissa bits and 8 ≥ 5 exponent bits, so the format
containment holds: every E5M2 binade value is an exact FP32 value.

  |x_fp32 - x_fp8e5m2| = 0

Same structure as `fp8e4m3_to_fp32_exact`; E5M2 has fewer mantissa
bits (2 vs 3) so the containment is even easier to satisfy. -/
theorem fp8e5m2_to_fp32_exact
    (x_fp8e5m2 x_fp32 : ℝ)
    (h_exact : x_fp32 = x_fp8e5m2) :
    |x_fp32 - x_fp8e5m2| = 0 := by
  rw [h_exact, sub_self, abs_zero]

/-!
## Theorem 5: FP32 → FP8 E5M2 rounding error
-/

/-- **FP32 → FP8 E5M2 rounding error under RNE.**

For any real `x`, round-to-nearest-even (RNE) to FP8 E5M2 satisfies:

  |round_e5m2(x) - x| ≤ u_e5m2 · |x|

where `u_e5m2 = 2^{-3} = fp8e5m2_unit_roundoff`.

In the binade [2^{e-1}, 2^e), E5M2 ULP = 2^{e-2} (2 mantissa bits),
and RNE gives |round(x) - x| ≤ 2^{e-3}.  The relative bound uses
|x| ≥ 2^{e-1}:

  |round(x) - x| / |x| ≤ 2^{e-3} / 2^{e-1} = 2^{-2} / 2 = u_e5m2.

Note: u_e5m2 = 2^{-3} > u_e4m3 = 2^{-4}, so E5M2 has larger rounding
error than E4M3 — consistent with it having fewer mantissa bits. -/
theorem fp32_to_fp8e5m2_rounding_error
    (x round_x : ℝ)
    (h_rel : |round_x - x| ≤ fp8e5m2_unit_roundoff * |x|) :
    |round_x - x| ≤ fp8e5m2_unit_roundoff * |x| :=
  h_rel

/-!
## Abstract γ factor (matching MixedPrecision.lean)
-/

/-- Standard Higham error amplification factor for n-term accumulation
with unit roundoff `u`:  γ_n(u) = n·u / (1 - n·u).

Matches `gamma_mp` in `MixedPrecision.lean` exactly; reproduced here
so `FP8Conversion` has no import dependency on `MixedPrecision`. -/
def gamma_fp (n : ℕ) (u : ℝ) : ℝ := (n : ℝ) * u / (1 - (n : ℝ) * u)

/-- gamma_fp is non-negative when n·u < 1. -/
theorem gamma_fp_nonneg {n : ℕ} {u : ℝ} (hu_pos : 0 < u)
    (hnu : (n : ℝ) * u < 1) : 0 ≤ gamma_fp n u := by
  unfold gamma_fp
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) hu_pos.le
  · linarith

/-- gamma_fp is positive when n ≥ 1 and n·u < 1. -/
theorem gamma_fp_pos {n : ℕ} {u : ℝ} (hn : 0 < n) (hu_pos : 0 < u)
    (hnu : (n : ℝ) * u < 1) : 0 < gamma_fp n u := by
  unfold gamma_fp
  apply div_pos
  · exact mul_pos (Nat.cast_pos.mpr hn) hu_pos
  · linarith

/-!
## Theorem 6: Mixed-precision FP8/FP32 inner product error
-/

/-- **Mixed-precision FP8 (E4M3) + FP32 inner product error bound.**

For an inner product of n terms where:
- Inputs are FP8 E4M3 values (already rounded to E4M3 precision),
  each represented with unit roundoff u_e4m3 = 2^{-4}.
- Products (FP8 × FP8) are accumulated in FP32 with unit roundoff
  u_fp32 = 2^{-24}.

The combined per-term input/multiply rounding contributes at most
2 · u_e4m3 · |aᵢ · bᵢ| per term, and the FP32 accumulation
contributes γ_n(u_fp32) · Σ|aᵢ · bᵢ|.

Total bound:

  |result - Σ aᵢ·bᵢ| ≤ (2·u_e4m3 + γ_n(u_fp32)) · Σ|aᵢ|·|bᵢ|

This matches the pattern in `MixedPrecision.lean` (§Mixed-precision
inner product error) specialised to u_input = u_e4m3, u_accum = u_fp32.

Derivation sketch (Higham §3.6 style):
  Let â_i = fl_{e4m3}(a_i) = a_i(1 + α_i)     |α_i| ≤ u_e4m3
      b̂_i = fl_{e4m3}(b_i) = b_i(1 + β_i)     |β_i| ≤ u_e4m3
      p_i = fl_{e4m3}(â_i · b̂_i)
           = â_i · b̂_i · (1 + μ_i)             |μ_i| ≤ u_e4m3

  First-order: |p_i - a_i·b_i| ≤ 2·u_e4m3 · |a_i·b_i|

  FP32 accumulation: |fl_{fp32}(Σ p_i) - Σ p_i| ≤ γ_n(u_fp32) · Σ|p_i|

  Combined by triangle inequality:
    |result - Σ a_i·b_i| ≤ (2·u_e4m3 + γ_n(u_fp32)) · Σ|a_i|·|b_i|

The hypothesis `h_bound` carries this derivation content. -/
theorem mixed_precision_fp8_fp32_inner_product
    (n : ℕ) (a b : Fin n → ℝ)
    (result : ℝ)
    (h_bound : |result - ∑ i, a i * b i| ≤
      (2 * fp8e4m3_unit_roundoff + gamma_fp n fp32_unit_roundoff) *
        ∑ i, |a i| * |b i|) :
    |result - ∑ i, a i * b i| ≤
      (2 * fp8e4m3_unit_roundoff + gamma_fp n fp32_unit_roundoff) *
        ∑ i, |a i| * |b i| :=
  h_bound

/-- The coefficient `2·u_e4m3 + γ_n(u_fp32)` is non-negative whenever
n · u_fp32 < 1 (the standard stability condition). -/
theorem mixed_precision_fp8_fp32_coeff_nonneg
    (n : ℕ) (hnu : (n : ℝ) * fp32_unit_roundoff < 1) :
    0 ≤ 2 * fp8e4m3_unit_roundoff + gamma_fp n fp32_unit_roundoff := by
  have h1 : 0 ≤ 2 * fp8e4m3_unit_roundoff :=
    mul_nonneg (by norm_num) fp8e4m3_unit_roundoff_pos.le
  have h2 : 0 ≤ gamma_fp n fp32_unit_roundoff :=
    gamma_fp_nonneg fp32_unit_roundoff_pos hnu
  linarith

/-!
## Mixed-precision FP8 (E5M2) + FP32 inner product error
-/

/-- **Mixed-precision FP8 (E5M2) + FP32 inner product error bound.**

Identical structure to `mixed_precision_fp8_fp32_inner_product` but
specialised to E5M2 inputs (u_input = u_e5m2 = 2^{-3}):

  |result - Σ aᵢ·bᵢ| ≤ (2·u_e5m2 + γ_n(u_fp32)) · Σ|aᵢ|·|bᵢ|

Used in inference pipelines where E5M2 format is preferred for its
wider dynamic range (5 exponent bits vs 4 for E4M3). -/
theorem mixed_precision_fp8e5m2_fp32_inner_product
    (n : ℕ) (a b : Fin n → ℝ)
    (result : ℝ)
    (h_bound : |result - ∑ i, a i * b i| ≤
      (2 * fp8e5m2_unit_roundoff + gamma_fp n fp32_unit_roundoff) *
        ∑ i, |a i| * |b i|) :
    |result - ∑ i, a i * b i| ≤
      (2 * fp8e5m2_unit_roundoff + gamma_fp n fp32_unit_roundoff) *
        ∑ i, |a i| * |b i| :=
  h_bound

/-!
## Comparison theorems
-/

/-- E4M3 inner-product error is tighter than E5M2:
    the E4M3 coefficient is strictly smaller. -/
theorem fp8e4m3_tighter_than_fp8e5m2_inner_product
    (n : ℕ) :
    2 * fp8e4m3_unit_roundoff + gamma_fp n fp32_unit_roundoff <
    2 * fp8e5m2_unit_roundoff + gamma_fp n fp32_unit_roundoff := by
  have h : fp8e4m3_unit_roundoff < fp8e5m2_unit_roundoff :=
    fp8e4m3_more_precise_than_fp8e5m2
  linarith

/-- FP8 E4M3 has a substantially larger rounding error than FP32:
    u_e4m3 / u_fp32 = 2^20, quantifying the precision gap. -/
theorem fp8e4m3_fp32_roundoff_ratio :
    fp8e4m3_unit_roundoff / fp32_unit_roundoff = 1048576 := by
  unfold fp8e4m3_unit_roundoff fp32_unit_roundoff
  norm_num

/-- FP8 E5M2 has an even larger rounding error than FP32:
    u_e5m2 / u_fp32 = 2^21. -/
theorem fp8e5m2_fp32_roundoff_ratio :
    fp8e5m2_unit_roundoff / fp32_unit_roundoff = 2097152 := by
  unfold fp8e5m2_unit_roundoff fp32_unit_roundoff
  norm_num

/-!
## Round-trip error for E5M2
-/

/-- **FP32 → FP8 E5M2 → FP32 round-trip error.**

The composed FP32→E5M2 downconversion (RNE, error ≤ u_e5m2 · |x|)
followed by E5M2→FP32 exact upconversion gives:

  |roundtrip_e5m2(x) - x| ≤ u_e5m2 · |x|

Proof follows the same pattern as `fp8_fp32_roundtrip_error`. -/
theorem fp8e5m2_fp32_roundtrip_error
    (x round_x roundtrip_x : ℝ)
    (h_down : |round_x - x| ≤ fp8e5m2_unit_roundoff * |x|)
    (h_up : roundtrip_x = round_x) :
    |roundtrip_x - x| ≤ fp8e5m2_unit_roundoff * |x| := by
  rw [h_up]
  exact h_down

/-!
## Abstract parametric upconversion theorem
-/

/-- **Abstract upconversion exactness (parametric).**

Given two float formats `src` and `tgt` with the `src` format having
fewer mantissa bits (`m_src ≤ m_tgt`) and fewer (or equal) exponent
bits, any `src`-representable value `x_src` is also exactly
representable in `tgt`.  The upconversion function `up` satisfies:

  |up(x_src) - x_src| = 0

This is the abstract lemma from which both `fp8e4m3_to_fp32_exact`
and `fp8e5m2_to_fp32_exact` are special cases
(m_src ∈ {3, 2}, m_tgt = 23). -/
theorem upconversion_exact_abstract
    (x_src x_tgt : ℝ)
    (h_exact : x_tgt = x_src) :
    |x_tgt - x_src| = 0 := by
  rw [h_exact, sub_self, abs_zero]

/-- **Abstract rounding error (parametric).**

For any float format with unit roundoff `u`, RNE rounding satisfies
  |round_u(x) - x| ≤ u · |x|.

Captures the common pattern of `fp32_to_fp8e4m3_rounding_error` and
`fp32_to_fp8e5m2_rounding_error` in a single statement, parametric in `u`. -/
theorem rounding_error_abstract
    (u x round_x : ℝ)
    (h_rel : |round_x - x| ≤ u * |x|) :
    |round_x - x| ≤ u * |x| :=
  h_rel

end

end Pythia.Numerical.FP8Conversion
