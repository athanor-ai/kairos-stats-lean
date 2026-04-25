/-
Kairos.Stats.EquivalenceBreak — formal statement of the
equivalence-breaking theorem (Theorem 5 of the NeurIPS paper).

Ramdas–Ruf 2022 established that the self-normalized and betting
confidence sequences are equivalent in continuous arithmetic under
the exponential martingale transform `W_t = exp(M_t - sigma² t / 2)`.
At finite precision `s < ∞`, additive quantization of `M_t` does not
correspond to multiplicative quantization of `W_t`, and the two
families produce different stopping decisions.

## STATUS: STATEMENT IS FALSE AS WRITTEN

The statement `equivalence_break_at_finite_precision` below is **false**
as formalized. A concrete counterexample is:

  b = 2, s = 1, sigma = 2, alpha = exp(-1.55) ≈ 0.2125

At these parameters, the two quantized decision thresholds
`C_a(t) = ⌈T1(t) * 2^s⌉ / 2^s` and `C_b(t) = D(t) + ⌈T2 * 2^s⌉ / 2^s`
coincide for ALL `t ∈ {1, 2, 3, 4}` (= {1, ..., 2^b}). Since the acceptance
sets `{m : quantizeReal s m ≥ T1(t)}` and `{m : quantizeReal s (m - D(t)) ≥ T2}`
are both half-lines with the same left endpoint, the two `decide` calls
agree for every `m_tstar` and every valid `tstar`.

### Verification of counterexample

With `sigma = 2`, `L = log(1/alpha) = 1.55`, `s = 1`:
- `t = 1`: `T1(1)*2 = 4*sqrt(3.1) ≈ 7.043`, `⌈7.043⌉ = 8`, `C_b*2 = 4+4 = 8`. Match.
- `t = 2`: `T1(2)*2 = 8*sqrt(2.243) ≈ 11.982`, `⌈11.982⌉ = 12`, `C_b*2 = 8+4 = 12`. Match.
- `t = 3`: `T1(3)*2 = 4*sqrt(15.893) ≈ 15.946`, `⌈15.946⌉ = 16`, `C_b*2 = 12+4 = 16`. Match.
- `t = 4`: `T1(4)*2 ≈ 11.314*sqrt(2.936) ≈ 19.386`, `⌈19.386⌉ = 20`, `C_b*2 = 16+4 = 20`. Match.

### Root cause

The continuous-arithmetic Ramdas–Ruf equivalence CAN be preserved at
finite precision when the quantization grid aligns with both decision
boundaries simultaneously. This alignment is possible for a measure-zero
set of `(sigma, alpha)` pairs (at fixed `b, s`), but the theorem claims
it never happens.

### Possible fixes

The theorem could potentially be rescued by:
1. **Weakening the conclusion**: assert only that the two rules produce
   different *sets of stopping times* in expectation (i.e., not pointwise
   disagreement, but distributional disagreement).
2. **Restricting parameters**: add a "genericity" hypothesis excluding
   the measure-zero set where alignment occurs (e.g., require
   `sigma^2 * 2^(s-1) ∉ ℤ`, which handles the easy case).
3. **Allowing larger `tstar`**: replace `tstar ≤ 2^b` with `tstar ∈ ℕ`
   (unbounded horizon), though this changes the theorem's meaning.
4. **Changing the quantization model**: if quantization is applied to
   the *boundary* (not the process), the alignment issue may not arise.
-/

import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.Quantization
import Kairos.Stats.SubGaussianMG

namespace Kairos.Stats

open MeasureTheory

/-! ## Helper lemmas for quantizeReal -/

/-- Half-line characterization of quantizeReal threshold comparison:
`quantizeReal s m ≥ c ↔ m ≥ ⌈c * 2^s⌉ / 2^s`. -/
lemma quantizeReal_ge_iff (s : ℕ) (m c : ℝ) :
    quantizeReal s m ≥ c ↔ m ≥ (⌈c * (2 : ℝ) ^ s⌉ : ℤ) / (2 : ℝ) ^ s := by
  constructor <;> intro h;
  · rw [ ge_iff_le, div_le_iff₀ ] at * <;> norm_num;
    unfold quantizeReal at h;
    rw [ le_div_iff₀ ( by positivity ) ] at h;
    exact le_trans ( Int.cast_le.mpr ( Int.ceil_le.mpr h ) ) ( Int.floor_le _ );
  · refine' le_trans _ ( div_le_div_of_nonneg_right ( Int.cast_le.mpr ( Int.le_floor.mpr ( _ ) ) ) ( by positivity ) );
    rw [ le_div_iff₀ ( by positivity ) ];
    exacts [ Int.le_ceil _, by rwa [ ge_iff_le, div_le_iff₀ ( by positivity ) ] at h ]

/-- If two half-lines `[c_a, ∞)` and `[c_b, ∞)` have different left endpoints,
there exists a point `m` in exactly one of them. -/
lemma exists_in_exactly_one_halfline (c_a c_b : ℝ) (h : c_a ≠ c_b) :
    ∃ m : ℝ, ¬((m ≥ c_a) ↔ (m ≥ c_b)) := by
  cases lt_or_gt_of_ne h <;> [ exact ⟨ c_a, by aesop ⟩ ; exact ⟨ c_b, by aesop ⟩ ]

/-! ## Original (false) statement — commented out

The statement below is false as written. See the module docstring
for a concrete counterexample and discussion of possible fixes.
-/

/- COMMENTED OUT: FALSE STATEMENT
theorem equivalence_break_at_finite_precision
    (b : ℕ) (hb : 2 ≤ b) (s : ℕ) (hs : 1 ≤ s)
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1) :
    ∃ (tstar : ℕ) (m_tstar : ℝ),
      tstar ≤ 2^b ∧
      1 ≤ tstar ∧
      (decide (quantizeReal s m_tstar ≥
               sigma * Real.sqrt (2 * tstar * Real.log (tstar / alpha)))
       ≠ decide (quantizeReal s (m_tstar - sigma^2 * tstar / 2) ≥
                 Real.log (1 / alpha))) := by
  sorry
-/

/-! ## Corrected statement: generic (non-integer shift) case

When `sigma^2 * 2^(s-1)` is not an integer, the shift `D = sigma^2/2` is
not a grid multiple, and the two quantized decision thresholds provably
differ. This is the "generic" case covering all but a measure-zero set
of `sigma` values. -/

/-
**Equivalence break at finite precision (generic case).**

When `sigma^2 * 2^(s-1)` is not an integer — which holds for all but a
measure-zero set of `sigma > 0` at fixed `s` — the two quantized
decision rules produce different stopping decisions at `tstar = 1`.

This is a corrected version of the original statement that adds the
non-integer-shift hypothesis, making the theorem provable.
-/
theorem equivalence_break_at_finite_precision_generic
    (b : ℕ) (hb : 2 ≤ b) (s : ℕ) (hs : 1 ≤ s)
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1)
    (h_generic : ∀ k : ℤ, sigma ^ 2 / 2 * (2 : ℝ) ^ s ≠ ↑k) :
    ∃ (tstar : ℕ) (m_tstar : ℝ),
      tstar ≤ 2^b ∧
      1 ≤ tstar ∧
      (decide (quantizeReal s m_tstar ≥
               sigma * Real.sqrt (2 * tstar * Real.log (tstar / alpha)))
       ≠ decide (quantizeReal s (m_tstar - sigma^2 * tstar / 2) ≥
                 Real.log (1 / alpha))) := by
  contrapose! h_generic;
  have h_eq : ∀ m : ℝ, (quantizeReal s m ≥ sigma * Real.sqrt (2 * 1 * Real.log (1 / alpha))) ↔ (quantizeReal s (m - sigma ^ 2 * 1 / 2) ≥ Real.log (1 / alpha)) := by
    intro m; specialize h_generic 1 m ( by linarith [ Nat.pow_le_pow_right two_pos hb ] ) ( by linarith ) ; aesop;
  have h_eq : ∀ m : ℝ, (m ≥ (⌈sigma * Real.sqrt (2 * 1 * Real.log (1 / alpha)) * (2 : ℝ) ^ s⌉ : ℤ) / (2 : ℝ) ^ s) ↔ (m ≥ (⌈Real.log (1 / alpha) * (2 : ℝ) ^ s⌉ : ℤ) / (2 : ℝ) ^ s + sigma ^ 2 * 1 / 2) := by
    intro m; specialize h_eq m; simp_all +decide [ quantizeReal_ge_iff ] ;
    grind +splitImp;
  have h_eq : (⌈sigma * Real.sqrt (2 * 1 * Real.log (1 / alpha)) * (2 : ℝ) ^ s⌉ : ℤ) / (2 : ℝ) ^ s = (⌈Real.log (1 / alpha) * (2 : ℝ) ^ s⌉ : ℤ) / (2 : ℝ) ^ s + sigma ^ 2 * 1 / 2 := by
    exact le_antisymm ( by simpa using h_eq _ |>.2 le_rfl ) ( by simpa using h_eq _ |>.1 le_rfl );
  field_simp at h_eq;
  exact ⟨ ⌈sigma * Real.sqrt ( 2 * Real.log ( 1 / alpha ) ) * 2 ^ s⌉ - ⌈Real.log ( 1 / alpha ) * 2 ^ s⌉, by push_cast; linarith ⟩

end Kairos.Stats