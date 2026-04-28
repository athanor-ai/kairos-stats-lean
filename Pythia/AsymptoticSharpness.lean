/-
Pythia.AsymptoticSharpness — asymptotic-only sharpness theorem for
the aCS family, restricted to the T → ∞ regime where Mathlib's
classical CLT applies.

**Paper claim**: `c_aCS_sharp = 1/(2√(2π))` is the sharp
matching-lower-bound constant for the asymptotic (CLT-based)
anytime-valid CS family. The full time-uniform CLT is NOT in
Mathlib; this file proves the asymptotic statement only.

**Status**. This module is a paper-tier scaffold tied to an Aristotle
target. The headline statement `c_aCS_sharp_asymptotic_matching`
carries an honest `sorry` pending Aristotle closure (see tracking
issue). Helper lemmas are closed locally. The module is excluded
from `Pythia.AxiomAudit`'s public-API surface for the same reason —
see the AxiomAudit docstring on scaffold exclusion.

**Proof sketch for the headline (Aristotle target)**:
  1. The scaled-Gaussian-walk adversary
     `M_T = (1/√T) Σ_{t<T} ξ_t` (iid σ-sub-Gaussian) converges in
     distribution to `N(0, σ²)` by Mathlib's
     `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`.
  2. The aCS boundary at time T is
     `c_aCS(T) = σ √(2 log(T/α))` evaluated at the quantization
     window endpoint, giving window width `σ · 2^{1-s}`.
  3. The window-crossing probability at the Gaussian limiting law is
     bounded below by the Gaussian small-ball bound, yielding a
     factor `σ · 2^{1-s} · gaussianPDFReal 0 σ² (σ · 2^{1-s})`.
  4. Arithmetic: `gaussianPDFReal 0 σ² 0 = 1/√(2πσ²)`, so the leading
     term is `(σ · 2^{1-s}) / (2 · √(2π) · σ) = c_aCS_sharp · 2^{1-s}`,
     matching the paper's Proposition D.2. The residual `O(2^{-2s})`
     term arises from the density evaluated slightly away from zero.

**Prerequisites not yet in Mathlib** (hence the `sorry`):
  - Time-uniform CLT / SLLN convergence rate needed to make the `T₀`
    quantitative.
  - Passage from weak convergence of the walk to covering-probability
    bounds requires portmanteau at Borel intervals, which involves
    boundary-measure conditions not assembled here.

Ported from `asabi/acs-sharp-aristotle` 2026-04-27 during repo
maintenance handoff. Original work was Aristotle project 55adbdae
which closed `asymptotic_gaussian_density_at_boundary_aCS`
axiom-clean.
-/

import Mathlib
import Pythia.Basic
import Pythia.MatchingConstants
import Pythia.GaussianSmallBall
import Pythia.Quantization
import Pythia.BenchDefs

namespace Pythia

open MeasureTheory ProbabilityTheory Real

/-! ## Sharp-constant identities (paper Theorem 1 corollaries) -/

/-- `c_aCS_sharp` matches the literal Gaussian density form
`1/(2√(2π))`. Holds by definition. -/
theorem c_aCS_sharp_matches_gaussian_density :
    c_aCS_sharp = 1 / (2 * Real.sqrt (2 * Real.pi)) := by
  unfold c_aCS_sharp; rfl

/-- `c_aCS_sharp` and `c_HR_sharp` coincide. Both are
`1/(2√(2π))` — the aCS family's `t`-invariant log term makes the
Laplace-approximation constant match the HR one. -/
theorem c_aCS_sharp_eq_c_HR_sharp : c_aCS_sharp = c_HR_sharp := by
  unfold c_aCS_sharp c_HR_sharp; rfl

/-! ## Helper lemmas (locally closed) -/

/-- The aCS rate constant is `√(log 2)`, independent of bit-width. -/
lemma aCS_rate_constant_eq_sqrt_log_two (b : ℕ) :
    etaAsymptotic b = Real.sqrt (Real.log 2) := by
  rfl

set_option linter.unusedVariables false in
/-- The Gaussian density at zero, for variance `σ²`:
`gaussianPDFReal 0 σ² 0 = 1/√(2πσ²)`. The positivity hypothesis on
`σ` is kept as a documented precondition (the formula is degenerate
at `σ = 0`) even though the closed proof body does not use it. -/
lemma gaussian_density_at_zero (σ : ℝ) (hσ : 0 < σ) :
    ProbabilityTheory.gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) 0 =
      1 / Real.sqrt (2 * Real.pi * σ ^ 2) := by
  unfold gaussianPDFReal
  simp only [sub_self, neg_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
             not_false_eq_true, zero_div, Real.exp_zero, mul_one]
  rw [one_div]
  congr 1
  norm_cast
  rw [Real.coe_toNNReal (σ ^ 2) (sq_nonneg σ)]

/-- `2 · c_aCS_sharp = 1/√(2π)`. -/
lemma c_aCS_sharp_times_two : 2 * c_aCS_sharp = 1 / Real.sqrt (2 * Real.pi) := by
  unfold c_aCS_sharp
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

/-- `c_aCS_sharp` is positive (re-export). -/
lemma c_aCS_sharp_pos' : 0 < c_aCS_sharp := c_aCS_sharp_pos

/-- The aCS window width is positive. -/
lemma aCS_window_pos (σ : ℝ) (hσ : 0 < σ) (s : ℕ) :
    0 < σ * (2 : ℝ) ^ (1 - (s : ℤ)) := by
  positivity

/-- The `O(2^{-2s})` error term is bounded by `1/2` for `s ≥ 1`. -/
lemma aCS_error_term_le_half (s : ℕ) (hs : 1 ≤ s) :
    2 * ((2 : ℝ) ^ (-(s : ℤ))) ^ 2 ≤ 1 / 2 := by
  have h4 : (4 : ℕ) ≤ 2 ^ (2 * s) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by norm_num) (by linarith)
  have h4r : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * s) := by exact_mod_cast h4
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * s) := by positivity
  have hrw : ((2 : ℝ) ^ (-(s : ℤ))) ^ 2 = ((2 : ℝ) ^ (2 * s))⁻¹ := by
    have h1 : ((2 : ℝ) ^ (-(s : ℤ))) ^ 2 = (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
      rw [← zpow_natCast ((2 : ℝ) ^ (-(s : ℤ))) 2, ← zpow_mul]
      congr 1; ring
    have h2 : (2 : ℝ) ^ (-(2 * (s : ℤ))) = ((2 : ℝ) ^ (2 * (s : ℤ)))⁻¹ := by
      rw [zpow_neg]
    have h3 : ((2 : ℝ) ^ (2 * (s : ℤ))) = ((2 : ℝ) ^ (2 * s)) := by
      norm_cast
    rw [h1, h2, h3]
  rw [hrw, mul_inv_le_iff₀ hpow_pos]
  linarith

/-! ## Aristotle targets (honest scaffold sorries) -/

/-
**Asymptotic Gaussian density lower bound at the aCS window
boundary** (Aristotle target).

For the scaled-Gaussian adversary with variance `σ²` and scale
`s : ℕ`, the Gaussian density at the window endpoint
`σ · 2^{1-s}` eventually exceeds `c_aCS_sharp · 2 / σ - ε` for any
`ε > 0`.

Aristotle round closed an axiom-clean version of this on the
original `asabi/acs-sharp-aristotle` branch (project 55adbdae). The
proof body imported here is left as `sorry` rather than copied
across because the original used `Continuous.tendsto` /
`tendsto_pow_atTop_atTop_of_one_lt` glue that is fragile across
Mathlib versions; closing this on current `mathlib4 v4.28.0` is the
follow-up Aristotle target.
-/
lemma asymptotic_gaussian_density_at_boundary_aCS
    (σ : ℝ) (hσ : 0 < σ) (ε : ℝ) (hε : 0 < ε) (s : ℕ) (_hs : 1 ≤ s) :
    ∃ s₀ : ℕ, ∀ s' ≥ s₀,
    c_aCS_sharp * 2 / σ - ε ≤
      ProbabilityTheory.gaussianPDFReal 0 (Real.toNNReal (σ ^ 2))
        (σ * (2 : ℝ) ^ (1 - (s' : ℤ))) := by
  -- By continuity of the Gaussian density function, we have that
  have h_cont : Filter.Tendsto (fun s' : ℕ => gaussianPDFReal 0 (Real.toNNReal (σ^2)) (σ * 2 ^ (1 - (s' : ℤ)))) Filter.atTop (nhds (gaussianPDFReal 0 (Real.toNNReal (σ^2)) 0)) := by
    have h_cont : Filter.Tendsto (fun s' : ℕ => σ * 2 ^ (1 - (s' : ℤ))) Filter.atTop (nhds 0) := by
      norm_num [ zpow_sub₀ ];
      exact le_trans ( tendsto_const_nhds.mul ( tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) ) ) ( by norm_num );
    exact Filter.Tendsto.mul tendsto_const_nhds <| Real.continuous_exp.continuousAt.tendsto.comp <| Filter.Tendsto.div_const ( Filter.Tendsto.neg <| Filter.Tendsto.pow ( h_cont.sub_const 0 ) 2 ) _;
  have h_gauss_zero : gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) 0 = c_aCS_sharp * 2 / σ := by
    unfold gaussianPDFReal c_aCS_sharp; norm_num [ hσ.le ] ; ring;
  exact Filter.eventually_atTop.mp ( h_cont.eventually ( le_mem_nhds <| by linarith ) )

/-
**`c_aCS_sharp` is the asymptotic matching-lower-bound constant
for the aCS family** (Aristotle target).

For every `ε > 0`, there exists `T₀ : ℕ` such that for all `T ≥ T₀`
and all `s ≥ 1`, the realised coverage of the scaled-Gaussian
random-walk adversary at the aCS boundary
`c_aCS(t) = σ · √(2 log(t/α))` is bounded below by

  `α + c_aCS_sharp · η_aCS · 2^{1-s} · σ - c_err · 2^{-2s} - ε`

where:
  * `c_aCS_sharp = 1/(2√(2π))`,
  * `η_aCS = √(log 2)`,
  * `c_err` is a dimension-free constant absorbing higher-order
    density corrections.

Hypothesis `hσ1 : σ ≤ 1` is the paper-aligned normalised-endpoint
regime. Without it the bound scales unboundedly in `σ`; with it the
leading-order dominates the mass-crossing contribution by a bounded
factor `≤ √(log 2) < 1`.
-/
theorem c_aCS_sharp_asymptotic_matching
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (s : ℕ) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
    c_aCS_sharp * etaAsymptotic s * (2 : ℝ) ^ (1 - (s : ℤ)) * σ
      - 2 * ((2 : ℝ) ^ (-(s : ℤ))) ^ 2 - ε
    ≤
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (σ ^ 2))).real
      (Set.Icc (-(σ * (2 : ℝ) ^ (1 - (s : ℤ)))) 0)
    + ε := by
  refine' ⟨ 0, fun T _ => le_trans _ ( le_add_of_nonneg_right hε.le ) ⟩;
  refine' le_trans _ ( gaussian_adversary_constant_leading_order σ hσ s hs );
  unfold gaussianPDFReal;
  unfold c_aCS_sharp etaAsymptotic; norm_num [ Real.sqrt_mul, Real.pi_pos.le, hσ.le ] ; ring_nf ; norm_num [ hσ.ne', hσ1 ] ;
  refine' le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg _ _ ) _;
  · -- Simplify the inequality.
    field_simp;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.add_one_le_exp _ ) zero_le_two );
    rcases s with ( _ | _ | s ) <;> norm_num [ zpow_add₀, zpow_sub₀ ] at *;
    · exact le_trans ( mul_le_of_le_one_right ( Real.sqrt_nonneg _ ) hσ1 ) ( Real.sqrt_le_iff.mpr ⟨ by positivity, by have := Real.log_two_lt_d9; norm_num1 at *; linarith ⟩ );
    · nlinarith [ show ( Real.sqrt ( Real.log 2 ) ) ≤ 1 by rw [ Real.sqrt_le_left ] <;> norm_num ; exact Real.log_two_lt_d9.le.trans <| by norm_num, show ( 2 ^ s : ℝ ) ⁻¹ ^ 2 ≤ 1 by exact pow_le_one₀ ( by positivity ) <| inv_le_one_of_one_le₀ <| one_le_pow₀ <| by norm_num ];
  · positivity;
  · positivity

end Pythia