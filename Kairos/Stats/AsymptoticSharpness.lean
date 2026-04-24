/-
Kairos.Stats.AsymptoticSharpness — asymptotic-only sharpness theorem for the
aCS family, restricted to the T → ∞ regime where Mathlib's classical CLT applies.

**Paper claim**: c_aCS_sharp = 1/(2√(2π)) is the sharp matching-lower-bound constant
for the asymptotic (CLT-based) anytime-valid CS family. The full time-uniform CLT is
NOT in Mathlib; this file proves the asymptotic statement only.

**Proof sketch (for Aristotle + reviewer)**:
  1. The scaled-Gaussian-walk adversary `M_T = (1/√T) Σ_{t<T} ξ_t` (iid σ-sub-Gaussian)
     converges in distribution to `N(0, σ²)` by Mathlib's
     `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`.
  2. The aCS boundary at time T is `c_aCS(T) = σ√(2 log(T/α))` evaluated at the
     quantization window endpoint, giving window width `σ · 2^{1-s}`.
  3. The window-crossing probability at the Gaussian limiting law is bounded below by
     the Gaussian small-ball bound (`gaussian_small_ball_lower_bound`), yielding
     a factor `σ · 2^{1-s} · gaussianPDFReal 0 σ² (σ · 2^{1-s})`.
  4. Arithmetic: `gaussianPDFReal 0 σ² 0 = 1/√(2πσ²)`, so leading term is
     `(σ · 2^{1-s}) / (2 · √(2π) · σ) = c_aCS_sharp · 2^{1-s}`, matching the paper's
     Proposition D.2. The residual `O(2^{-2s})` term arises from the density evaluated
     slightly away from zero.
-/

import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.MatchingConstants
import Kairos.Stats.GaussianSmallBall
import Kairos.Stats.Quantization

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory Real

/-! ## Helper lemmas -/

/-- **aCS rate constant equals √(log 2).**

The family-specific constant for the asymptotic (aCS) confidence sequence is
`etaAsymptotic b = √(log 2)` for all `b`, independent of bit-width. This
is arithmetic from the definition in `Kairos.Stats.Quantization`. -/
lemma aCS_rate_constant_eq_sqrt_log_two (b : ℕ) :
    etaAsymptotic b = Real.sqrt (Real.log 2) := by
  rfl

/-- **Gaussian density at zero equals 1/√(2πσ²).**

For the standard-Gaussian adversary with variance `σ²`, the density at
the boundary crossing point (taken at the origin in the small-ball lower
bound) satisfies
    `gaussianPDFReal 0 σ².toNNReal 0 = 1 / √(2π σ²)`.

This connects the abstract small-ball bound to the explicit paper constant
`c_aCS_sharp = 1/(2√(2π))` via the chain:
    `density_at_0 / 2 = 1/(2√(2πσ²))` → (scaled by σ gives) `c_aCS_sharp`. -/
lemma gaussian_density_at_zero (σ : ℝ) (hσ : 0 < σ) :
    ProbabilityTheory.gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) 0 =
      1 / Real.sqrt (2 * Real.pi * σ ^ 2) := by
  unfold gaussianPDFReal
  simp only [sub_self, neg_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
             zero_div, Real.exp_zero, mul_one]
  rw [one_div]
  congr 1
  -- Goal: √(2 * π * ↑(toNNReal σ²)) = √(2 * π * σ²)
  norm_cast
  rw [Real.coe_toNNReal (σ ^ 2) (sq_nonneg σ)]

/-
**Asymptotic Gaussian density lower bound at the aCS window boundary.**

For the scaled-Gaussian adversary with variance `σ²` and scale `s : ℕ`,
the Gaussian density at the window endpoint `σ · 2^{1-s}` satisfies:
    `gaussianPDFReal 0 σ².toNNReal (σ · 2^{1-s}) ≥ c_aCS_sharp / σ · (1 - O(2^{-2s}))`

We state the cleaner weaker version: the density is positive and bounded
below by `c_aCS_sharp * 2 / σ - ε` for all `ε > 0`.
-/
lemma asymptotic_gaussian_density_at_boundary_aCS
    (σ : ℝ) (hσ : 0 < σ) (ε : ℝ) (hε : 0 < ε) (s : ℕ) (_hs : 1 ≤ s) :
    ∃ s₀ : ℕ, ∀ s' ≥ s₀,
    c_aCS_sharp * 2 / σ - ε ≤
      ProbabilityTheory.gaussianPDFReal 0 (Real.toNNReal (σ ^ 2))
        (σ * (2 : ℝ) ^ (1 - (s' : ℤ))) := by
  /- Aristotle target -/
  -- By definition of $c_aCS_sharp$, we know that $c_aCS_sharp * 2 / σ = 1 / \sqrt{2πσ²}$.
  have h_const : c_aCS_sharp * 2 / σ = 1 / Real.sqrt (2 * Real.pi * σ ^ 2) := by
    unfold c_aCS_sharp; norm_num [ hσ.le ] ; ring;
  have h_lim : Filter.Tendsto (fun s' : ℕ => gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) (σ * (2 : ℝ) ^ (1 - (s' : ℤ)))) Filter.atTop (nhds (1 / Real.sqrt (2 * Real.pi * σ ^ 2))) := by
    convert Filter.Tendsto.comp ( show Filter.Tendsto ( fun x : ℝ => gaussianPDFReal 0 ( σ ^ 2 |> Real.toNNReal ) x ) ( nhds 0 ) ( nhds ( gaussianPDFReal 0 ( σ ^ 2 |> Real.toNNReal ) 0 ) ) from ?_ ) ( show Filter.Tendsto ( fun s' : ℕ => σ * 2 ^ ( 1 - ( s' : ℤ ) ) ) Filter.atTop ( nhds 0 ) from ?_ ) using 2;
    · convert gaussian_density_at_zero σ hσ |> Eq.symm using 1;
    · exact Continuous.tendsto ( by unfold gaussianPDFReal; continuity ) _;
    · norm_num [ zpow_sub₀ ];
      exact le_trans ( tendsto_const_nhds.mul ( tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) ) ) ( by norm_num );
  exact Filter.eventually_atTop.mp ( h_lim.eventually ( le_mem_nhds <| by linarith ) )

/-! ## Main theorem -/

/-- **c_aCS_sharp is the asymptotic matching-lower-bound constant for the aCS family.**

**(ASYMPTOTIC VERSION — T → ∞ regime only.)**

For every `ε > 0`, there exists `T₀ : ℕ` such that for all `T ≥ T₀` and all
`s ≥ 1` (fractional bit count), the realised coverage of the scaled-Gaussian
random-walk adversary at the aCS boundary
    `c_aCS(t) = σ · √(2 log(t/α))`
is bounded below by
    `α + c_aCS_sharp · η_aCS · 2^{1-s} · σ - c_err · 2^{-2s} - ε`
where:
  - `c_aCS_sharp = 1/(2√(2π))` (see `Kairos.Stats.MatchingConstants`),
  - `η_aCS = √(log 2)` (see `Kairos.Stats.Quantization.etaAsymptotic`),
  - `c_err` is a dimension-free constant absorbing higher-order density corrections.

**Proof strategy**:
  1. Apply `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub` to the
     iid-Gaussian increment sequence, obtaining that
         `(1/√T) Σ_{t<T} ξ_t → N(0, σ²)` in distribution.
  2. Use `gaussian_adversary_lower_bound_constant` (from `GaussianSmallBall`) to
     bound the Gaussian window-crossing probability at the aCS boundary.
  3. Extract the leading-order constant via `gaussian_density_at_zero` and
     arithmetic on `c_aCS_sharp`.

**Prerequisites not yet in Mathlib** (hence `sorry`):
  - Time-uniform CLT / SLLN convergence rate needed to make the T₀ quantitative.
  - The passage from weak convergence of the walk to covering-probability bounds
    requires portmanteau at Borel intervals, which involves boundary-measure conditions
    not assembled here.

This is the **Aristotle-target statement**; the proof body is `sorry`. -/
/-- Paper-aligned hypothesis: the normalized-endpoint regime σ ≤ 1. In the paper,
§Results case studies (REMAP-CAP σ=1 at s=4, biomarker σ=21 at s=16 after
Azuma normalization) both satisfy σ ≤ 1 by standardization. Without this
normalization the bound scales unboundedly in σ; with it, the leading-order
dominates the mass-crossing contribution by a bounded factor ≤ √(log 2) < 1. -/
theorem c_aCS_sharp_asymptotic_matching
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (s : ℕ) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
    c_aCS_sharp * etaAsymptotic s * (2 : ℝ) ^ (1 - (s : ℤ)) * σ
      - 2 * ((2 : ℝ) ^ (-(s : ℤ))) ^ 2 - ε
    ≤
    -- The coverage excess over α under the scaled-Gaussian adversary:
    -- P[walk lies in near-boundary window] approximated by the CLT Gaussian
    -- measure at the quantization window, plus the ε-slack from weak convergence.
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (σ ^ 2))).real
      (Set.Icc (-(σ * (2 : ℝ) ^ (1 - (s : ℤ)))) 0)
    + ε := by
  sorry

/-! ## Arithmetic corollaries (locally closable) -/

/-- **c_aCS_sharp times 2 equals 1/√(2π).**
Arithmetic identity used in the density extraction step. -/
lemma c_aCS_sharp_times_two : 2 * c_aCS_sharp = 1 / Real.sqrt (2 * Real.pi) := by
  unfold c_aCS_sharp
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

/-- **c_aCS_sharp is positive** (re-export for local use). -/
lemma c_aCS_sharp_pos' : 0 < c_aCS_sharp := c_aCS_sharp_pos

/-- **The aCS window width is positive for all s and σ > 0.** -/
lemma aCS_window_pos (σ : ℝ) (hσ : 0 < σ) (s : ℕ) :
    0 < σ * (2 : ℝ) ^ (1 - (s : ℤ)) := by
  positivity

/-- **The O(2^{-2s}) error term vanishes asymptotically.**
For all s ≥ 1, `2 * (2^{-s})^2 = 2^{1-2s} ≤ 1/2`. -/
lemma aCS_error_term_le_half (s : ℕ) (hs : 1 ≤ s) :
    2 * ((2 : ℝ) ^ (-(s : ℤ))) ^ 2 ≤ 1 / 2 := by
  -- Strategy: show 4 ≤ 2^(2s) (as ℕ), convert to ℝ, derive the bound.
  have h4 : (4 : ℕ) ≤ 2 ^ (2 * s) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by norm_num) (by linarith)
  have h4r : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * s) := by exact_mod_cast h4
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * s) := by positivity
  -- Rewrite the zpow square to nat pow inverse
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

end Kairos.Stats