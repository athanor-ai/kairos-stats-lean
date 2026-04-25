/-
Kairos.Stats.Bernstein — Bernstein's inequality + Bennett-Bernstein
maximal inequality for martingales.

Mathlib v4.28 has Hoeffding's inequality for sub-Gaussian random
variables (`measure_sum_ge_le_of_iIndepFun` in
`Mathlib.Probability.Moments.SubGaussian`) but does NOT have the
variance-aware Bernstein form. Bernstein is sharper than Hoeffding
when the variance of the summands is small relative to their range.

Given iid bounded random variables `X₁, …, X_n` with `|X_i| ≤ b`,
zero mean, and variance `σ²`, Bernstein's inequality bounds:

    P(S_n ≥ ε) ≤ exp(−ε² / (2 (n σ² + b ε / 3)))

Hoeffding gives `exp(−ε² / (2 n b²))`. When `σ² ≪ b²` (low-variance
bounded RVs), Bernstein wins by a factor of `b² / σ²` in the exponent.

This module supplies:

1. `bernstein_iid` — Bernstein for iid bounded RVs.
2. `bennett_iid` — Bennett's tighter Bernstein with explicit log
   factor.
3. `bernstein_martingale` — Bennett-Bernstein maximal inequality for
   martingales with conditionally-bounded increments. Supersedes
   Azuma-Hoeffding when conditional variance is small.
4. `freedman` — Freedman's inequality (martingale Bernstein with
   predictable variance process).

Status: scaffold (statements only). Closure path is via the sub-
gamma martingale framework in `Kairos.Stats.SubGamma` — bounded
random variables are sub-gamma with `(ν, c) = (σ², b/3)`, and the
sub-gamma Ville inequality from `subGamma_ville_ineq` reduces to
Bernstein under that parameterisation. Followup PR closes the four
sorries by instantiating the existing `subGamma_ville_ineq`.

Mathlib upstream target: once stable, the iid case ships as a PR to
`Mathlib.Probability.Moments` next to the existing Hoeffding lemmas.
-/
import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.SubGamma

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- **Bernstein's inequality** for iid bounded random variables.
Given `X_i` iid with `|X_i| ≤ b` a.s., `E[X_i] = 0`, `Var(X_i) ≤ σ²`,
and `n` samples:
$$ P\left( \sum_{i=1}^n X_i \geq \varepsilon \right)
   \leq \exp\left( -\frac{\varepsilon^2}{2 (n \sigma^2 + b\varepsilon/3)} \right). $$
-/
theorem bernstein_iid
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b : ℝ} {sigma_sq : ℝ}
    (hb_pos : 0 < b) (hsigma_sq_nonneg : 0 ≤ sigma_sq)
    (h_iid : ∀ t, ProbabilityTheory.IndepFun (X 0) (X t) μ)
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    (h_zero_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (h_var_bound : ∀ t, ∫ ω, (X t ω)^2 ∂μ ≤ sigma_sq)
    (n : ℕ) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | (Finset.range n).sum (fun i => X i ω) ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps^2) / (2 * (n * sigma_sq + b * eps / 3)))) := by
  sorry

/-- **Bennett's inequality**: refined Bernstein with explicit
sub-exponential structure. For iid bounded RVs, Bennett gives the
sharpest known closed-form tail bound. Used in the empirical-process
literature to bound `sup_θ |P_n f_θ - P f_θ|` over rich classes. -/
theorem bennett_iid
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b sigma_sq : ℝ}
    (hb_pos : 0 < b) (hsigma_sq_pos : 0 < sigma_sq)
    (h_iid : ∀ t, ProbabilityTheory.IndepFun (X 0) (X t) μ)
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    (h_zero_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (h_var_bound : ∀ t, ∫ ω, (X t ω)^2 ∂μ ≤ sigma_sq)
    (n : ℕ) (eps : ℝ) (hε : 0 < eps) :
    -- Bennett rate: exp(-n σ²/b² · h(b ε / (n σ²)))
    -- where h(u) = (1+u) log(1+u) - u.
    -- Statement placeholder pending the explicit h-function form.
    True := by
  sorry

/-- **Bernstein's inequality for martingales** (Freedman): a
martingale with conditionally-bounded increments and predictable
variance process satisfies a Bernstein-type bound. Supersedes
Azuma-Hoeffding when conditional variance is small.

Reduces to `Kairos.Stats.subGamma_ville_ineq` via the embedding of
bounded-conditional-increment martingales into the sub-gamma class
with `(ν, c) = (V_n, b/3)` where `V_n = ∑_{t≤n} Var(M_{t+1} - M_t | F_t)`. -/
theorem bernstein_martingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : MeasureTheory.Martingale M 𝓕 μ)
    (b : ℝ) (hb_pos : 0 < b)
    (h_bounded_increments : ∀ t, ∀ᵐ ω ∂μ,
      |M (t + 1) ω - M t ω| ≤ b)
    (V_n : ℝ) (hV_pos : 0 < V_n)
    (h_predictable_var : ∀ t,
      μ[fun ω => (M (t + 1) ω - M t ω)^2 | 𝓕 t] =ᵐ[μ] (fun _ => V_n / (t + 1 : ℝ)))
    (n : ℕ) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | M n ω ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps^2) / (2 * (V_n + b * eps / 3)))) := by
  sorry

/-- **Freedman's inequality**: the maximal-inequality form of
`bernstein_martingale`. Bounds `P(sup_{t ≤ n} M_t ≥ ε)` rather than
the fixed-time `P(M_n ≥ ε)`. Useful for sequential stopping
problems.

Closes via `Kairos.Stats.subGamma_ville_ineq`. -/
theorem freedman
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : MeasureTheory.Martingale M 𝓕 μ)
    (b : ℝ) (hb_pos : 0 < b)
    (h_bounded_increments : ∀ t, ∀ᵐ ω ∂μ,
      |M (t + 1) ω - M t ω| ≤ b)
    (V_n : ℝ) (hV_pos : 0 < V_n)
    (n : ℕ) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | ∃ t : ℕ, t ≤ n ∧ M t ω ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps^2) / (2 * (V_n + b * eps / 3)))) := by
  sorry

end Kairos.Stats
