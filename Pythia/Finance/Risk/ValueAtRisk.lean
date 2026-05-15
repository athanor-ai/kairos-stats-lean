/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Value-at-Risk (algebraic closed-form for the normal case)

For a returns distribution that is normal `N(μ, σ²)`, the
Value-at-Risk at confidence level `α ∈ (0, 1)` is the closed form

    VaR_α(μ, σ) = -μ + σ · z_α,

where `z_α = Φ⁻¹(1 - α)` is the upper-α quantile of the standard
normal.  This file exposes the algebraic kernel parametrised over an
abstract quantile `z : ℝ` (the user supplies the value of `z_α`
appropriate to their confidence level), so we can state and prove
sign / scaling / monotonicity properties without depending on
Mathlib's `Real.normalCDF` / `Real.inverseNormalCDF` machinery.

## Main results

* `varNormal`                : `-μ + σ · z` (parametrised closed form)
* `varNormal_zero_mean`      : at `μ = 0` → `σ · z`
* `varNormal_pos_homogeneous`: `VaR(α·μ, α·σ; z) = α · VaR(μ, σ; z)` for `α ≥ 0`
* `varNormal_mono_in_sigma`  : monotone non-decreasing in `σ` for `z ≥ 0`
* `varNormal_translation`    : `VaR(μ + c, σ; z) = VaR(μ, σ; z) - c`

## Why this lemma

VaR is the practitioner-standard tail-risk metric across trading
desks, regulatory capital (Basel III), and portfolio reporting.
Surfacing the closed-form Normal-VaR identities in Pythia gives the
`pythia` tactic cascade a clean closure target for tail-risk
sign-direction sanity checks.

The companion `Pythia.Finance.ExpectedShortfall` module surfaces the
sharper coherent-risk-measure cousin; this VaR module is *not*
coherent (the canonical counterexample of subadditivity failure is
documented in the references below).

## References

* Jorion, P. *Value at Risk*, 3rd ed. McGraw-Hill (2006).
* Acerbi, C. and Tasche, D. "On the Coherence of Expected Shortfall."
  *Journal of Banking and Finance* 26(7): 1487-1503 (2002).
  (VaR is not coherent; ES is — connection to ADEH axioms.)
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Normal-distribution Value-at-Risk closed form:
    `VaR(μ, σ; z) = -μ + σ · z`,
where `z = Φ⁻¹(1 - α)` is the upper-α standard-normal quantile. -/
noncomputable def varNormal (μ σ z : ℝ) : ℝ :=
  -μ + σ * z

/-- **Zero-mean specialisation.** With `μ = 0`, VaR reduces to `σ · z`
(the pure scale-times-quantile form). -/
@[stat_lemma]
theorem varNormal_zero_mean (σ z : ℝ) :
    varNormal 0 σ z = σ * z := by
  unfold varNormal; ring

/-- **Positive homogeneity.** Rescaling both mean and volatility by a
non-negative constant rescales VaR by the same constant.  This is one
of the four ADEH coherent-risk-measure axioms; VaR satisfies it (the
counterexample to coherence is subadditivity, not pos. homogeneity). -/
@[stat_lemma]
theorem varNormal_pos_homogeneous {α : ℝ} (hα : 0 ≤ α) (μ σ z : ℝ) :
    varNormal (α * μ) (α * σ) z = α * varNormal μ σ z := by
  unfold varNormal; ring

/-- **Monotone in volatility.** For non-negative quantile (the
typical right-tail VaR case with `z = Φ⁻¹(1-α)` for `α < 0.5`),
VaR is monotone non-decreasing in `σ`. -/
@[stat_lemma]
theorem varNormal_mono_in_sigma {z : ℝ} (hz : 0 ≤ z)
    {σ₁ σ₂ : ℝ} (h : σ₁ ≤ σ₂) (μ : ℝ) :
    varNormal μ σ₁ z ≤ varNormal μ σ₂ z := by
  unfold varNormal; have : σ₁ * z ≤ σ₂ * z := mul_le_mul_of_nonneg_right h hz; linarith

/-- **Translation invariance under cash injection.** Adding `c` to
the mean (e.g. injecting cash into a portfolio) reduces VaR by `c`.
This is the cash-invariance axiom of coherent risk measures, which
VaR satisfies. -/
@[stat_lemma]
theorem varNormal_translation (μ σ z c : ℝ) :
    varNormal (μ + c) σ z = varNormal μ σ z - c := by
  unfold varNormal; ring

end Pythia.Finance
