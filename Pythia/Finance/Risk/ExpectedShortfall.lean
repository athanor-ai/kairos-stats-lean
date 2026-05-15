/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expected Shortfall (algebraic closed-form for the normal case)

Expected Shortfall (ES, also called Conditional VaR) at confidence
level `α ∈ (0, 1)` for a normal `N(μ, σ²)` distribution has the
closed form

    ES_α(μ, σ) = -μ + σ · h,

where `h = φ(z_α) / α` and `z_α = Φ⁻¹(1 - α)` is the upper-α
quantile.  ES is the coherent-risk-measure cousin of VaR (it
satisfies subadditivity; VaR does not), making it the practitioner-
preferred metric under Basel III and across hedge-fund risk teams.

This file parameterises over the abstract `h` value (the user
supplies `φ(z_α) / α` for their chosen confidence level), so we can
state and prove sign / scaling / VaR-dominance properties without
depending on Mathlib's `Real.normalCDF` machinery.

## Main results

* `esNormal`                    : `-μ + σ · h`
* `esNormal_zero_mean`          : at `μ = 0` → `σ · h`
* `esNormal_pos_homogeneous`    : positive-homogeneous (ADEH axiom 3)
* `esNormal_translation`        : translation-invariant (ADEH axiom 4)
* `esNormal_dominates_varNormal`: `VaR(μ, σ; z) ≤ ES(μ, σ; h)` when
  `z ≤ h` (the standard normal-tail-mean-dominates-quantile fact
  `φ(z_α)/α ≥ z_α` for `α < 0.5`)

## Why this lemma (coherent-risk bridge)

ES is the canonical coherent risk measure under the ADEH (Artzner-
Delbaen-Eber-Heath) characterisation already formalised in
`Pythia.Risk.CoherentMeasures` (theorem `isCoherent_sup_expect`).
This file gives the closed-form Normal-ES identities and the
ES ≥ VaR dominance inequality so the `pythia` tactic cascade can
close ES-vs-VaR comparisons + capital-adequacy goals.

## References

* Artzner, P., Delbaen, F., Eber, J.-M., and Heath, D.
  "Coherent Measures of Risk." *Mathematical Finance* 9(3): 203-228 (1999).
* Acerbi, C. and Tasche, D. "On the Coherence of Expected Shortfall."
  *Journal of Banking and Finance* 26(7): 1487-1503 (2002).
* Rockafellar, R. T. and Uryasev, S. "Optimization of Conditional
  Value-at-Risk." *Journal of Risk* 2(3): 21-41 (2000).
-/
import Mathlib
import Pythia.Finance.Risk.ValueAtRisk
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Normal-distribution Expected Shortfall closed form:
    `ES(μ, σ; h) = -μ + σ · h`,
where `h = φ(z_α) / α` is the conditional-tail-mean factor. -/
noncomputable def esNormal (μ σ h : ℝ) : ℝ :=
  -μ + σ * h

/-- **Zero-mean specialisation.** -/
@[stat_lemma]
theorem esNormal_zero_mean (σ h : ℝ) :
    esNormal 0 σ h = σ * h := by
  unfold esNormal; ring

/-- **Positive homogeneity (ADEH axiom 3).** -/
@[stat_lemma]
theorem esNormal_pos_homogeneous {α : ℝ} (hα : 0 ≤ α) (μ σ h : ℝ) :
    esNormal (α * μ) (α * σ) h = α * esNormal μ σ h := by
  unfold esNormal; ring

/-- **Translation invariance (ADEH axiom 4 / cash invariance).**
Adding `c` to the mean reduces ES by `c`. -/
@[stat_lemma]
theorem esNormal_translation (μ σ h c : ℝ) :
    esNormal (μ + c) σ h = esNormal μ σ h - c := by
  unfold esNormal; ring

/-- **ES dominates VaR.** When the conditional-tail-mean factor `h`
exceeds the quantile `z` (the standard fact `φ(z_α)/α ≥ z_α` for
`α < 0.5`), and `σ ≥ 0`, ES is at least as large as VaR.

This is the practitioner-relevant comparison: ES gives a sharper
(weakly larger) tail-risk capital number than VaR at the same
confidence level. -/
@[stat_lemma]
theorem esNormal_dominates_varNormal
    {σ : ℝ} (hσ : 0 ≤ σ) {z h : ℝ} (hzh : z ≤ h) (μ : ℝ) :
    varNormal μ σ z ≤ esNormal μ σ h := by
  unfold varNormal esNormal
  have : σ * z ≤ σ * h := mul_le_mul_of_nonneg_left hzh hσ
  linarith

end Pythia.Finance
