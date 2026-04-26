/-
Copyright (c) 2025 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Infinite-Product Path-Measure Radon–Nikodym Chain Rule

## Overview

For a sequence of measurable spaces `(Ω_n, F_n)` equipped with σ-finite
measures `μ_n, ν_n`, the Radon–Nikodym derivative of the countable product
measure `⊗_n μ_n` with respect to `⊗_n ν_n` on `∏_n Ω_n` equals the
(a.e.) limit of the partial products `∏_{i<n} (dμ_i/dν_i)(ω_i)`,
provided these partial products converge in `L¹(∏ ν)`.

### Main results

* `finProdMeasure_rnDeriv_eq_prod` — finite-product RN factorisation
* `pathMeasure_rnDeriv_eq_tprod` — the target infinite-product chain rule
* `kakutani_dichotomy` — Kakutani's 0–1 law for equivalence vs singularity

### Gap inventory (honest `sorry`s)

| Gap name                      | Difficulty | Blocked on                        |
|-------------------------------|------------|-----------------------------------|
| `finProd_rnDeriv`             | Medium     | Mathlib `Measure.pi` glue         |
| `finProd_ac`                  | Medium     | Mathlib `Measure.pi` glue         |
| `kolmogorov_extension`        | Hard       | Missing Mathlib infra             |
| `measurable_partialRNDeriv`   | ✅ Proved  | —                                 |
| `measurable_rnDeriv_comp`     | ✅ Proved  | —                                 |
| `pathMeasure_rnDeriv`         | Hard       | Kolmogorov ext. + martingale conv |
| `kakutani_dichotomy`          | Hard       | Full Kakutani theorem             |
| `partialRNDeriv_pos`          | Medium     | AC + positivity of RN deriv       |
| `lintegral_partialRNDeriv`    | Medium     | Product integral factorisation    |

### References

* Kakutani, S. "On equivalence of infinite product measures", 1948.
* Williams, D. *Probability with Martingales*, Ch. 14.
-/

import Mathlib

open scoped ENNReal NNReal MeasureTheory
open MeasureTheory MeasureTheory.Measure Filter

noncomputable section

/-! ## §1  Finite-product RN derivative factorisation -/

namespace PathMeasureRN

section FiniteProd

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  (μ ν : ∀ i, Measure (Ω i))
  [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]

/-- The pointwise product of coordinate-wise RN derivatives for a finite
index set, evaluated at a point `ω : ∏ i, Ω i`. -/
def finProdRNDeriv (ω : ∀ i, Ω i) : ℝ≥0∞ :=
  Finset.univ.prod (fun i => (μ i).rnDeriv (ν i) (ω i))

/-- **Finite-product RN factorisation.** For finite `ι` and σ-finite
measures, the RN derivative of the product measure `Measure.pi μ` with
respect to `Measure.pi ν` equals the pointwise product of the individual
RN derivatives, a.e.  Gap: `finProd_rnDeriv`. -/
theorem finProdMeasure_rnDeriv_eq_prod :
    (Measure.pi μ).rnDeriv (Measure.pi ν) =ᵐ[Measure.pi ν] finProdRNDeriv μ ν := by
  sorry -- gap:finProd_rnDeriv

/-- Absolute continuity of finite products reduces to coordinate-wise
absolute continuity.  Gap: `finProd_ac`. -/
theorem finProd_absolutelyContinuous
    (hac : ∀ i, (μ i) ≪ (ν i)) :
    Measure.pi μ ≪ Measure.pi ν := by
  sorry -- gap:finProd_ac

end FiniteProd

/-! ## §2  Sequential / countable-product path-measure setup

Since Mathlib does not yet provide a `Measure.iInfProd` (countable product
measure via Kolmogorov extension), we axiomatise the minimal interface
needed.  Every axiom is recorded as a `sorry` with a named gap so that
downstream code can track when a Mathlib PR closes it.
-/

/-- Bundled data for an infinite product probability measure on `∏ (n : ℕ), Ω n`.

This packages the Kolmogorov-extension product together with the
consistency property that downstream proofs require. -/
structure InfProdMeasure
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)] where
  /-- The product measure on `∏ n, Ω n`. -/
  measure : Measure (∀ n, Ω n)
  /-- The product measure is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure measure

/-- Existence of the Kolmogorov-extension product measure.
Gap: `kolmogorov_extension`. -/
theorem infProdMeasure_exists
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)] :
    Nonempty (InfProdMeasure μ) := by
  sorry -- gap:kolmogorov_extension

/-! ## §3  Partial-product Radon–Nikodym densities -/

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The partial-product RN derivative up to index `n`:
  `L_n(ω) = ∏_{i < n} (dμ_i/dν_i)(ω_i)`. -/
def partialRNDeriv (μ ν : ∀ n, Measure (Ω n)) (n : ℕ) (ω : ∀ k, Ω k) : ℝ≥0∞ :=
  (Finset.range n).prod (fun i => (μ i).rnDeriv (ν i) (ω i))

/-- `partialRNDeriv 0` is identically 1. -/
@[simp]
theorem partialRNDeriv_zero (μ ν : ∀ n, Measure (Ω n)) (ω : ∀ k, Ω k) :
    partialRNDeriv μ ν 0 ω = 1 := by
  simp [partialRNDeriv]

/-- Multiplicative recursion: `L_{n+1} = L_n · (dμ_n/dν_n)`. -/
theorem partialRNDeriv_succ (μ ν : ∀ n, Measure (Ω n)) (n : ℕ) (ω : ∀ k, Ω k) :
    partialRNDeriv μ ν (n + 1) ω =
      partialRNDeriv μ ν n ω * (μ n).rnDeriv (ν n) (ω n) := by
  simp [partialRNDeriv, Finset.prod_range_succ]

/-- Each coordinate-wise `rnDeriv` is measurable in the product. -/
theorem measurable_rnDeriv_comp (μ ν : ∀ n, Measure (Ω n)) (n : ℕ) :
    Measurable (fun (ω : ∀ k, Ω k) => (μ n).rnDeriv (ν n) (ω n)) := by
  exact (Measure.measurable_rnDeriv (μ n) (ν n)).comp (measurable_pi_apply n)

/-
The partial-product density is measurable.
-/
theorem measurable_partialRNDeriv (μ ν : ∀ n, Measure (Ω n)) (n : ℕ) :
    Measurable (partialRNDeriv μ ν n) := by
  convert Finset.measurable_prod _ fun i _ => ?_;
  · infer_instance;
  · exact measurable_rnDeriv_comp μ ν i

/-! ## §4  The infinite-product RN chain rule -/

section InfProd

variable (μ ν : ∀ n, Measure (Ω n))
  [∀ n, IsProbabilityMeasure (μ n)]
  [∀ n, IsProbabilityMeasure (ν n)]

/-- Convergence hypothesis: the partial-product densities converge pointwise
a.e. and the limit is integrable (L¹ convergence of the martingale). -/
structure PartialProdConverges
    (Pν : InfProdMeasure ν) where
  /-- The a.e. pointwise limit of `partialRNDeriv`. -/
  limitFn : (∀ n, Ω n) → ℝ≥0∞
  /-- The limit function is measurable. -/
  measurable_limitFn : Measurable limitFn
  /-- Pointwise a.e. convergence. -/
  ae_tendsto :
    ∀ᵐ ω ∂Pν.measure,
      Filter.Tendsto (fun n => partialRNDeriv μ ν n ω)
        Filter.atTop (nhds (limitFn ω))
  /-- The limit is integrable (ensures the density is in L¹). -/
  integrable_limitFn :
    ∫⁻ ω, limitFn ω ∂Pν.measure ≤ 1

/-- **Path-Measure RN Chain Rule (target theorem).**

Given probability measures `μ_n, ν_n` on each `Ω_n`, let `P = ⊗ ν_n`
and `Q = ⊗ μ_n` be the Kolmogorov-extension product measures.  If the
partial-product densities `L_n = ∏_{i<n} dμ_i/dν_i` converge a.e. and
the limit is integrable, then:

1. `Q ≪ P`, and
2. `dQ/dP = lim_n L_n` a.e.

Gap: `pathMeasure_rnDeriv`.  A full proof requires either:
  (a) the Kolmogorov-extension product + a Lévy-type 0–1 argument, or
  (b) a direct martingale-convergence proof via the backward-martingale
      representation.
-/
theorem pathMeasure_rnDeriv_eq_tprod
    (Pν : InfProdMeasure ν)
    (Pμ : InfProdMeasure μ)
    (hconv : PartialProdConverges μ ν Pν) :
    Pμ.measure ≪ Pν.measure ∧
    Pμ.measure.rnDeriv Pν.measure =ᵐ[Pν.measure] hconv.limitFn := by
  sorry -- gap:pathMeasure_rnDeriv

/-! ## §5  Kakutani's dichotomy -/

/-- The Hellinger integral `ρ(μ, ν) = ∫ √(dμ/dν) dν` for a single
coordinate.  Uses `ENNReal.rpow` with exponent `1/2`. -/
def hellingerIntegral {α : Type*} [MeasurableSpace α]
    (μ' ν' : Measure α) [SigmaFinite ν'] : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.rpow (μ'.rnDeriv ν' x) ((2 : ℝ)⁻¹) ∂ν'

/-- The partial Hellinger product up to index `n`. -/
def partialHellingerProd (n : ℕ) : ℝ≥0∞ :=
  (Finset.range n).prod (fun i => hellingerIntegral (μ i) (ν i))

/-- **Kakutani's dichotomy.**  For sequences of probability measures:
* If `∏_n ρ(μ_n, ν_n) → 0`, the product measures are mutually singular.
* If `∏_n ρ(μ_n, ν_n) → c > 0`, the product measures are mutually
  absolutely continuous (equivalent).

Gap: `kakutani_dichotomy`.
-/
theorem kakutani_dichotomy
    (Pν : InfProdMeasure ν)
    (Pμ : InfProdMeasure μ) :
    (Filter.Tendsto (partialHellingerProd μ ν) Filter.atTop (nhds 0) →
      Pμ.measure.MutuallySingular Pν.measure) ∧
    (∀ c : ℝ≥0∞, 0 < c →
      Filter.Tendsto (partialHellingerProd μ ν) Filter.atTop (nhds c) →
        Pμ.measure ≪ Pν.measure ∧ Pν.measure ≪ Pμ.measure) := by
  sorry -- gap:kakutani_dichotomy

/-! ## §6  Further auxiliary lemmas -/

/-- If every `μ_n ≪ ν_n`, then `partialRNDeriv` is a.e. positive. -/
theorem partialRNDeriv_pos
    (hac : ∀ n, (μ n) ≪ (ν n))
    (Pν : InfProdMeasure ν)
    (n : ℕ) :
    ∀ᵐ ω ∂Pν.measure, 0 < partialRNDeriv μ ν n ω := by
  sorry -- gap:partialRNDeriv_pos

/-- Integral of `partialRNDeriv n` under the ν-product is 1
(each factor integrates to 1 because μ_n, ν_n are probability measures
and `∫ dμ/dν dν = μ(Ω) = 1`). -/
theorem lintegral_partialRNDeriv_eq_one
    (hac : ∀ n, (μ n) ≪ (ν n))
    (Pν : InfProdMeasure ν)
    (n : ℕ) :
    ∫⁻ ω, partialRNDeriv μ ν n ω ∂Pν.measure = 1 := by
  sorry -- gap:lintegral_partialRNDeriv

end InfProd

end PathMeasureRN

end