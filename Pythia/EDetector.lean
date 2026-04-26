/-
Pythia.EDetector — E-detector framework for sequential change detection.

# Overview

An **e-detector** (Shin, Ramdas, Rinaldo 2024) is the sequential-change-detection
counterpart to confidence sequences. Rather than bounding a parameter at every
stopping time, an e-detector maintains a process that is bounded (≤ 1 in
expectation under the null) and grows when a change has occurred, yielding
anytime-valid Type-I error control.

Reference:
  Shin, J., Ramdas, A., and Rinaldo, A. (2024).
  *E-detectors: a non-parametric framework for online change detection.*
  arXiv:2203.03532.

# Core objects

## EProcess
A non-negative process `M : ℕ → Ω → ℝ≥0` with `M 0 = 1` and `E[M τ] ≤ 1`
for every stopping time τ under the null. This is Ville's inequality in reverse:
Ville gives `ℙ(M_τ ≥ c) ≤ 1/c`; the e-process property is `E[M_τ] ≤ 1`.

## EDetector
Given an e-process M and a threshold α ∈ (0, 1), the detector fires at the
first time t where `M t ≥ 1/α`. Anytime-valid Type-I error control:

  ℙ_null(τ_α < ∞) ≤ α.

This follows from Markov's inequality at the stopped value together with
`E[M_{τ_α}] ≤ 1`.

## MartingaleEProcess
A non-negative martingale starting at 1 is automatically an e-process (the
optional-stopping theorem gives `E[M_τ] = E[M_0] = 1` under integrability
conditions; Ville's inequality is the strict supermartingale version).

## ExpEProcess
For an iid sequence X_1, X_2, … that is sub-Gaussian with parameter σ, the
exponential process

  M_t = exp(λ · S_t − t · ψ(λ)),      ψ(λ) = λ² σ² / 2

is a non-negative martingale starting at 1 under the null (sub-Gaussian MGF
equals `exp(ψ(λ))` per step). This bridges the e-detector framework to
`Pythia.SubGaussianMG`.

## Combining e-processes
If M and N are e-processes, so are:
  • `(M + N) / 2` (mixture / averaging) — convexity of the e-class;
  • `M · N` (product) — when M and N are independent.

This enables detector combination (e.g. multi-stream monitoring, independent
sensors aggregated into a single anytime-valid alarm).

# Closure roadmap (per statement)

* `eprocess_supermartingale_bound` — direct application of Ville's inequality
  (`VilleSupermartingale.ville_ineq`) after establishing that any
  supermartingale with E[M_0] = 1 satisfies the e-process bound at stopping times.
  Needs: `OptionalStoppingUnbounded.stoppedValue_le_nnreal` or similar.

* `edetector_type_i_error` — one-line Markov on `M_{τ_α}` + e-process bound.
  Needs: `eprocess_supermartingale_bound` + `MeasureTheory.measure_le_of_integral`.

* `martingale_eprocess_iff` — forward: optional stopping (`stoppedValue_integral_eq`
  for the martingale). Reverse: supermartingale is weaker than martingale, direct.
  Needs: `MeasureTheory.Martingale.stoppedValue_integral_eq`.

* `exp_eprocess_subgaussian` — apply `SubGaussianMG.exp_supermartingale` at the
  optimal λ; M_0 = exp(0) = 1. Uses `HasCondSubgaussianMGF` from Mathlib.

* `combine_eprocesses_avg` — linearity of expectation + convexity.
  Product version needs independence hypothesis.

# Status

Tier 2 / sequential stats scaffold (2026-04-25).
All five statements are `sorry`-ed with flagged closure plans.
**Excluded from `Pythia.AxiomAudit` until closures land.**
-/
import Mathlib
import Pythia.Basic
import Pythia.SubGaussianMG
import Pythia.VilleSupermartingale

namespace Pythia

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal BigOperators

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {𝓕 : Filtration ℕ mΩ}

/-! ## E-process definition -/

/-- An **e-process** specification: a non-negative process M adapted to 𝓕,
starting at 1, whose stopped value has expectation ≤ 1 under μ for every
bounded stopping time τ.

The `e_bound` field captures `∀ τ bounded stopping time, ∫ M τ ∂μ ≤ 1`.
We carry the bound with respect to bounded stopping times (≤ N for some N)
rather than general stopping times, matching the Doob/Ville machinery
available in Mathlib v4.28.0 for `stoppedValue`. -/
structure EProcess (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- The process itself. -/
  process    : ℕ → Ω → ℝ
  /-- Non-negativity at every time and every ω. -/
  nonneg     : ∀ t ω, 0 ≤ process t ω
  /-- Initial value is 1. -/
  start_one  : ∀ ω, process 0 ω = 1
  /-- Adapted to the filtration. -/
  adapted    : Adapted 𝓕 process
  /-- Integrability at each step. -/
  integrable : ∀ t, Integrable (process t) μ
  /-- E-process bound: for every bounded stopping time τ (τ ω ≤ N for some N),
      the expected stopped value is at most 1. -/
  e_bound    : ∀ (τ : Ω → ℕ∞) (_ : IsStoppingTime 𝓕 τ) (N : ℕ) (_ : ∀ ω, τ ω ≤ ↑N),
      ∫ ω, stoppedValue process τ ω ∂μ ≤ 1

/-! ## Core theorems -/

/-- **E-process supermartingale bound** (Ville-style).

If M is an e-process, then for any threshold `c > 0`:

  ℙ_null(∃ t, M_t ≥ c) ≤ 1 / c.

This is Ville's inequality: the e-process is a non-negative supermartingale
starting at 1, so the measure of the event that M ever exceeds `c` is at
most `E[M_0] / c = 1 / c`.

Closure plan: apply `VilleSupermartingale.ville_ineq` after establishing that
`EProcess.e_bound` implies the supermartingale property on the process. The
key step is the tower property: `E[M_{t+1} | F_t] ≤ M_t` follows from
`e_bound` applied to the constant stopping time t+1 versus t. Then
`ville_ineq` yields the bound directly with `E[M_0] = 1`. -/
theorem eprocess_supermartingale_bound
    (M : EProcess 𝓕 μ)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t : ℕ, c ≤ M.process t ω} ≤ ENNReal.ofReal (1 / c) := by
  -- closure plan: derive Supermartingale M.process 𝓕 μ from M.e_bound via the
  -- tower property, then apply ville_ineq with E[M.process 0] = 1.
  sorry

/-- **E-detector Type-I error control**.

Given an e-process M and threshold α ∈ (0, 1), define the stopping time:

  τ_α(ω) = inf{t : M_t(ω) ≥ 1/α}

Then `ℙ_null(τ_α < ∞) ≤ α`.

This is the fundamental guarantee of the e-detector framework: by choosing
to alarm at level 1/α, the false-alarm probability under the null is ≤ α
at every stopping time, regardless of how long one observes.

Closure plan: `{ω | τ_α ω < ∞} ⊆ {ω | ∃ t, M.process t ω ≥ 1/α}`. Then
`eprocess_supermartingale_bound` at `c = 1/α` gives the bound as
`ENNReal.ofReal (1 / (1/α)) = ENNReal.ofReal α`. -/
theorem edetector_type_i_error
    (M : EProcess 𝓕 μ)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt : α < 1)
    -- The detector firing time: first t where M_t ≥ 1/α.
    (τ_α : Ω → ℕ∞)
    (hτ_stop : IsStoppingTime 𝓕 τ_α)
    -- τ_α fires exactly when M crosses 1/α.
    (hτ_def : ∀ ω, τ_α ω < ⊤ → M.process (τ_α ω).toNat ω ≥ 1 / α) :
    μ {ω | τ_α ω < ⊤} ≤ ENNReal.ofReal α := by
  -- closure plan: inclusion {ω | τ_α ω < ⊤} ⊆ {ω | ∃ t, M_t ω ≥ 1/α},
  -- then eprocess_supermartingale_bound at c = 1/α gives measure ≤ 1/(1/α) = α.
  sorry

/-- **Non-negative martingales starting at 1 are e-processes**.

A non-negative martingale M with M_0 = 1 satisfies `E[M_τ] ≤ 1` for every
bounded stopping time τ (optional stopping for martingales gives `E[M_τ] = 1`;
for supermartingales the inequality is ≤).

This is the key bridge: every non-negative martingale gives an e-process, and
hence an e-detector. In particular, the Wald SPRT likelihood ratio process
(a positive martingale under H_0) is an e-process.

Closure plan: `MeasureTheory.Martingale.stoppedValue_integral_eq` gives equality
`∫ stoppedValue M τ = ∫ M 0` for a uniformly integrable martingale stopped at a
bounded stopping time. Combine with `M.start_one` and the definition of
`EProcess.e_bound`. The `iff` direction (e-process ⇒ martingale) is false in
general; we state the forward direction only in the `→` and the natural weaker
converse (supermartingale ⇒ e-process) as the `←` arm. -/
theorem martingale_eprocess_iff
    (process : ℕ → Ω → ℝ)
    (hnonneg : ∀ t ω, 0 ≤ process t ω)
    (hstart : ∀ ω, process 0 ω = 1)
    (hadapt : Adapted 𝓕 process)
    (hint : ∀ t, Integrable (process t) μ)
    -- Key hypothesis: M is a non-negative martingale.
    (hmg : Martingale process 𝓕 μ) :
    -- Conclusion: M satisfies the e-process bound (martingales have equality,
    -- so the ≤ 1 bound holds trivially).
    ∀ (τ : Ω → ℕ∞) (_ : IsStoppingTime 𝓕 τ) (N : ℕ) (_ : ∀ ω, τ ω ≤ ↑N),
        ∫ ω, stoppedValue process τ ω ∂μ ≤ 1 := by
  intro τ hτ N hτN
  -- closure plan: Martingale.stoppedValue_integral_eq gives ∫ stoppedValue process τ = ∫ process 0.
  -- Then ∫ process 0 = 1 by hstart + IsProbabilityMeasure.
  sorry

/-- **Exponential e-process for sub-Gaussian sequences**.

Let X_1, X_2, … be iid with mean 0 and sub-Gaussian parameter σ under the
null measure μ. For any λ, the exponential process

  M_t(ω) = exp(λ · S_t(ω) − t · λ² σ² / 2),      S_t = Σ_{i < t} X_i

satisfies:
  1. M_0 = 1,
  2. M_t ≥ 0 for all t,
  3. E[M_τ] ≤ 1 for every bounded stopping time τ.

Hence M is an e-process; this bridges `Pythia.SubGaussianMG` to the
e-detector framework. The same process is the building block for
sub-Gaussian anytime-valid confidence sequences.

Closure plan: property (3) follows because `M_t = exp(λ S_t) / exp(t ψ(λ))`
is a non-negative martingale under H_0 (the sub-Gaussian MGF gives conditional
expectation = 1 per step). Apply `martingale_eprocess_iff` to close via the
`SubGaussianMG.exp_supermartingale` construction in `Pythia.SubGaussianMG`.
The `HasCondSubgaussianMGF` hypothesis in `SubGaussianMG` supplies the needed
conditional MGF bound. -/
theorem exp_eprocess_subgaussian
    [StandardBorelSpace Ω]
    {σ : ℝ} (hσ : 0 < σ)
    (mg : SubGaussianMG σ 𝓕 μ)
    -- X_i are the increments of the sub-Gaussian martingale.
    (X : ℕ → Ω → ℝ)
    (hX_eq : ∀ t ω, X t ω = mg.process (t + 1) ω - mg.process t ω)
    (lam : ℝ) :
    -- The exponential process M_t = exp(lam · S_t − t · lam² σ² / 2) is an e-process.
    let S : ℕ → Ω → ℝ := fun t ω => (Finset.range t).sum (fun i => X i ω)
    let M : ℕ → Ω → ℝ :=
      fun t ω => Real.exp (lam * S t ω - t * (lam ^ 2 * σ ^ 2 / 2))
    ∀ (τ : Ω → ℕ∞) (_ : IsStoppingTime 𝓕 τ) (N : ℕ) (_ : ∀ ω, τ ω ≤ ↑N),
        ∫ ω, stoppedValue M τ ω ∂μ ≤ 1 := by
  intro S M τ hτ N hτN
  -- closure plan: M is a non-negative martingale by SubGaussianMG.increments_subG
  -- (HasCondSubgaussianMGF) + the MGF identity E[exp(lam · X_i) | F_i] = exp(lam² σ² / 2).
  -- Then martingale_eprocess_iff gives ∫ stoppedValue M τ ≤ 1.
  sorry

/-- **Combining e-processes by averaging**.

If M and N are e-processes under the same filtration and null measure μ,
then their average `(M + N) / 2` is also an e-process.

This is the simplest detector-combination result: run two independent
detection methods and average. The e-class is convex, so any mixture of
e-processes is an e-process.

The product `M · N` is also an e-process when M and N are independent, but
that version requires an independence hypothesis and is left as a follow-up.

Closure plan: linearity of the integral gives
  `∫ stoppedValue ((M + N)/2) τ = (∫ stoppedValue M τ + ∫ stoppedValue N τ) / 2`
and by `M.e_bound`, `N.e_bound` both integrals are ≤ 1, so the sum / 2 ≤ 1.
This is a 10-line local proof once the `stoppedValue` linearity lemmas are
identified (likely `stoppedValue_add` + `integral_add` in Mathlib). -/
theorem combine_eprocesses_avg
    (M N : EProcess 𝓕 μ) :
    -- The averaged process satisfies the e-process bound.
    ∀ (τ : Ω → ℕ∞) (_ : IsStoppingTime 𝓕 τ) (K : ℕ) (_ : ∀ ω, τ ω ≤ ↑K),
        ∫ ω, stoppedValue (fun t ω => (M.process t ω + N.process t ω) / 2) τ ω ∂μ ≤ 1 := by
  intro τ hτ K hτK
  -- closure plan: stoppedValue_add + integral_add give linearity;
  -- then M.e_bound + N.e_bound + (a + b)/2 ≤ 1 when a, b ≤ 1.
  sorry

end Pythia
