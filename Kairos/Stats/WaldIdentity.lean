/-
Kairos.Stats.WaldIdentity — Wald's identity for stopping times.

Wald's identity (1944, *Sequential Analysis*) is the workhorse identity
of sequential statistics: for an iid integrable sequence `X_i` and a
stopping time `τ` with `E[τ] < ∞`,

  E[Σ_{i ≤ τ} X_i] = E[X_1] · E[τ].

Mathlib has the optional-stopping theorem in fully general form
(`MeasureTheory.Martingale.stoppedValue_integral_eq`) but the iid-sum
corollary that practitioners actually invoke is missing. We ship four
statements:

* `wald_identity_centered`    — first-moment, μ = 0 (just optional stop).
* `wald_identity`             — first-moment, general mean.
* `wald_identity_squared`     — second-moment: E[(Σ - μτ)²] = σSq · E[τ].
* `wald_identity_exp`         — exponential-MGF form for sub-Gaussian X.
                                 Bridge to anytime-valid inference.

Status (2026-04-25, ATH-605): scaffolded with full statements + closure
plan in each proof body. Sorries are flagged here and the module is
**excluded from `Kairos.Stats.AxiomAudit`** until closures land. Closure
path is direct local Mathlib — no Aristotle needed; each theorem fits in
<30 lean lines once the right `OptionalSampling.*` lemma is identified.

The hypotheses are stated with the abstract martingale/iid properties as
hypotheses (rather than constructed from `ProbabilityTheory.iIndepFun`)
to keep the statements robust against Mathlib Independence-API churn.
A `from_iIndepFun` lemma will bridge once the closures land.

References
----------
* Wald, *Sequential Analysis*, 1944. Original.
* Williams, *Probability with Martingales*, §10.10.
-/
import Mathlib
import Kairos.Stats.Basic

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}

/-- Partial-sum process `S_n = X_1 + … + X_n` of a real-valued process
indexed by `ℕ`. We define it directly on the path space; downstream
consumers will instantiate via concrete iid samples. -/
noncomputable def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range n).sum (fun i => X i ω)

@[simp] lemma partialSum_zero (X : ℕ → Ω → ℝ) (ω : Ω) :
    partialSum X 0 ω = 0 := by
  simp [partialSum]

lemma partialSum_succ (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum X (n + 1) ω = partialSum X n ω + X n ω := by
  simp [partialSum, Finset.sum_range_succ]

/-- Coerce a `Ω → ℕ` stopping time to the `Ω → WithTop ℕ` form Mathlib
uses for `IsStoppingTime`. -/
noncomputable def liftStoppingTime (τ : Ω → ℕ) : Ω → WithTop ℕ :=
  fun ω => (τ ω : WithTop ℕ)

/-- **Wald's identity** (first moment, centered case).

For an iid integrable sequence `X_i` with `E[X_1] = 0` adapted to a
filtration `𝓕`, and a stopping time `τ` of `𝓕` with `E[τ] < ∞`,

  E[S_τ] = 0

where `S_n = Σ_{i < n} X_i` is the partial-sum process.

Closure plan (local, no Aristotle):
  1. Show `partialSum X` is a martingale w.r.t. `𝓕` using the
     iid-mean-zero hypothesis (telescoping conditional expectations).
  2. Apply `Submartingale.expectation_stoppedValue_le_expectation`
     bidirectionally (martingale = both sub and super).
  3. The integrability hypothesis `E[τ] < ∞` controls boundary terms.
-/
theorem wald_identity_centered
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ)
    (_hX_int : ∀ i, Integrable (X i) μ)
    (_hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (_hX_mart : Martingale (fun n ω => partialSum X n ω) 𝓕 μ)
    (τ : Ω → ℕ)
    (_hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (_hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ) :
    ∫ ω, partialSum X (τ ω) ω ∂μ = 0 := by
  sorry

/-- **Wald's identity** (first moment, general mean).

For an iid integrable sequence `X_i` with `E[X_1] = m` and a stopping
time `τ` with `E[τ] < ∞`,

  E[S_τ] = m · E[τ].

Reduction: subtract the mean from each `X_i`, apply the centered
version, expand. -/
theorem wald_identity
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (m : ℝ)
    (_hX_int : ∀ i, Integrable (X i) μ)
    (_hX_mean : ∀ i, ∫ ω, X i ω ∂μ = m)
    (_hX_mart_centered :
      Martingale (fun n ω => partialSum X n ω - m * (n : ℝ)) 𝓕 μ)
    (τ : Ω → ℕ)
    (_hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (_hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ) :
    ∫ ω, partialSum X (τ ω) ω ∂μ = m * ∫ ω, (τ ω : ℝ) ∂μ := by
  sorry

/-- **Wald's identity, second moment.**

For iid `X_i` with `E[X_1] = m`, `Var(X_1) = σSq`, and stopping time `τ`
with `E[τ²] < ∞`,

  E[(S_τ - m·τ)²] = σSq · E[τ].

The squared-deviation analogue. Closure: the same Doob-style optional
stopping but applied to the quadratic-variation martingale
`M_n = (S_n - m·n)² - σSq·n`. -/
theorem wald_identity_squared
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (m σSq : ℝ)
    (_hX_sq_int : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    (_hX_mean : ∀ i, ∫ ω, X i ω ∂μ = m)
    (_hX_var : ∀ i, ∫ ω, (X i ω - m) ^ 2 ∂μ = σSq)
    (_hQuadVar_mart :
      Martingale
        (fun n ω => (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
        𝓕 μ)
    (τ : Ω → ℕ)
    (_hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (_hτ_sq_int : Integrable (fun ω => (τ ω : ℝ) ^ 2) μ) :
    ∫ ω, (partialSum X (τ ω) ω - m * (τ ω : ℝ)) ^ 2 ∂μ
      = σSq * ∫ ω, (τ ω : ℝ) ∂μ := by
  sorry

/-- **Wald's identity, exponential / MGF form.**

For sub-Gaussian iid `X_i` with proxy variance `σSq` (so the cumulant
generating function `ψ(λ) ≤ σSqλ²/2` for all real `λ`), and a stopping
time `τ`,

  E[exp(λ · S_τ - τ · ψ(λ))] ≤ 1.

This is the *bridge to anytime-valid inference*: it says the
exponential martingale `exp(λ·S_n - n·ψ(λ))` evaluated at any stopping
time is still under control. Combined with Markov this gives
Hoeffding-style anytime-valid bounds. -/
theorem wald_identity_exp
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (σSq : ℝ) (_hσ : 0 ≤ σSq)
    (_hX_subG : ∀ i (lam : ℝ),
                ∫ ω, Real.exp (lam * X i ω) ∂μ ≤ Real.exp (σSq * lam ^ 2 / 2))
    (_hExp_super :
      ∀ lam,
        Submartingale
          (fun n ω =>
            -(Real.exp (lam * partialSum X n ω
                       - (n : ℝ) * (σSq * lam ^ 2 / 2))))
          𝓕 μ)
    (τ : Ω → ℕ)
    (_hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ)) (lam : ℝ) :
    ∫ ω, Real.exp (lam * partialSum X (τ ω) ω
                    - (τ ω : ℝ) * (σSq * lam ^ 2 / 2)) ∂μ ≤ 1 := by
  sorry

end Kairos.Stats
