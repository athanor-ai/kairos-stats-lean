/-
Pythia.WaldIdentity — Wald's identity for stopping times.

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

Status (2026-04-25): scaffolded with full statements + closure
plan in each proof body. Sorries are flagged here and the module is
**excluded from `Pythia.AxiomAudit`** until closures land. Closure
path is direct local Mathlib — no external prover needed; each theorem fits in
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
import Pythia.Basic
import Pythia.MeasureTheory.OptionalStoppingUnbounded
import Pythia.Tactic.Pythia

namespace Pythia

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

/-- **Wald's identity** (first moment, m-parameterized).

For an iid integrable sequence `X_i` with `E[X_1] = m` and a stopping
time `τ` with `E[τ] < ∞`,

  E[S_τ] = m · E[τ].

The centered version `m = 0` is `wald_identity_centered` below (a
1-line corollary). Unifying both into one m-parameterized theorem per
peer-review feedback (PR #11): the centered form is what's used
internally, the m-form is what practitioners reach for, and shipping
the general theorem with a corollary is the Mathlib-upstream-friendly
shape.

Closure plan (local, local closure):
  1. Show `partialSum X - m·n` is a martingale w.r.t. `𝓕` using the
     iid-mean hypothesis (telescoping conditional expectations).
  2. Apply `Submartingale.expectation_stoppedValue_le_expectation`
     bidirectionally (martingale = both sub and super).
  3. The integrability hypothesis `E[τ] < ∞` controls boundary terms.
-/
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

/-- **Wald's identity** (centered corollary, m = 0).

The classical statement: for centered iid `X_i` with `E[X_1] = 0` and
finite-mean stopping time τ,

  E[S_τ] = 0.

Direct corollary of `wald_identity` at `m = 0`. Kept as a separate
declaration for prose clarity in the user-facing API; Mathlib upstream
will see the unified `wald_identity` only. -/
theorem wald_identity_centered
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ)
    (hX_int : ∀ i, Integrable (X i) μ)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_mart : Martingale (fun n ω => partialSum X n ω) 𝓕 μ)
    (τ : Ω → ℕ)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ))
    (hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ) :
    ∫ ω, partialSum X (τ ω) ω ∂μ = 0 := by
  have h := wald_identity 𝓕 X 0 hX_int hX_mean
    (by simpa using hX_mart) τ hτ hτ_int
  simpa using h

/-- **Wald's identity (centered) via uniform integrability — ℕ∞ form.**

A direct application of `Pythia.MTUnbounded.optional_stopping_unbounded`
to the centered partial-sum martingale. This variant takes the stopping
time as `τ : Ω → ℕ∞` (matching the form `optional_stopping_unbounded`
consumes), with `τ < ∞ a.s.` as a hypothesis rather than a coercion
artifact. Used internally; the `Ω → ℕ` ergonomic wrapper
`wald_identity_centered_via_UI` lives below.

For a martingale `S_n = partialSum X n` (`S_0 = 0`), an a.s.-finite
stopping time `τ : Ω → ℕ∞`, and uniform integrability of the stopped
process, we get `E[stoppedValue S τ] = 0`. -/
@[stat_lemma]
theorem wald_identity_centered_via_optional_stopping
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ)
    (hS_mart : Martingale (fun n ω => partialSum X n ω) 𝓕 μ)
    (τ : Ω → ℕ∞)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 τ)
    (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hUI : MeasureTheory.UniformIntegrable
              (fun n : ℕ =>
                MeasureTheory.stoppedProcess
                  (fun n ω => partialSum X n ω) τ n)
              1 μ) :
    ∫ ω, MeasureTheory.stoppedValue
            (fun n ω => partialSum X n ω) τ ω ∂μ = 0 := by
  -- `optional_stopping_unbounded` says ∫ stoppedValue S τ = ∫ S 0.
  have hOS :=
    Pythia.MTUnbounded.optional_stopping_unbounded
      (M := fun n ω => partialSum X n ω) hS_mart hτ hτ_finite hUI
  -- And ∫ S 0 = ∫ 0 = 0 by `partialSum_zero`.
  rw [hOS]
  simp [partialSum_zero]

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
        Supermartingale
          (fun n ω =>
            Real.exp (lam * partialSum X n ω
                       - (n : ℝ) * (σSq * lam ^ 2 / 2)))
          𝓕 μ)
    (τ : Ω → ℕ)
    (_hτ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime τ)) (lam : ℝ) :
    ∫ ω, Real.exp (lam * partialSum X (τ ω) ω
                    - (τ ω : ℝ) * (σSq * lam ^ 2 / 2)) ∂μ ≤ 1 := by
  sorry

/-- **Wald's identity (second moment) via uniform integrability — ℕ∞ form.**

A direct application of `Pythia.MTUnbounded.optional_stopping_unbounded`
to the quadratic-variation martingale
`M_n = (S_n - m·n)² - σSq·n`. This martingale has `M_0 = 0`, so optional
stopping gives `E[M_τ] = 0`, equivalently
`E[(S_τ - m·τ)²] = σSq · E[τ]`.

Companion to `wald_identity_squared`: takes the same quadratic-variation
martingale hypothesis, but parameterizes the stopping time as `τ : Ω → ℕ∞`
with explicit `τ < ∞ a.s.` + UI of the stopped process, instead of the
`Ω → ℕ` + `Integrable τ²` shape. -/
theorem wald_identity_squared_via_optional_stopping
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (m σSq : ℝ)
    (hQuadVar_mart :
      Martingale
        (fun n ω => (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
        𝓕 μ)
    (τ : Ω → ℕ∞)
    (hτ : MeasureTheory.IsStoppingTime 𝓕 τ)
    (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hUI : MeasureTheory.UniformIntegrable
              (fun n : ℕ =>
                MeasureTheory.stoppedProcess
                  (fun n ω =>
                    (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
                  τ n)
              1 μ) :
    ∫ ω, MeasureTheory.stoppedValue
            (fun n ω =>
              (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
            τ ω ∂μ = 0 := by
  -- `optional_stopping_unbounded` says ∫ stoppedValue M τ = ∫ M 0,
  -- and M_0 ω = (S_0 ω - m·0)² - σSq·0 = (0 - 0)² - 0 = 0.
  have hOS :=
    Pythia.MTUnbounded.optional_stopping_unbounded
      (M := fun n ω =>
        (partialSum X n ω - m * (n : ℝ)) ^ 2 - σSq * (n : ℝ))
      hQuadVar_mart hτ hτ_finite hUI
  rw [hOS]
  simp [partialSum_zero]

/-- **Wald's identity (exponential / MGF form) via optional stopping — ℕ∞ form.**

For a sub-Gaussian iid sequence `X_i` with proxy variance `σSq`, the
exponential process `E_n(λ, ω) = exp(λ S_n - n ψ(λ))` with
`ψ(λ) = σSq λ² / 2` is a non-negative supermartingale. Applied via the
supermartingale-form of optional stopping (Williams §10.10 supermartingale
analogue) to an a.s.-finite `τ : Ω → ℕ∞`, one obtains

  E[E_τ(λ)] ≤ E[E_0(λ)] = 1.

Honest gap: the unbounded-τ optional-stopping module shipped in
`Pythia.MeasureTheory.OptionalStoppingUnbounded` exposes only the
**martingale** version (`optional_stopping_unbounded`), giving equality
`∫ stoppedValue M τ = ∫ M 0`. The supermartingale `≤`-variant requires
a parallel proof with only the `Submartingale.expected_stoppedValue_mono`
applied to `-M` direction (no sandwich), and is deferred to a follow-up
in the `MTUnbounded` module. The statement here pre-bakes the result so
downstream consumers can already depend on it; closure plan is one-line:
once `MTUnbounded.optional_stopping_unbounded_super` lands, this proof
mirrors the squared-version body. -/
theorem wald_identity_exp_via_optional_stopping
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (σSq : ℝ) (_hσ : 0 ≤ σSq) (lam : ℝ)
    (_hExp_super :
      Supermartingale
        (fun n ω =>
          Real.exp (lam * partialSum X n ω
                     - (n : ℝ) * (σSq * lam ^ 2 / 2)))
        𝓕 μ)
    (τ : Ω → ℕ∞)
    (_hτ : MeasureTheory.IsStoppingTime 𝓕 τ)
    (_hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (_hUI : MeasureTheory.UniformIntegrable
              (fun n : ℕ =>
                MeasureTheory.stoppedProcess
                  (fun n ω =>
                    Real.exp (lam * partialSum X n ω
                              - (n : ℝ) * (σSq * lam ^ 2 / 2)))
                  τ n)
              1 μ) :
    ∫ ω, MeasureTheory.stoppedValue
            (fun n ω =>
              Real.exp (lam * partialSum X n ω
                        - (n : ℝ) * (σSq * lam ^ 2 / 2)))
            τ ω ∂μ ≤ 1 := by
  -- needs `MTUnbounded.optional_stopping_unbounded_super` (supermartingale `≤`-variant).
  sorry

end Pythia
