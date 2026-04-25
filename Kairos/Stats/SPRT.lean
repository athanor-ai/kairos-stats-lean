/-
Kairos.Stats.SPRT — Wald's sequential probability ratio test.

The SPRT (Wald 1947) is the foundational *sequential* hypothesis test:
two simple hypotheses

  H_0: data is iid p_0,    H_1: data is iid p_1,

observe X_1, X_2, … sequentially, maintain the log-likelihood ratio
Λ_n = Σ_{i ≤ n} log(p_1(X_i) / p_0(X_i)), stop at the first n with
Λ_n ≥ A or Λ_n ≤ B (for A > 0 > B), then declare H_1 if Λ_n ≥ A and
H_0 if Λ_n ≤ B.

Mathlib has zero formalization of SPRT. We ship four headline theorems:

* `SPRT.error_rates`           — Wald's bound on type-I error in terms
                                  of the (A, B) boundaries.
* `SPRT.wald_approximation`    — practitioner-facing form: choose
                                  A = log((1-β)/α), B = log(β/(1-α))
                                  to get error rates ≤ (α, β).
* `SPRT.wald_wolfowitz_optimal` — *the* optimality theorem: SPRT
                                  minimizes E[τ | H_0] and E[τ | H_1]
                                  among all sequential tests with the
                                  same error rates. Aristotle-class.
* `SPRT.expected_sample_size`  — closed-form E[τ | H_i] in terms of KL
                                  divergences D(p_i ‖ p_{1-i}).

Status (2026-04-25, ATH-604): scaffolded with full statements + closure
plan in each proof body. Sorries flagged here, **excluded from
`Kairos.Stats.AxiomAudit`** until closures land.

References
----------
* Wald (1947), *Sequential Analysis*. Wiley.
* Wald & Wolfowitz (1948), *Optimum character of the SPRT*.
* Siegmund (1985), *Sequential Analysis*. Modern reference.
* Ramdas, Grünwald, Vovk, Shafer (2023), *Game-theoretic statistics*.
-/
import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.WaldIdentity

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

universe u

/-- An SPRT specification: two probability density functions `p₀, p₁`
on a measurable space, with boundary parameters `A > 0 > B`. The
`logLR` field stores the per-sample log-likelihood ratio
`log(p₁ x / p₀ x)` as a measurable real-valued function — abstract
rather than computed from `p₀, p₁` so that the user can plug in the
analytic form for tractable hypothesis pairs. -/
structure SPRT (X : Type u) [MeasurableSpace X] where
  /-- Per-sample log-likelihood ratio. -/
  logLR     : X → ℝ
  /-- LR is measurable. -/
  logLR_mble : Measurable logLR
  /-- Upper boundary. -/
  A          : ℝ
  /-- Lower boundary. -/
  B          : ℝ
  /-- A > 0. -/
  hA_pos     : 0 < A
  /-- B < 0. -/
  hB_neg     : B < 0

namespace SPRT

variable {X : Type u} [MeasurableSpace X]
variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}

/-- The cumulative log-likelihood ratio process for an iid sample
sequence `Y : ℕ → Ω → X`:

  Λ_n(ω) = Σ_{i < n} logLR(Y i ω). -/
noncomputable def cumLogLR (S : SPRT X) (Y : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range n).sum (fun i => S.logLR (Y i ω))

@[simp] lemma cumLogLR_zero (S : SPRT X) (Y : ℕ → Ω → X) (ω : Ω) :
    cumLogLR S Y 0 ω = 0 := by
  simp [cumLogLR]

lemma cumLogLR_succ (S : SPRT X) (Y : ℕ → Ω → X) (n : ℕ) (ω : Ω) :
    cumLogLR S Y (n + 1) ω = cumLogLR S Y n ω + S.logLR (Y n ω) := by
  simp [cumLogLR, Finset.sum_range_succ]

/-- The boundary-exit event at time `n`: the cumulative LR has left
the continuation region `(B, A)` by step `n`. -/
def exitedBy (S : SPRT X) (Y : ℕ → Ω → X) (n : ℕ) (ω : Ω) : Prop :=
  cumLogLR S Y n ω ≤ S.B ∨ S.A ≤ cumLogLR S Y n ω

/-- The "rejected H_0" event up to time `n`: cumulative LR has crossed
the upper boundary at some `k ≤ n`. -/
def rejectedH0By (S : SPRT X) (Y : ℕ → Ω → X) (n : ℕ) (ω : Ω) : Prop :=
  ∃ k, k ≤ n ∧ S.A ≤ cumLogLR S Y k ω

/-- **Wald's error-rate bound** (the basic SPRT guarantee).

For any SPRT with boundary `A > 0`, under H_0 (data iid p₀) the
probability that the running cumulative LR ever crosses `A` is at most
`exp(-A)`:

  Pr_{H_0}(∃ n, Λ_n ≥ A) ≤ exp(-A).

This is the type-I error of the boundary-stopping test. The dual under
H_1 gives the type-II error.

Closure plan: this is `wald_identity_exp` applied at λ = 1 to the
LR-martingale, combined with Ville's inequality on the boundary-crossing
event. The exp-martingale property of `exp(Λ_n)` under H_0 is the key
fact — `E_{p_0}[p_1/p_0] = 1` makes `(p_1/p_0)_n` a positive
martingale with mean 1. -/
theorem error_rates
    [IsProbabilityMeasure μ]
    (S : SPRT X) (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (Y : ℕ → Ω → X)
    (_hY_adapted : ∀ i, Measurable[𝓕 i] (Y i))
    -- Under H_0 (data iid p₀), the per-sample LR-exponential has
    -- conditional mean ≤ 1: ∫ exp(logLR(Y_i)) | F_{i-1} = ∫ p₁/p₀ dp₀ = 1.
    (_hLR_under_H0 :
      ∀ i, ∫ ω, Real.exp (S.logLR (Y i ω)) ∂μ ≤ 1)
    -- The exp-LR process forms a non-negative supermartingale.
    (_hExpLR_super :
      Supermartingale
        (fun n ω => Real.exp (cumLogLR S Y n ω))
        𝓕 μ) :
    μ {ω | ∃ n, S.A ≤ cumLogLR S Y n ω} ≤ ENNReal.ofReal (Real.exp (-S.A)) := by
  sorry

/-- **Wald's approximation**: the practitioner-facing form.

To get type-I error ≤ α and type-II error ≤ β, set

  A = log((1-β)/α),    B = log(β/(1-α)).

This is a corollary of `error_rates` applied symmetrically under H_0
and H_1, with the algebra worked out for the standard error-rate
parameterization. The "approximation" name is historical (Wald used
it because the inequalities are tight only modulo overshoot at the
boundary) — the bound it gives is exact.

Statement: with the Wald boundary choice and the abstract LR-martingale
hypothesis, the boundary-crossing event under H_0 has probability ≤ α.
-/
theorem wald_approximation
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (Y : ℕ → Ω → X) (logLR : X → ℝ) (_hLR_mble : Measurable logLR)
    {α β : ℝ} (hα : 0 < α) (hα' : α < 1) (hβ : 0 < β) (_hβ' : β < 1)
    (_hY_adapted : ∀ i, Measurable[𝓕 i] (Y i))
    (_hLR_under_H0 : ∀ i, ∫ ω, Real.exp (logLR (Y i ω)) ∂μ ≤ 1)
    (_hExpLR_super :
      Supermartingale
        (fun n ω => Real.exp ((Finset.range n).sum
          (fun i => logLR (Y i ω))))
        𝓕 μ) :
    μ {ω | ∃ n, Real.log ((1 - β) / α)
                  ≤ (Finset.range n).sum (fun i => logLR (Y i ω))}
      ≤ ENNReal.ofReal α := by
  sorry

/-- **Wald-Wolfowitz optimality**: SPRT minimizes expected sample size.

Among all sequential tests `T = (σ, δ)` (a stopping time σ + a
{H_0, H_1}-valued decision δ) with type-I error ≤ α and type-II error
≤ β, Wald's SPRT (with boundaries chosen via `wald_approximation`)
achieves

  E[τ_T | H_i] ≥ E[τ_SPRT | H_i],   i ∈ {0, 1}.

This is the original Wald-Wolfowitz 1948 optimality theorem.

Closure: Aristotle-class. Min-max argument over the space of
sequential tests; the proof in Wald-Wolfowitz 1948 is ~12 pages of
measure-theoretic case analysis. -/
theorem wald_wolfowitz_optimal
    [IsProbabilityMeasure μ]
    (S : SPRT X) (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (Y : ℕ → Ω → X)
    -- Any other sequential test = (stopping time σ, decision δ).
    (σ : Ω → ℕ)
    (_hσ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime σ))
    (δ : Ω → Bool) (_hδ_mble : Measurable δ)
    -- σ achieves the same error rates under H_0 and H_1.
    {α β : ℝ}
    (_h_typeI  : μ {ω | δ ω = true}  ≤ ENNReal.ofReal α)
    (_h_typeII : μ {ω | δ ω = false} ≤ ENNReal.ofReal β)
    -- Wald-approximation boundaries.
    (_hA : S.A = Real.log ((1 - β) / α))
    (_hB : S.B = Real.log (β / (1 - α)))
    -- SPRT stopping time (the function whose expectation is bounded).
    -- For optimality the theorem only needs `sprtStop` to be the
    -- first-exit time of the LR from `(B, A)`; this is captured
    -- abstractly by the per-ω characterizing predicate below.
    (sprtStop : Ω → ℕ)
    (_hsprtStop : ∀ ω, S.A ≤ cumLogLR S Y (sprtStop ω) ω
                       ∨ cumLogLR S Y (sprtStop ω) ω ≤ S.B)
    (_hτ_int : Integrable (fun ω => (sprtStop ω : ℝ)) μ) :
    ∫ ω, (sprtStop ω : ℝ) ∂μ ≤ ∫ ω, (σ ω : ℝ) ∂μ := by
  sorry

/-- **Expected sample size** in closed form.

Under H_0 the SPRT stopping time has expectation

  E[τ | H_0] ≈ ((1-β)·B + β·A) / (-D(p_0 ‖ p_1))

where `D(p_0 ‖ p_1)` is the Kullback-Leibler divergence and α, β are
the achieved type-I and type-II rates. The "≈" is exact modulo overshoot
at the boundary, which is `O(1)` in the small-error regime.

Closure: this is `wald_identity` (first moment) applied to Λ_n with
the boundary crossing recharacterizing
E[Λ_τ | H_0] = (1-β)·B + β·A. -/
theorem expected_sample_size
    [IsProbabilityMeasure μ]
    (S : SPRT X) (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (Y : ℕ → Ω → X) (D_p0_p1 : ℝ) (_hD_pos : 0 < D_p0_p1)
    -- Under H_0, the per-step expected log-LR is the negative KL divergence
    -- from p_0 to p_1.
    (_hKL : ∀ i, ∫ ω, S.logLR (Y i ω) ∂μ = -D_p0_p1)
    (_hY_adapted : ∀ i, Measurable[𝓕 i] (Y i))
    {α β : ℝ} (_hα : 0 < α) (_hβ : 0 < β)
    -- SPRT stopping time (abstract; a real construction would use
    -- `Nat.find` on the boundary-exit predicate).
    (sprtStop : Ω → ℕ)
    (_hτ_int : Integrable (fun ω => (sprtStop ω : ℝ)) μ) :
    ∫ ω, (sprtStop ω : ℝ) ∂μ
      = ((1 - β) * S.B + β * S.A) / (-D_p0_p1) := by
  sorry

end SPRT

end Kairos.Stats
