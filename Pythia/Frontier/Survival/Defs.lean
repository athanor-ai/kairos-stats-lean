/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Survival Analysis: Core Definitions

Counting-process formulation of right-censored survival data, following
Andersen–Gill (1982). Defines the key objects for the Cox proportional
hazards model:

* `obsTime` — observed time min(T, C)
* `eventInd` — failure indicator 1{T ≤ C}
* `atRisk` — at-risk indicator 1{t ≤ X}
* `linPred` — linear predictor β · Z
* `S0` — averaged zeroth-moment risk-set weight
* `logPL` — normalized log partial likelihood
* `Ebar` — risk-set covariate average
* `scorePL` — score function (gradient of log partial likelihood)

## References

* D.R. Cox, "Regression models and life-tables", JRSS-B 34 (1972)
* P.K. Andersen & R.D. Gill, "Cox's regression model for counting
  processes: A large sample study", Ann. Statist. 10 (1982)
* T.R. Fleming & D.P. Harrington, "Counting Processes and Survival
  Analysis", Wiley (1991)
-/
import Mathlib

namespace Pythia.Survival

open Real BigOperators Finset

/-! ## Primitive survival indicators -/

/-- Observed time: X = min(T, C). -/
noncomputable def obsTime (T C : ℝ) : ℝ := min T C

/-- Event (failure) indicator: δ = 1{T ≤ C}.
    Returns 1 when the event is observed, 0 when censored. -/
noncomputable def eventInd (T C : ℝ) : ℝ := if T ≤ C then 1 else 0

/-- At-risk indicator: Y(t) = 1{t ≤ X}.
    Indicates whether a subject is still in the risk set at time t. -/
noncomputable def atRisk (X t : ℝ) : ℝ := if t ≤ X then 1 else 0

/-- Counting-process jump: dN(t) = 1{X ≤ t, δ = 1}.
    Counts whether the observed event has occurred by time t. -/
noncomputable def countJump (T C t : ℝ) : ℝ :=
  if obsTime T C ≤ t ∧ T ≤ C then 1 else 0

/-! ## Cox model regression quantities -/

variable {p : ℕ}

/-- Linear predictor β · Z = Σ_k β_k Z_k. -/
noncomputable def linPred (β Z : Fin p → ℝ) : ℝ := ∑ k, β k * Z k

/-- Averaged zeroth moment of the risk set:
    S⁰_n(β, t) = n⁻¹ Σ_{j<n} Y_j(t) exp(β · Z_j).
    This is the denominator (up to a factor n) in each term of the
    Cox partial likelihood. -/
noncomputable def S0 (n : ℕ) (β : Fin p → ℝ)
    (Z : ℕ → Fin p → ℝ) (X : ℕ → ℝ) (t : ℝ) : ℝ :=
  (↑n)⁻¹ * ∑ j ∈ range n, atRisk (X j) t * exp (linPred β (Z j))

/-- Normalized log partial likelihood (Cox, 1972):
    ℓ_n(β) = n⁻¹ Σ_{i<n} δ_i [ β · Z_i − log S⁰_n(β, X_i) ].

    Here X_i = obsTime (T i) (C i) and δ_i = eventInd (T i) (C i). -/
noncomputable def logPL (n : ℕ) (β : Fin p → ℝ)
    (Z : ℕ → Fin p → ℝ) (T C : ℕ → ℝ) : ℝ :=
  (↑n)⁻¹ * ∑ i ∈ range n,
    eventInd (T i) (C i) *
    (linPred β (Z i) -
     log (S0 n β Z (fun j => obsTime (T j) (C j)) (obsTime (T i) (C i))))

/-- Weighted average covariate in the risk set:
    Ē_n(β, t)_k = [Σ_{j<n} Y_j(t) Z_{jk} exp(β·Z_j)]
                 / [Σ_{j<n} Y_j(t) exp(β·Z_j)]
    This is S¹_n(β,t) / S⁰_n(β,t), component-wise. -/
noncomputable def Ebar (n : ℕ) (β : Fin p → ℝ)
    (Z : ℕ → Fin p → ℝ) (X : ℕ → ℝ) (t : ℝ) (k : Fin p) : ℝ :=
  (∑ j ∈ range n, atRisk (X j) t * Z j k * exp (linPred β (Z j))) /
  (∑ j ∈ range n, atRisk (X j) t * exp (linPred β (Z j)))

/-- Score function (gradient of log partial likelihood), component k:
    U_n(β)_k = n⁻¹ Σ_{i<n} δ_i [ Z_{ik} − Ē_n(β, X_i)_k ].

    At the true parameter β₀ under the proportional-hazards model,
    U_n(β₀) is a sum of martingale increments w.r.t. the
    counting-process filtration (Andersen–Gill, 1982). -/
noncomputable def scorePL (n : ℕ) (β : Fin p → ℝ)
    (Z : ℕ → Fin p → ℝ) (T C : ℕ → ℝ) (k : Fin p) : ℝ :=
  let X := fun j => obsTime (T j) (C j)
  (↑n)⁻¹ * ∑ i ∈ range n,
    eventInd (T i) (C i) * (Z i k - Ebar n β Z X (X i) k)

/-! ## Random-variable versions (for probability statements) -/

variable {Ω : Type*}

/-- Random log partial likelihood evaluated at sample ω:
    β ↦ ℓ_n(β, ω). -/
noncomputable def logPL_rv
    (Z : ℕ → Ω → Fin p → ℝ) (T C : ℕ → Ω → ℝ)
    (n : ℕ) (β : Fin p → ℝ) (ω : Ω) : ℝ :=
  logPL n β (fun i => Z i ω) (fun i => T i ω) (fun i => C i ω)

/-! ## Basic properties -/

lemma eventInd_nonneg (T C : ℝ) : 0 ≤ eventInd T C := by
  unfold eventInd; split_ifs <;> norm_num

lemma eventInd_le_one (T C : ℝ) : eventInd T C ≤ 1 := by
  unfold eventInd; split_ifs <;> norm_num

lemma eventInd_mem {T C : ℝ} : eventInd T C = 0 ∨ eventInd T C = 1 := by
  unfold eventInd; split_ifs <;> simp

lemma atRisk_nonneg (X t : ℝ) : 0 ≤ atRisk X t := by
  unfold atRisk; split_ifs <;> norm_num

lemma atRisk_le_one (X t : ℝ) : atRisk X t ≤ 1 := by
  unfold atRisk; split_ifs <;> norm_num

lemma obsTime_pos {T C : ℝ} (hT : 0 < T) (hC : 0 < C) :
    0 < obsTime T C := lt_min hT hC

lemma obsTime_le_T (T C : ℝ) : obsTime T C ≤ T := min_le_left T C

lemma obsTime_le_C (T C : ℝ) : obsTime T C ≤ C := min_le_right T C

/-- S⁰ is non-negative. -/
lemma S0_nonneg (n : ℕ) (β : Fin p → ℝ)
    (Z : ℕ → Fin p → ℝ) (X : ℕ → ℝ) (t : ℝ) :
    0 ≤ S0 n β Z X t := by
  unfold S0
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg
    · exact atRisk_nonneg _ _
    · exact le_of_lt (exp_pos _)

/-- The linear predictor is bilinear: linPred β Z = inner product. -/
lemma linPred_eq_inner (β Z : Fin p → ℝ) :
    linPred β Z = ∑ k, β k * Z k := rfl

end Pythia.Survival
