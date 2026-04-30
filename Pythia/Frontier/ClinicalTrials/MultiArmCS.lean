/-
Pythia.Frontier.ClinicalTrials.MultiArmCS

Multi-arm anytime-valid confidence sequence — Phase C scaffold for
ATH-895 (clinical-trials theorem coverage).

## Goal

Compose K single-arm betting confidence sequences at level α/K via
the union bound to obtain a JOINT anytime-valid CS at level α for
the K-dimensional parameter (μ_1, …, μ_K).

## Theorem (informal)

Let `CS_1, …, CS_K` be K independent betting CS instances, each
`(α/K)`-anytime-valid for its own parameter `μ_k`. Then the cartesian
product

  `JointCS t = ⋂_k CS_k(t)`

is `α`-anytime-valid for the joint parameter `(μ_1, …, μ_K)`. By
Bonferroni / union bound:

  `P(∃ t, μ ∉ JointCS t) ≤ Σ_k P(∃ t, μ_k ∉ CS_k(t)) ≤ K · (α/K) = α`.

## Why this matters for clinical trials

K-arm clinical trials need a CS that controls the family-wise
coverage error across arms simultaneously, with ANY-TIME stopping
(not just at a fixed sample size). The Bonferroni split is the
simplest valid construction; tighter constructions (e-process
intersection, Fisher combination) come later.

## Status

**Honest sorries — Phase C scaffold.** The structures + headline
statement are written; the union-bound calculation is left as an
explicit `sorry` with a closure-plan comment. Closure path:

1. Lift `Pythia.bettingStoppingRule_admissible` to a per-arm e-process.
2. Apply `MeasureTheory.measure_iUnion_le` for finite K.
3. Reduce `K · (α/K) = α` by ring.

Will graduate to mainline + register in `Pythia.Lookup` with
goal-class `clinical_trials.multi_arm.union_bound` once sorries
close.

## Driver

ATH-895 (Pythia clinical-trials theorem coverage). Filed under
ATH-894 (cross-vertical MCP router) for the clinical-trial-statistician
persona.
-/
import Mathlib
import Pythia.BettingCS

namespace Pythia.Frontier.ClinicalTrials

open MeasureTheory ProbabilityTheory

/-- A K-arm anytime-valid CS family. Each arm `k : Fin K` carries its
own `(α/K)`-anytime-valid betting CS, so the joint CS at level `α`
follows by union bound.

The structure is parametric in the per-arm CS witness (any
admissibility-tagged stopping rule); v0 fixes the betting CS family
since it has the tightest known constants. -/
structure MultiArmBettingCS (K : ℕ) (alpha : ℝ) where
  /-- α is in (0, 1). -/
  alpha_mem : 0 < alpha ∧ alpha < 1
  /-- K ≥ 1 (at least one arm). -/
  arms_nonempty : 1 ≤ K
  /-- Per-arm boundary: each arm uses its own α/K Bonferroni split. -/
  perArmLevel : ℝ := alpha / (K : ℝ)
  /-- Boundary positivity: α/K > 0 follows from α > 0 and K ≥ 1. -/
  perArmLevel_pos : 0 < perArmLevel := by
    -- Reduces to: 0 < alpha / K, given 0 < alpha and 1 ≤ K
    sorry

/-- The joint coverage error under K-arm Bonferroni Bonferroni split.

**Statement (informal):** if every arm's per-arm CS is
`(α/K)`-anytime-valid for its own parameter, then the JOINT CS
(parameter-wise intersection across arms) has coverage error
bounded by `α` uniformly over time.

**Closure plan:**
1. For each arm `k`, lift the per-arm betting-CS admissibility to a
   non-coverage event `E_k = {∃ t, μ_k ∉ CS_k(t)}` with
   `μ E_k ≤ α/K` (this is `bettingStoppingRule_admissible` applied
   per arm).
2. The joint non-coverage event is `E = ⋃_k E_k`.
3. By `measure_iUnion_le_of_measurable` (or finite countable
   sub-additivity for `Fin K`), `μ E ≤ Σ_k μ E_k ≤ K · (α/K) = α`.
4. The arithmetic reduction is `Finset.sum_const + ring`.

The sorry below is the entire (3) + (4) calculation. (1) and (2)
are stable once the per-arm structure is fixed. -/
theorem multi_arm_admissible
    {K : ℕ} {alpha : ℝ} (M : MultiArmBettingCS K alpha) :
    -- Headline claim (informal): joint coverage error ≤ alpha.
    -- We state a placeholder real-valued inequality that will be
    -- replaced with the formal probabilistic statement once the
    -- per-arm e-process lifting is wired.
    K * M.perArmLevel ≤ alpha + 1 := by
  -- Once the per-arm e-process lifting lands, the headline rewrites
  -- to: μ {∃ t k, μ_k ∉ CS_k(t)} ≤ α. The placeholder here keeps the
  -- statement compiling while the dependency chain is being built.
  -- See module docstring for closure plan.
  sorry

/-- Sanity: the per-arm Bonferroni split sums to exactly α. This is
the algebraic core of the union-bound argument; keeping it as a
named lemma makes the eventual `multi_arm_admissible` proof one
line of `linarith`. -/
theorem perArmLevel_sum_eq_alpha
    {K : ℕ} {alpha : ℝ} (M : MultiArmBettingCS K alpha) :
    K * M.perArmLevel = alpha := by
  -- M.perArmLevel = alpha / K, and K ≥ 1, so K * (alpha / K) = alpha
  -- follows from field_simp / mul_div_cancel.
  sorry

end Pythia.Frontier.ClinicalTrials
