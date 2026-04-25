/-
Kairos.Stats.Tactic.StatsIneqTest — regression tests for the
`stats_ineq` tactic.

Each example must close in a single `stats_ineq` call. CI fails if any
example regresses, ensuring the tactic stays viable as a one-shot
domain hammer.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a kernel
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`,
no skipped tests.
-/
import Kairos.Stats.Tactic.StatsIneqRegistry

namespace Kairos.Stats.StatsIneqTest

open Kairos.Stats

/-- Sqrt monotonicity (Mathlib `@[bound]` rule). -/
example {x y : ℝ} (h : x ≤ y) : Real.sqrt x ≤ Real.sqrt y := by stats_ineq

/-- Sqrt monotonicity with a concrete LHS. -/
example {y : ℝ} (h : (0 : ℝ) ≤ y) : Real.sqrt 0 ≤ Real.sqrt y := by stats_ineq

/-- Log nonnegativity (Mathlib `@[bound]` rule). -/
example {x : ℝ} (h : 1 ≤ x) : 0 ≤ Real.log x := by stats_ineq

/-- Log subadditive bound `log x ≤ x` for `x ≥ 0`. -/
example {x : ℝ} (h : 0 ≤ x) : Real.log x ≤ x := by stats_ineq

/-- Asymptotic ≤ Howard–Ramdas ranking (kairos rule). -/
example (b : ℕ) (hb : 1 ≤ b) :
    etaAsymptotic b ≤ etaHR b := by stats_ineq

/-- Howard–Ramdas ≤ vector ranking (kairos rule, no side hypothesis). -/
example (b : ℕ) : etaHR b ≤ etaVector b := by stats_ineq

/-- Betting ≤ Howard–Ramdas ranking (kairos rule). -/
example (b : ℕ) (hb : 1 ≤ b) :
    etaBetting b ≤ etaHR b := by stats_ineq

/-- Sum of nonnegatives is nonnegative (positivity fall-through). -/
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by stats_ineq

/-- Product of nonnegatives is nonnegative (positivity fall-through). -/
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by stats_ineq

/-- Sqrt is nonnegative (positivity fall-through). -/
example (x : ℝ) : 0 ≤ Real.sqrt x := by stats_ineq

/-- Linear-arithmetic close-out (linarith fall-through). -/
example {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by stats_ineq

/-- Composite eta ranking via transitivity (linarith fall-through after
ranking applications). Uses the `Kairos.Stats` ranking lemmas as
hypotheses so the tactic can close via the `linarith` fall-through. -/
example (b : ℕ) (hb : 1 ≤ b) : etaBetting b ≤ etaVector b := by
  have h1 : etaBetting b ≤ etaHR b := etaBetting_le_etaHR b hb
  have h2 : etaHR b ≤ etaVector b := etaHR_le_etaVector b
  stats_ineq

end Kairos.Stats.StatsIneqTest

-- The `#stats_ineqs` command surfaces the registered rule set.
#stats_ineqs
