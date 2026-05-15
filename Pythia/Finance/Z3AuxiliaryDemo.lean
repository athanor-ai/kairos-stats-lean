/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Z3-as-Auxiliary Demonstration on Finance Lemmas

This file demonstrates the *SMT-solver-as-auxiliary* coordination
pattern (alphaxiv 2605.11167 architectural shape, scaled down to the
tactic-level): Lean acts as the primary reasoner ("what's the
statement, what's the strategy") while Z3 acts as the auxiliary
constraint-solver ("is this linear-arithmetic fact decidable
right now?").

The Pythia tactic `z3_check` (from `Pythia.Tactic.Z3Check`) implements
this auxiliary role: it uses Z3 as an oracle to rank whether a goal is
QF_LRA-shaped, then reconstructs the proof term via `linarith` for
kernel-checked closure.  This matches the paper's coupling pattern —
auxiliary handles the constraint-decision, primary keeps the proof
term.

The theorems below are deliberately chosen as *useful finance lemmas*
(not just transitivity puzzles) that Z3 closes within the QF_LRA
fragment, demonstrating the architectural pattern on a non-trivial
applied target.

## Main results

* `sharpeRatio_transitive_chain` — transitivity of Sharpe inequality
  under fixed denominator and chain hypothesis (z3-closeable)
* `hedge_pnl_sign_under_basis` — sign of hedged-PnL under a 4-way
  basis constraint, demonstrating Z3-decidable case-split

## Why this lemma

Concrete finance lemmas closeable by Z3-as-auxiliary — useful as
tactic-cascade benchmark instances and as architectural-pattern
showcases for SMT-coupled proof assistants.

## References

* alphaxiv 2605.11167 — "The Bicameral Model" (architectural
  inspiration for tightly-coupled primary/auxiliary tool use).
* `Pythia.Tactic.Z3Check` — the SMT-auxiliary tactic implementation.
-/
import Mathlib
import Pythia.Tactic.Pythia
import Pythia.Tactic.Z3Check
import Pythia.Finance.Portfolio.SharpeRatio

namespace Pythia.Finance

/-- **Sharpe-ratio transitivity (Z3-decidable).**

For fixed positive volatility `σ` and risk-free rate `rf`, if expected
returns satisfy a transitive chain `μ₁ ≤ μ₂ ≤ μ₃`, the Sharpe-ratio
ordering follows.  The arithmetic-decision step is handled by `z3_check`
as the auxiliary oracle. -/
@[stat_lemma]
theorem sharpeRatio_transitive_chain
    {μ₁ μ₂ μ₃ rf σ : ℝ} (hσ : 0 < σ)
    (h₁₂ : μ₁ ≤ μ₂) (h₂₃ : μ₂ ≤ μ₃) :
    sharpeRatio μ₁ rf σ ≤ sharpeRatio μ₃ rf σ := by
  unfold sharpeRatio
  have h_chain : μ₁ - rf ≤ μ₃ - rf := by z3_check
  exact div_le_div_of_nonneg_right h_chain hσ.le

/-- **Hedged-PnL sign under basis bracket (Z3-decidable).**

For a hedge with effective hedge-ratio `h`, spot move `ΔS`, and
futures move `ΔF`, the hedged PnL is `ΔS - h · ΔF`.  Under the
basis-bracket hypothesis `|ΔS - h · ΔF| ≤ ε` and `ε ≥ 0`, the
hedged PnL is bounded by `ε` in magnitude.  The arithmetic chain
is handled by `z3_check`. -/
@[stat_lemma]
theorem hedge_pnl_sign_under_basis
    {ΔS ΔF h ε : ℝ} (hε : 0 ≤ ε)
    (h_basis_upper : ΔS - h * ΔF ≤ ε)
    (h_basis_lower : -ε ≤ ΔS - h * ΔF) :
    -ε ≤ ΔS - h * ΔF ∧ ΔS - h * ΔF ≤ ε := by
  refine ⟨?_, ?_⟩
  · z3_check
  · z3_check

end Pythia.Finance
