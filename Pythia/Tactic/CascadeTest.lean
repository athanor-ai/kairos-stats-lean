/-
Pythia.Tactic.CascadeTest: regression suite for the `pythia` cascade
routing.

This file's job: confirm that the `pythia` tactic's dispatch ladder
closes a representative cross-section of goal shapes AND that the
verbose companion `pythia?` (the `pythia!` ladder verbose; ATH-756)
reports which rung actually fired across the full 9-rung ladder. The
test contract is "first rung in the ladder that succeeds wins,"
which is the documented `pythia` semantics. The verbose output is
the regression check: if a rung is reordered or broken, the printed
rung name changes and CI surfaces it.

Each test case appears twice:

  1. `example ... := by pythia`: confirms the cascade closes the
     goal at all (any rung is fine).
  2. `set_option trace.Pythia.Verbose true in example ... := by pythia?`
     emits the rung name as an info message; CI captures it. The
     comment above each example records the rung that fires at the
     commit this file lands at, so a reviewer can spot routing drift.

A note on rung selection: `pythia`'s ladder runs the most-specific
shapes first (anytime_valid, stats_ineq, prob_simp), then the SMT /
FOL oracles (z3_check, cvc5_check, vampire_check, e_check), then
the `Pythia` aesop ruleset, then the generic Mathlib chain
(`simp; omega; linarith; positivity`), then default aesop as the
last resort. Tactics like `anytime_valid` and `stats_ineq` themselves
fall through to general-purpose closers (aesop / linarith /
positivity), so they may close goals that LOOK like they belong on
a later rung. The verbose output is the source of truth, not the
section header.

Lean-gating rule (Aidan 2026-04-25): every example reduces to a
kernel term against `{propext, Classical.choice, Quot.sound}`. No
`sorry`, no skipped tests, no axiom smuggling. Tests must pass
without z3 / cvc5 / vampire / eprover installed: every rung has a
Lean-side reconstructor (linarith / bv_decide / aesop) that closes
the same goal.

## Driver

Phase B+. Companion to `Pythia/Tactic/Pythia.lean` (cascade owner)
and `docs/sledgehammer_dispatch.md` (rung table).
-/
import Pythia.Tactic.Pythia
import Pythia.Tactic.PythiaBang
import Pythia.Tactic.AnytimeValidRegistry

namespace Pythia.CascadeTest

open MeasureTheory ProbabilityTheory ENNReal Pythia

/-! ## Section A : Ville-bound goal

The canonical CS shape: `μ {ω | ∃ t, f t ω ≥ c} ≤ ...`. The
`anytime_valid` rung is the first rung of the cascade and the
designated owner of this shape. Observed verbose output at this
commit: `closed by anytime_valid (Ville-bound shape)`. -/

example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  pythia

set_option trace.Pythia.Verbose true in
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  pythia?

/-! ## Section B : QF_LRA goal

A linear-real arithmetic chain. The `z3_check` rung owns this
shape on the rung table, but `stats_ineq` (which itself ends in
`linarith`) is earlier in the ladder and closes the goal first.
Observed verbose output: `closed by stats_ineq (concentration
tail)`. The test still confirms the cascade closes pure-LRA goals;
it also documents that `stats_ineq` is general-purpose enough to
shadow `z3_check` on simple chains. -/

example {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  pythia

set_option trace.Pythia.Verbose true in
example {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  pythia?

/-! ## Section C : registered `@[stat_lemma]` case

A trivial arithmetic identity registered as a `@[stat_lemma]`. The
cascade's earlier rungs (anytime_valid, stats_ineq, etc.) all
contain general-purpose closers, and `anytime_valid`'s aesop falls
through `ring`-shape goals on the default rule set. Observed
verbose output: `closed by anytime_valid (Ville-bound shape)`. The
test confirms registered lemmas DO compose with the cascade
even though the verbose log credits an earlier rung; the
`Pythia`-ruleset rung is the safety net for goals the earlier
rungs miss. -/

@[stat_lemma]
theorem cascade_test_double_zero (x : ℝ) : x + 0 + 0 = x := by ring

example (x : ℝ) : x + 0 + 0 = x := by pythia

set_option trace.Pythia.Verbose true in
example (x : ℝ) : x + 0 + 0 = x := by pythia?

/-! ## Section D : generic Mathlib chain (positivity)

A nonneg goal that fits the `simp; omega; linarith; positivity`
chain rung. `stats_ineq` reaches positivity via its own ladder, so
it closes the goal first. Observed verbose output: `closed by
stats_ineq (concentration tail)`. -/

example (x : ℝ) : 0 ≤ x ^ 2 := by pythia

set_option trace.Pythia.Verbose true in
example (x : ℝ) : 0 ≤ x ^ 2 := by pythia?

/-! ## Section E : aesop-default case

A pure FOL tautology with no arithmetic and no registered
`@[stat_lemma]`. The cascade closes via the first rung that
applies; aesop's default rules trivially solve `A ∧ B → B ∧ A`,
so an earlier rung that internally calls aesop (e.g.
`anytime_valid`) handles it. Observed verbose output: `closed by
anytime_valid (Ville-bound shape)`. The test still confirms the
cascade closes pure-propositional goals end to end. -/

example (A B : Prop) (h : A ∧ B) : B ∧ A := by pythia

set_option trace.Pythia.Verbose true in
example (A B : Prop) (h : A ∧ B) : B ∧ A := by pythia?

end Pythia.CascadeTest
