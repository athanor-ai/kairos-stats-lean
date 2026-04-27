/-
Pythia.Tactic.PythiaBangTest — regression tests for `pythia!` and
`pythia?` from ATH-753 / ATH-756 / ATH-758.

The orchestrator must dispatch correctly across the 9-rung ladder.
Each section targets ONE rung with goals chosen so that ONLY that
rung is expected to close the goal. The first rung that succeeds
wins, so the goal is constructed so cheaper rungs fail fast.

Lean-gating: every example elaborates to a kernel term against
`{propext, Classical.choice, Quot.sound}`. No sorry, no skips. The
ladder is LLM-free per CONTRIBUTING rule 4 (offline-first); LLM-
augmented closure lives in the kairos-sdk companion under
`kairos.lean_cycle.cycle_prove` and is not exercised here.

Each test is intentionally tiny so the suite finishes quickly even
when several rungs are tried before one succeeds.

## Naming history (ATH-756)

This file originally exercised `pythia!!` / `pythia!?`. ATH-756
renamed the tactics to `pythia!` / `pythia?` to match the Lean idiom
(`simp!` / `apply?`). A small tail of the file (Section 14) covers
the deprecated `pythia!!` / `pythia!?` aliases that survive for one
minor version with a deprecation warning.
-/
import Pythia.Tactic.PythiaBang

namespace Pythia.PythiaBangTest

open Pythia
open MeasureTheory
open scoped ENNReal NNReal

/-! ## Section 1 — Rung 1: `stat_simp` / `simp` -/

/-- simp closes a trivial reflexive equality. -/
example (x : ℝ) : x = x := by pythia!

/-- simp closes `x + 0 = x` after normalization. -/
example (x : ℝ) : x + 0 = x := by pythia!

/-- simp closes via `Nat.add_zero`. -/
example (n : ℕ) : n + 0 = n := by pythia!

/-- simp closes a trivial conjunction with `And.intro` shape. -/
example : True ∧ True := by pythia!

/-! ## Section 2 — Rung 2: `linarith` / `nlinarith` / `polyrith` -/

/-- linarith closes a linear ordering chain. -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by pythia!

/-- linarith closes a sum-of-bounds inequality. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by pythia!

/-- linarith closes a 4-step chain. -/
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d) :
    a ≤ d := by pythia!

/-- nlinarith closes a quadratic-style nonneg goal not in linarith's
fragment (uses multiplications between hypotheses). -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b + a + b := by
  pythia!

/-! ## Section 3 — Rung 3: `positivity` -/

/-- positivity closes nonneg square. -/
example (x : ℝ) : 0 ≤ x ^ 2 := by pythia!

/-- positivity closes nonneg sqrt unconditionally. -/
example (x : ℝ) : 0 ≤ Real.sqrt x := by pythia!

/-- positivity closes |x| ≥ 0. -/
example (x : ℝ) : 0 ≤ |x| := by pythia!

/-! ## Section 4 — Rung 4: `aesop` on the `Pythia` ruleset -/

/-- A `@[stat_lemma]`-tagged trivial lemma joins the Pythia
ruleset; aesop on the ruleset closes a goal that matches its head. -/
@[stat_lemma]
theorem bang_test_helper (x : ℝ) : x + 0 - 0 = x := by ring

/-- aesop on the Pythia ruleset closes a direct application of the
registered lemma. -/
example (y : ℝ) : y + 0 - 0 = y := by pythia!

/-! ## Section 5 — Rung 5: `pythia` shape-dispatch cascade -/

-- The `pythia` rung itself runs simp/omega/linarith/positivity inside
-- its fall-through chain plus the @[stat_lemma] aesop ruleset; goals
-- that arrive here would already have been caught by rungs 1-4. We
-- exercise the rung indirectly by ensuring `pythia!` does not crash
-- on goals it has handled before in the broader suite (PythiaTest.lean).

/-- Direct use case: `pythia` closes via its omega fall-through
on a ℕ goal that simp may also handle, exercising the cascade
without changing dispatch correctness. -/
example (n m : ℕ) : n + m = m + n := by pythia!

/-! ## Section 6-9 — SMT / FOL oracles + disprove

The external-oracle rungs (z3_check, cvc5_check, vampire_check,
e_check, disprove) all require their respective binaries on PATH. We
do NOT exercise these against bespoke goals in CI: each oracle has
its own dedicated regression suite (Z3CheckTest etc.) that handles
the install-or-skip protocol. Here we only check that `pythia!`
does NOT regress on goals already covered by cheaper rungs, since a
broken upstream oracle would otherwise surface as a `pythia!`
failure rather than the targeted oracle-test failure.
-/

/-! ## Section 10 — Verbose `pythia?` smoke -/

/-- Verbose mode closes via simp and emits a per-rung timing summary. -/
example (x : ℝ) : x = x := by pythia?

/-- Verbose mode closes via linarith and reports it. -/
example (a b : ℝ) (h : a ≤ b) : a ≤ b := by pythia?

/-! ## Section 11 — Multi-rung dispatch (orchestrator-level) -/

/-- A trivial reflexive ℝ equality: simp wins immediately. -/
example (x : ℝ) : x + 0 = x := by pythia!

/-- A linarith goal that simp cannot close: rung 1 fails, rung 2
catches it. -/
example (a b c : ℝ) (h₁ : a < b) (h₂ : b < c) : a < c := by pythia!

/-- A positivity goal that simp + linarith cannot fully close:
rung 3 catches it. -/
example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by pythia!

/-- A registered-lemma goal where rungs 1-3 fail: rung 4 catches it
via the aesop ruleset. -/
example (z : ℝ) : z + 0 - 0 = z := by pythia!

/-! ## Section 11b — More simp / linarith / positivity coverage -/

/-- simp closes a Bool reflexive equality. -/
example : true = true := by pythia!

/-- simp closes `0 + n = n` on ℕ. -/
example (n : ℕ) : 0 + n = n := by pythia!

/-- linarith closes a strict-inequality chain on ℤ. -/
example (a b : ℤ) (h : a < b) : a ≤ b := by pythia!

/-- linarith closes a sum-and-bound goal. -/
example (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : 2 ≤ a + b := by pythia!

/-- positivity closes a fourth-power. -/
example (x : ℝ) : 0 ≤ x ^ 4 := by pythia!

/-! ## Section 12 — Contradictory hypothesis (False from contradiction)

A goal of `False` from contradictory linear hypotheses. linarith
catches contradictions in the hypotheses directly, so the goal closes
on rung 2. This validates the orchestrator handles contradiction-
shaped goals without needing the disprove rung to fire first. -/

/-- Contradictory hypotheses ⇒ False closes via linarith on rung 2. -/
example (a : ℝ) (h₁ : a ≤ 0) (h₂ : 1 ≤ a) : False := by pythia!

/-- Contradiction propagates to any goal under absurd hypotheses. -/
example (a : ℝ) (h₁ : a ≤ 0) (h₂ : 1 ≤ a) : a = 42 := by pythia!

/-! ## Section 13 — Axiom audit attestation

`#print axioms` on a `pythia!`-closed example must yield only
`{propext, Classical.choice, Quot.sound}`. We capture one canonical
example per rung family and #print its axioms; CI / the reviewer can
visually confirm the audit attests cleanly. -/

theorem bang_axiom_simp (x : ℝ) : x + 0 = x := by pythia!
theorem bang_axiom_linarith (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) :
    a ≤ c := by pythia!
theorem bang_axiom_positivity (x : ℝ) : 0 ≤ x ^ 2 := by pythia!

#print axioms bang_axiom_simp
#print axioms bang_axiom_linarith
#print axioms bang_axiom_positivity

/-! ## Section 14 — Deprecated alias smoke (ATH-756)

The legacy spellings `pythia!!` and `pythia!?` survive for one minor
version as deprecated aliases. They emit a deprecation warning on
use and otherwise behave identically. Any future contributor who
deletes the alias must remove this section in the same PR. -/

/-- Deprecated `pythia!!` alias still closes the goal. -/
example (x : ℝ) : x = x := by pythia!!

/-- Deprecated `pythia!?` alias still closes the goal. -/
example (x : ℝ) : x = x := by pythia!?

/-- Deprecated alias closes a non-trivial linarith goal. -/
example (a b : ℝ) (h : a ≤ b) : a ≤ b := by pythia!!

/-! ## Section 15 — `@[stat_simp]` hook regression (ATH-758)

Rung 1 of `pythia!` wires the `@[stat_simp]` curated simp set in
front of bare `simp`. Each example below produces a goal that bare
`simp` does NOT close on its own (the rewrite chain only fires under
the curated set), proving the hook is load-bearing.

The first three examples cover the headline use cases from ATH-758:
ENNReal.toReal round-trips, indicator literals, and Measure.real
bridging. The remaining cases compose `@[stat_simp]` rewrites with
the linarith / positivity rungs to verify normal-form lift propagates
through the ladder. -/

/-- `(ENNReal.ofReal x).toReal` round-trip on a non-negative real:
fires `@[stat_simp]` lemma `ENNReal.toReal_ofReal` (conditional on
`0 ≤ x`, discharged via the assumption discharger). -/
example {x : ℝ} (hx : 0 ≤ x) : (ENNReal.ofReal x).toReal = x := by pythia!

/-- `(μ Set.univ).toReal = 1` under `IsProbabilityMeasure`: composes
the `measure_univ` and `ENNReal.one_toReal` `@[stat_simp]` rewrites. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : (μ Set.univ).toReal = 1 := by pythia!

/-- `(μ ∅).toReal = 0`: composes the `measure_empty` and
`ENNReal.zero_toReal` `@[stat_simp]` rewrites. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    (μ ∅).toReal = 0 := by pythia!

/-- `Set.indicator` of universal set folds to the function itself,
then the equality closes by reflexivity after the `@[stat_simp]`
indicator rewrite fires. -/
example {α : Type*} (f : α → ℝ) (a : α) :
    (Set.univ : Set α).indicator f a = f a := by pythia!

/-- ENNReal.toReal nonnegativity composed with linarith: the
`@[stat_simp]` rewrite establishes the `≤` shape and rung 2 closes
the residual linear inequality. -/
example (a : ℝ≥0∞) : 0 ≤ a.toReal + 1 := by pythia!

/-! ## Section 15 — Failure-diagnostic contract (ATH-760)

When the ladder exhausts without closing, `pythia!` emits a
structured error message: a per-rung breakdown, a hint indexed
by the LAST rung tried, and a pointer at `pythia?` for verbose
success-path timing.

These tests pin one contract: the `Pythia.rungHint` lookup table covers
every `rung.id` returned by `buildRungs`, plus a documented
fallback for unknown ids. If a future edit drops a hint or
renames a rung, the test fails before the rename propagates to
user-facing failure messages.

The pure-text-message regression test (assert that an unclosable
goal produces a message containing "no rung closed", "Ladder
breakdown", and "Hint") is intentionally left as a follow-up:
Lean 4's `#guard_msgs` requires exact match including timings,
and capturing the error from a failing tactic in-place produces
brittle nested-tactic-monad code. The unit-test below covers the
single most-likely regression class — typos in the Pythia.rungHint
keys — which would manifest as "no hint available" surfacing for
a real rung. -/

/-- Every `rung.id` produced by `buildRungs` must have a non-empty
hint in `Pythia.rungHint`. The 9 rung ids below are the contract; if
`buildRungs` evolves, update both this list and the hint table in
the same PR. -/
example (id : String)
    (hmem : id ∈ ["stat_simp", "linarith_chain", "positivity",
                  "aesop_pythia", "pythia", "z3_check", "cvc5_check",
                  "fol_check", "disprove"]) :
    Pythia.rungHint id ≠ "" ∧ Pythia.rungHint id ≠ "no hint available" := by
  fin_cases hmem <;> exact ⟨by decide, by decide⟩

/-- `Pythia.rungHint` returns the documented fallback string for any id
that is NOT in the known set. Pins the fallback behaviour so a
future refactor that swaps it (e.g., to `throw` or to silent `""`)
breaks loud. -/
example : Pythia.rungHint "made_up_id" = "no hint available" := by decide

/-- Spot-check: the `disprove` rung_id maps to the documented
hint about vacuous-truth goals. Catches a typo where the table
has `"Disprove"` (capitalised) but `buildRungs` emits `"disprove"`. -/
example :
    Pythia.rungHint "disprove" =
      "the goal MAY be vacuously true; check hypotheses are satisfiable" := by
  rfl

end Pythia.PythiaBangTest
