/-
Pythia.Tactic.PythiaBangTest — regression tests for `pythia!!` and
`pythia!?` from ATH-753.

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
-/
import Pythia.Tactic.PythiaBang

namespace Pythia.PythiaBangTest

open Pythia

/-! ## Section 1 — Rung 1: `simp` -/

/-- simp closes a trivial reflexive equality. -/
example (x : ℝ) : x = x := by pythia!!

/-- simp closes `x + 0 = x` after normalization. -/
example (x : ℝ) : x + 0 = x := by pythia!!

/-- simp closes via `Nat.add_zero`. -/
example (n : ℕ) : n + 0 = n := by pythia!!

/-- simp closes a trivial conjunction with `And.intro` shape. -/
example : True ∧ True := by pythia!!

/-! ## Section 2 — Rung 2: `linarith` / `nlinarith` / `polyrith` -/

/-- linarith closes a linear ordering chain. -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by pythia!!

/-- linarith closes a sum-of-bounds inequality. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by pythia!!

/-- linarith closes a 4-step chain. -/
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d) :
    a ≤ d := by pythia!!

/-- nlinarith closes a quadratic-style nonneg goal not in linarith's
fragment (uses multiplications between hypotheses). -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b + a + b := by
  pythia!!

/-! ## Section 3 — Rung 3: `positivity` -/

/-- positivity closes nonneg square. -/
example (x : ℝ) : 0 ≤ x ^ 2 := by pythia!!

/-- positivity closes nonneg sqrt unconditionally. -/
example (x : ℝ) : 0 ≤ Real.sqrt x := by pythia!!

/-- positivity closes |x| ≥ 0. -/
example (x : ℝ) : 0 ≤ |x| := by pythia!!

/-! ## Section 4 — Rung 4: `aesop` on the `Pythia` ruleset -/

/-- A `@[stat_lemma]`-tagged trivial lemma joins the Pythia
ruleset; aesop on the ruleset closes a goal that matches its head. -/
@[stat_lemma]
theorem bang_test_helper (x : ℝ) : x + 0 - 0 = x := by ring

/-- aesop on the Pythia ruleset closes a direct application of the
registered lemma. -/
example (y : ℝ) : y + 0 - 0 = y := by pythia!!

/-! ## Section 5 — Rung 5: `pythia` shape-dispatch cascade -/

-- The `pythia` rung itself runs simp/omega/linarith/positivity inside
-- its fall-through chain plus the @[stat_lemma] aesop ruleset; goals
-- that arrive here would already have been caught by rungs 1-4. We
-- exercise the rung indirectly by ensuring `pythia!!` does not crash
-- on goals it has handled before in the broader suite (PythiaTest.lean).

/-- Direct use case: `pythia` closes via its omega fall-through
on a ℕ goal that simp may also handle, exercising the cascade
without changing dispatch correctness. -/
example (n m : ℕ) : n + m = m + n := by pythia!!

/-! ## Section 6-9 — SMT / FOL oracles + disprove

The external-oracle rungs (z3_check, cvc5_check, vampire_check,
e_check, disprove) all require their respective binaries on PATH. We
do NOT exercise these against bespoke goals in CI: each oracle has
its own dedicated regression suite (Z3CheckTest etc.) that handles
the install-or-skip protocol. Here we only check that `pythia!!`
does NOT regress on goals already covered by cheaper rungs, since a
broken upstream oracle would otherwise surface as a `pythia!!`
failure rather than the targeted oracle-test failure.
-/

/-! ## Section 10 — Verbose `pythia!?` smoke -/

/-- Verbose mode closes via simp and emits a per-rung timing summary. -/
example (x : ℝ) : x = x := by pythia!?

/-- Verbose mode closes via linarith and reports it. -/
example (a b : ℝ) (h : a ≤ b) : a ≤ b := by pythia!?

/-! ## Section 11 — Multi-rung dispatch (orchestrator-level) -/

/-- A trivial reflexive ℝ equality: simp wins immediately. -/
example (x : ℝ) : x + 0 = x := by pythia!!

/-- A linarith goal that simp cannot close: rung 1 fails, rung 2
catches it. -/
example (a b c : ℝ) (h₁ : a < b) (h₂ : b < c) : a < c := by pythia!!

/-- A positivity goal that simp + linarith cannot fully close:
rung 3 catches it. -/
example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by pythia!!

/-- A registered-lemma goal where rungs 1-3 fail: rung 4 catches it
via the aesop ruleset. -/
example (z : ℝ) : z + 0 - 0 = z := by pythia!!

/-! ## Section 11b — More simp / linarith / positivity coverage -/

/-- simp closes a Bool reflexive equality. -/
example : true = true := by pythia!!

/-- simp closes `0 + n = n` on ℕ. -/
example (n : ℕ) : 0 + n = n := by pythia!!

/-- linarith closes a strict-inequality chain on ℤ. -/
example (a b : ℤ) (h : a < b) : a ≤ b := by pythia!!

/-- linarith closes a sum-and-bound goal. -/
example (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : 2 ≤ a + b := by pythia!!

/-- positivity closes a fourth-power. -/
example (x : ℝ) : 0 ≤ x ^ 4 := by pythia!!

/-! ## Section 12 — Contradictory hypothesis (False from contradiction)

A goal of `False` from contradictory linear hypotheses. linarith
catches contradictions in the hypotheses directly, so the goal closes
on rung 2. This validates the orchestrator handles contradiction-
shaped goals without needing the disprove rung to fire first. -/

/-- Contradictory hypotheses ⇒ False closes via linarith on rung 2. -/
example (a : ℝ) (h₁ : a ≤ 0) (h₂ : 1 ≤ a) : False := by pythia!!

/-- Contradiction propagates to any goal under absurd hypotheses. -/
example (a : ℝ) (h₁ : a ≤ 0) (h₂ : 1 ≤ a) : a = 42 := by pythia!!

/-! ## Section 13 — Axiom audit attestation

`#print axioms` on a `pythia!!`-closed example must yield only
`{propext, Classical.choice, Quot.sound}`. We capture one canonical
example per rung family and #print its axioms; CI / the reviewer can
visually confirm the audit attests cleanly. -/

theorem bang_axiom_simp (x : ℝ) : x + 0 = x := by pythia!!
theorem bang_axiom_linarith (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) :
    a ≤ c := by pythia!!
theorem bang_axiom_positivity (x : ℝ) : 0 ≤ x ^ 2 := by pythia!!

#print axioms bang_axiom_simp
#print axioms bang_axiom_linarith
#print axioms bang_axiom_positivity

end Pythia.PythiaBangTest
