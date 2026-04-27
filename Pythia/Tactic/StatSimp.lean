/-
Pythia.Tactic.StatSimp — the `@[stat_simp]` curated simp-set and the
`stat_simp` tactic for ENNReal / probability normal-form rewriting.

A probability-aware normal form that core Mathlib `simp` does not carry
end-to-end. Concentration goals routinely leave residue mixing
`ENNReal.toReal`, `ENNReal.ofReal`, `Set.indicator`, and
`MeasureTheory.condExp` that `linarith` then cannot close. `stat_simp`
walks the expression once with a curated rule-set so that everything
reduces to `ℝ` plus boolean indicator + condExp side-conditions.

## Architecture

* `register_simp_attr stat_simp` — registers a *true* simp attribute
  (distinct from the `prob_simp` design which re-tags lemmas as
  `@[simp]` and so pollutes the global simp set). Lemmas are tagged
  `@[stat_simp]` and only fire when the user invokes the set
  explicitly via `simp only [stat_simp]` or the `stat_simp` tactic.

* `stat_simp` tactic — runs `simp only [stat_simp]` everywhere
  (`at *`) and falls through to `push_cast` / `norm_cast` for any
  residual ENNReal ↔ ℝ coercion.

The split is deliberate. `prob_simp` (companion module) is the
"pull-the-emergency-brake" tactic that includes both upstream `@[simp]`
lemmas and Pythia-specific ones via `@[simp]` re-tagging. `stat_simp`
is the *minimal, opt-in* normal form: callers know exactly which 40
lemmas it will apply, and adding a new lemma requires demonstrating no
loop on the fixture in `StatSimpTest.lean`.

## Membership criteria for `@[stat_simp]`

A lemma qualifies if all four hold:

1. Clear normalization direction (LHS is "less normal", RHS is "more
   normal"). For us, "more normal" means: prefer `ℝ` over `ℝ≥0∞`,
   prefer `if` over `indicator`, prefer constant fold (`measure univ`
   under `IsProbabilityMeasure` becomes `1`).
2. No loop. Verified by the 5x-fixed-point fixture in
   `StatSimpTest.lean`.
3. No expensive side condition. `condExp_const` requires
   `IsFiniteMeasure μ` (instance lookup, cheap) and `m ≤ m₀`
   (assumption discharge, cheap) — fine. `condExp_add` requires
   `Integrable f μ`, `Integrable g μ` — these are arbitrary
   propositions that block `simp` discharge, so excluded.
4. Already exists at Mathlib v4.28.0 (this repo's pin). Verified by
   direct grep under `.lake/packages/mathlib/Mathlib/`. See
   `StatSimpRegistry.lean` for the membership table including
   exclusions and reasoning.

## Lean-gating

Every `example` in `StatSimpTest.lean` reduces to a Lean kernel-checked
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
skipped tests. Per Aidan's 2026-04-25 directive.

## Driver

Companion to `pythia` (general hammer), `stats_ineq` (inequality
hammer), and `prob_simp` (PDF / probability-measure / coercion
specialist). `stat_simp` slots between `prob_simp` and `linarith` /
`nlinarith` in concentration-of-measure pipelines: rewrite to ℝ,
then close numerically.
-/
import Mathlib

namespace Pythia

/-- Simp set for the `stat_simp` tactic: probability + ENNReal normal
forms. See `Pythia.Tactic.StatSimpRegistry` for the curated list and
`Pythia.Tactic.StatSimpTest` for the no-loop fixture. -/
register_simp_attr stat_simp

end Pythia

namespace Pythia

open Lean Elab Meta Tactic

/-- `stat_simp` — pythia ENNReal / probability normal-form rewriter.

Runs `simp only [stat_simp]` against the curated rule-set tagged via
`@[stat_simp]`. Optional bracketed argument list `stat_simp [h₁, h₂]`
splices extra hypothesis terms into the same `simp only` invocation —
useful for discharging side conditions like `a ≠ ∞` or `0 ≤ p` that
appear on conditional `@[stat_simp]` lemmas.

Designed for the gap between concentration goal-shape and `linarith`
close-out where `simp` alone leaves `ENNReal.toReal (ENNReal.ofReal x)`
that `linarith` cannot see through. -/
syntax (name := statSimpTac)
  "stat_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

@[tactic statSimpTac] def evalStatSimp : Tactic := fun stx => do
  match stx with
  | `(tactic| stat_simp) =>
    evalTactic <| ← `(tactic| simp (discharger := assumption) only [stat_simp])
  | `(tactic| stat_simp [$args,*]) =>
    evalTactic <| ← `(tactic|
      simp (discharger := assumption) only [stat_simp, $args,*])
  | _ => throwUnsupportedSyntax

end Pythia
