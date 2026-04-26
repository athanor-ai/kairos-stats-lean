/-
Pythia.Tactic.StatsIneqRegistry — auto-tags a curated set of
monotonicity / inequality lemmas with `@[stats_ineq]`.

This file is split from `StatsIneq.lean` because Lean does not let a
freshly-`initialize`d builtin attribute be applied in the same module
that declares it. Mirrors the `CSFamilyAttr` ↔ `CSFamilyRegistry`
split.

Each lemma below is verified to exist in either Mathlib v4.28.0 or
the pythia library at this commit. Lemmas already carrying `@[bound]`
upstream (`Real.sqrt_le_sqrt`, `Real.log_nonneg`) are re-tagged here
so they appear in `#stats_ineqs`; re-applying `@[bound]` to the same
decl is a no-op.

## Lemmas requested by that do NOT exist at this commit

  • `Real.sqrt_add_le_sqrt_add_sqrt` — sqrt subadditivity
    `√(a + b) ≤ √a + √b`. Not in Mathlib v4.28.0 under this name.
    TODO: prove locally and tag once shipped.

  • `Pythia.etaBetting_le_etaAsymptotic` — does not exist at
    this commit. The composite `etaBetting ≤ etaAsymptotic` is proved
    as the first conjunct of `Pythia.ranking_four_way` but
    isn't a standalone named lemma. TODO: extract and tag once it
    lands as a top-level theorem.
-/
import Pythia.Tactic.StatsIneq

attribute [stats_ineq]
  Real.sqrt_le_sqrt
  Real.log_nonneg
  Real.log_le_self
  Pythia.etaAsymptotic_le_etaHR
  Pythia.etaHR_le_etaVector
  Pythia.etaBetting_le_etaHR
