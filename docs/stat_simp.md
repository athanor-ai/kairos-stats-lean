# `stat_simp`: ENNReal / probability normal-form simp set

A curated `simp` attribute and tactic for the gap between
concentration-of-measure goals and `linarith` / `nlinarith` close-out.
`stat_simp` rewrites a goal into the team's "normal form": prefer `ℝ`
over `ℝ≥0∞`, prefer `if` over `Set.indicator`, fold every `μ univ` for
`IsProbabilityMeasure μ` to `1`. Once the rewrite is done, ordinary
real-number arithmetic tactics can close.

## What's in the set

39 lemmas tagged via the `@[stat_simp]` attribute, organized by
category. The full list lives in
[`Pythia/Tactic/StatSimpRegistry.lean`](../Pythia/Tactic/StatSimpRegistry.lean);
the membership criteria and exclusions are documented in the same
file's docstring.

| Category | Lemma count | Examples |
|----------|-------------|----------|
| ENNReal `toReal` normalization | 12 | `toReal_one`, `toReal_mul`, `toReal_add`, `toReal_ofReal` |
| ENNReal `ofReal` round-trips | 9 | `ofReal_zero`, `ofReal_pos`, `ofReal_le_ofReal_iff` |
| NNReal coercions | 3 | `toNNReal_one`, `toNNReal_zero`, `toNNReal_top` |
| Probability measure axioms | 3 | `IsProbabilityMeasure.measure_univ`, `measure_empty`, `coe_toOuterMeasure` |
| `Measure.real` | 4 | `measureReal_zero`, `measureReal_empty`, `probReal_univ` |
| Indicator function | 4 | `indicator_of_mem`, `indicator_of_notMem`, `indicator_univ`, `indicator_empty` |
| Conditional expectation | 2 | `condExp_zero`, `condExp_const` |
| Integral zero-measure shortcuts | 2 | `integral_zero_measure`, `lintegral_zero_measure` |

Total: 12 + 9 + 3 + 3 + 4 + 4 + 2 + 2 = 39.

Each lemma was verified against Mathlib v4.28.0 (this repo's pinned
toolchain) by direct grep under `.lake/packages/mathlib/Mathlib/`.

## When to use `stat_simp` vs core `simp`

| Tactic | Pulls from | Use for |
|--------|------------|---------|
| `simp` | global simp set (~thousands) | catch-all default |
| `simp only [...]` | exactly the listed lemmas | known-rewrite isolated normalization |
| `prob_simp` | global simp + Pythia-tagged via `@[prob_simp]` | PDF / probability-measure / coercion goals where the rewrite path is unknown |
| `stat_simp` | exactly the 40 `@[stat_simp]` lemmas | when you need a probability-aware normal form but want to know exactly which 40 rules will fire |

The defining property of `stat_simp` is that the rule set is small,
audited, and loop-free. Reaching for it instead of `simp` gives
predictable proof terms that survive future Mathlib simp-set churn.

## How to use

Plain form:

```lean
example (a b : ℝ≥0∞) : (a * b).toReal = a.toReal * b.toReal := by stat_simp
```

With side-condition hypotheses (passed through to the simp discharger
via `assumption`):

```lean
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
    (a + b).toReal = a.toReal + b.toReal := by stat_simp [ha, hb]
```

Equivalent direct form (useful when calling from a larger tactic):

```lean
simp (discharger := assumption) only [stat_simp, ha, hb]
```

## How to add a new lemma

A lemma qualifies for `@[stat_simp]` if all four hold:

1. **Clear normalization direction.** The LHS is a "less normal" form
   and the RHS is a "more normal" form. For us, "more normal" means:
   prefer `ℝ` over `ℝ≥0∞`; prefer constant-fold (`μ univ` becomes `1`
   under `IsProbabilityMeasure`); prefer `if` or boolean form over
   `Set.indicator`.
2. **No loop.** Adding the lemma must not cause the no-loop fixture in
   `Pythia/Tactic/StatSimpTest.lean` (search for "NO-LOOP ATTESTATION")
   to oscillate. Verify by adding the lemma, running the fixture, and
   confirming iterations 2-5 are no-ops.
3. **No expensive side condition.** Hypotheses that reduce by
   `assumption` or typeclass search are fine
   (`IsFiniteMeasure μ`, `m ≤ m₀`). Hypotheses requiring a
   decision procedure on arbitrary propositions are not
   (`Integrable f μ`, `Measurable f`). The latter belong in user
   proofs as explicit `rw [foo hf hg]`.
4. **Exists at the pinned Mathlib version.** Verify by direct grep
   under `.lake/packages/mathlib/Mathlib/` or via
   `lake env lean -e "#check <name>"`.

Process:

1. Edit `Pythia/Tactic/StatSimpRegistry.lean`, add the lemma to the
   `attribute [stat_simp]` block under the relevant category, and
   document any side-condition story in the header table.
2. Add a regression `example` to `Pythia/Tactic/StatSimpTest.lean`
   that closes via `stat_simp` in a single call.
3. Run `lake build Pythia.Tactic.StatSimpTest`. If the no-loop fixture
   passes, you're done. If it fails, the lemma loops with another;
   either revise the lemma's direction or remove the offender.
4. Open a PR. Per `CODEOWNERS`, simp-attribute changes are reviewed
   by the research lane (probability + concentration owners).

## Maintenance

- **Owner:** research lane.
- **Review checklist:** loop-free fixture passes, exists at v4.28.0,
  category placement justified, audit-pass impact assessed (does it
  obsolete any manual `simp [foo, bar, baz]` patterns elsewhere in
  `Pythia/`?).
- **Pinning:** tied to the Mathlib `v4.28.0` lakefile pin. When the
  pin advances, re-grep for renamed lemmas and update names in the
  registry.

## Related modules

- `Pythia/Tactic/ProbSimp.lean`: broader probability normalizer that
  re-tags as `@[simp]` (so it pulls from the global simp set).
- `Pythia/Tactic/StatsIneq.lean`: inequality hammer that forwards to
  Mathlib's `bound`. Sits alongside `stat_simp` in the
  concentration-of-measure pipeline (rewrite then bound then linarith).
