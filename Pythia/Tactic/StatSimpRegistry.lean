/-
Pythia.Tactic.StatSimpRegistry — the curated `@[stat_simp]` membership
table.

This file is split from `StatSimp.lean` because Lean 4 does not let a
freshly-`register_simp_attr`-declared attribute be applied in the same
module that declares it. Mirrors the `StatsIneq` ↔ `StatsIneqRegistry`
and `ProbSimp` ↔ `ProbSimpRegistry` splits.

Each lemma below was verified against Mathlib v4.28.0 by direct grep
under `.lake/packages/mathlib/Mathlib/`. Lemma criteria are documented
in `StatSimp.lean` (clear normalization direction, no loop on the
fixed-point fixture, no expensive side condition, exists at v4.28.0).

## Coverage (40 lemmas)

### ENNReal `toReal` normalization (`ℝ≥0∞ → ℝ`)
- `ENNReal.toReal_one`, `ENNReal.toReal_zero`, `ENNReal.toReal_top`
- `ENNReal.toReal_nonneg`
- `ENNReal.coe_toReal`
- `ENNReal.toReal_ofReal` (LHS: `ENNReal.ofReal x).toReal`, condition `0 ≤ x`)
- `ENNReal.ofReal_toReal` (LHS: `ENNReal.ofReal a.toReal`, condition `a ≠ ∞`)
- `ENNReal.toReal_mul`, `ENNReal.toReal_div`, `ENNReal.toReal_pow`,
  `ENNReal.toReal_inv`
- `ENNReal.toReal_add` (condition: `a ≠ ∞`, `b ≠ ∞`)

### ENNReal `ofReal` and round-trip iffs
- `ENNReal.ofReal_zero`, `ENNReal.ofReal_one`, `ENNReal.ofReal_ofNat`
- `ENNReal.ofReal_pos`, `ENNReal.ofReal_eq_zero`, `ENNReal.ofReal_lt_top`
- `ENNReal.ofReal_le_ofReal_iff` (condition: `0 ≤ q`)
- `ENNReal.ofReal_eq_ofReal_iff` (condition: `0 ≤ p`, `0 ≤ q`)
- `ENNReal.ofReal_mul` (condition: `0 ≤ p`)

### NNReal coercions (round-trip cleanup)
- `ENNReal.toNNReal_one`, `ENNReal.toNNReal_zero`, `ENNReal.toNNReal_top`

### Probability measure axiom + outer-measure lifting
- `MeasureTheory.IsProbabilityMeasure.measure_univ`
- `MeasureTheory.measure_empty`
- `MeasureTheory.Measure.coe_toOuterMeasure`

### `Measure.real` (real-valued measure normal-form)
- `MeasureTheory.measureReal_zero`
- `MeasureTheory.measureReal_empty`
- `MeasureTheory.measureReal_nonneg`
- `MeasureTheory.probReal_univ` (probability measure univ = 1 in ℝ)

### Indicator function
- `Set.indicator_of_mem`, `Set.indicator_of_notMem`
- `Set.indicator_univ`, `Set.indicator_empty`

### Conditional expectation
- `MeasureTheory.condExp_zero`
- `MeasureTheory.condExp_const` (conditions `m ≤ m₀`, `[IsFiniteMeasure μ]`)

### Integral / lintegral (zero-measure shortcuts only)
- `MeasureTheory.integral_zero_measure`
- `MeasureTheory.lintegral_zero_measure`

## Lemmas considered but EXCLUDED (with reasoning)

- `MeasureTheory.condExp_add` — requires `Integrable f μ` and
  `Integrable g μ` as explicit hypotheses. `simp` cannot discharge
  these from a typeclass / decision procedure, so the rewrite would
  rarely fire and would clutter the rule-set when it did. Callers
  should `rw [condExp_add hf hg]` explicitly.

- `MeasureTheory.condExp_indicator` — same reason: requires
  `Integrable f μ` + `MeasurableSet[m] s`. Conditional rewrite
  belongs in user proofs, not in a normal-form set.

- `Set.indicator_apply` — exists in Mathlib v4.28.0 but is NOT
  `@[simp]` upstream because of the `[Decidable (a ∈ s)]` instance
  argument. Tagging it would force `simp` to materialise a decidability
  instance on every probability goal, bloating closure time. Excluded
  by design; the cheaper `indicator_of_mem` / `indicator_of_notMem`
  pair is in the set instead.

- `MeasureTheory.Measure.map_apply` — requires both `Measurable f`
  and `MeasurableSet s`. Excluded for the same hypothesis-discharge
  reason as `condExp_add`.

- `ENNReal.ofReal_add` — requires `0 ≤ p` AND `0 ≤ q`. Adding it
  with two side conditions makes the rewrite fragile; callers
  who want this should use `prob_simp` (the broader tactic) or
  rewrite manually.

- `ENNReal.ofReal_div_of_pos` — requires `0 < y` (strict). Same
  fragility argument. The `toReal_div` variant (which has no side
  condition) IS in the set, so the use case is covered going the
  other direction.

- `ENNReal.ofReal_lt_ofReal_iff_of_nonneg` — adding both this and
  `ofReal_le_ofReal_iff` to the set is redundant; the `≤` form
  composes via `lt_iff_le_not_le`. Keeping the rule-set minimal
  reduces simp-search cost.

- `MeasureTheory.integral_const`, `MeasureTheory.lintegral_const` —
  these rewrite `∫ _, c ∂μ` to `(μ.real univ) • c`. Useful for
  probability measures (becomes `c`) but interacts poorly with
  `integral_zero_measure`: simp picks the const-rewrite first,
  leaving `((0 : Measure α).real univ) • c` which is harder to
  close than the direct `= 0`. Excluded from the set; callers
  who want this rewrite should `rw [integral_const]` explicitly.
  Tracked for re-evaluation if a measure-application normal-form
  lemma lands upstream.

## No-loop attestation

The fixed-point fixture in `StatSimpTest.lean` runs `stat_simp` 5×
on a synthetic goal exercising every category above and asserts
that iterations 2-5 are no-ops (state stable after iteration 1).
CI fails if any added lemma introduces a loop.
-/
import Pythia.Tactic.StatSimp

attribute [stat_simp]
  -- ENNReal `toReal` normalization (ℝ≥0∞ → ℝ).
  ENNReal.toReal_one
  ENNReal.toReal_zero
  ENNReal.toReal_top
  ENNReal.toReal_nonneg
  ENNReal.coe_toReal
  ENNReal.toReal_ofReal
  ENNReal.ofReal_toReal
  ENNReal.toReal_mul
  ENNReal.toReal_div
  ENNReal.toReal_pow
  ENNReal.toReal_inv
  ENNReal.toReal_add
  -- ENNReal `ofReal` and round-trip iffs.
  ENNReal.ofReal_zero
  ENNReal.ofReal_one
  ENNReal.ofReal_ofNat
  ENNReal.ofReal_pos
  ENNReal.ofReal_eq_zero
  ENNReal.ofReal_lt_top
  ENNReal.ofReal_le_ofReal_iff
  ENNReal.ofReal_eq_ofReal_iff
  ENNReal.ofReal_mul
  -- NNReal coercions.
  ENNReal.toNNReal_one
  ENNReal.toNNReal_zero
  ENNReal.toNNReal_top
  -- Probability-measure axiom + outer-measure lifting.
  MeasureTheory.IsProbabilityMeasure.measure_univ
  MeasureTheory.measure_empty
  MeasureTheory.Measure.coe_toOuterMeasure
  -- `Measure.real` (real-valued measure normal-form).
  MeasureTheory.measureReal_zero
  MeasureTheory.measureReal_empty
  MeasureTheory.measureReal_nonneg
  MeasureTheory.probReal_univ
  -- Indicator function.
  Set.indicator_of_mem
  Set.indicator_of_notMem
  Set.indicator_univ
  Set.indicator_empty
  -- Conditional expectation.
  MeasureTheory.condExp_zero
  MeasureTheory.condExp_const
  -- Integral / lintegral (zero-measure shortcuts only — see header
  -- for why `integral_const` / `lintegral_const` are excluded).
  MeasureTheory.integral_zero_measure
  MeasureTheory.lintegral_zero_measure
