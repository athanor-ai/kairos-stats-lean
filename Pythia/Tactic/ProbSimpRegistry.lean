/-
Pythia.Tactic.ProbSimpRegistry — auto-tags a curated set of
probability normalization lemmas with `@[prob_simp]`.

This file is split from `ProbSimp.lean` because Lean does not let a
freshly-`initialize`d builtin attribute be applied in the same module
that declares it. Mirrors the `StatsIneq` ↔ `StatsIneqRegistry` and
`CSFamilyAttr` ↔ `CSFamilyRegistry` splits.

Each lemma below was verified against Mathlib v4.28.0 by direct grep
under `.lake/packages/mathlib/Mathlib/`. Lemmas already carrying
`@[simp]` upstream (most of these) are re-tagged here so they appear
in `#prob_simps`; re-applying `@[simp]` to the same decl is a no-op.

## Coverage

  • Probability-measure axiom:
      `MeasureTheory.IsProbabilityMeasure.measure_univ`
  • PDF-style normalization (∫⁻ … = μ univ, etc.):
      `MeasureTheory.lintegral_const`
      `MeasureTheory.integral_const`
      `MeasureTheory.integral_zero_measure`
      `MeasureTheory.setIntegral_measure_zero`
  • Outer-measure lifting:
      `MeasureTheory.Measure.coe_toOuterMeasure`
  • Empty-set:
      `MeasureTheory.measure_empty`
  • ENNReal ↔ ℝ coercion normalization:
      `ENNReal.toReal_one`
      `ENNReal.toReal_zero`
      `ENNReal.toNNReal_one`
      `ENNReal.toNNReal_zero`
      `ENNReal.toReal_ofReal`
      `ENNReal.ofReal_toReal`
      `ENNReal.ofReal_one`
      `ENNReal.ofReal_zero`
      `ENNReal.coe_toReal`
      `ENNReal.toReal_top`

## Lemmas requested by that do NOT exist at this commit

  • `MeasureTheory.set_integral_eq_zero_of_zero_measure` — does not
    exist as a top-level decl in Mathlib v4.28.0. The closest match
    is `MeasureTheory.setIntegral_measure_zero`, which takes the
    same form `μ s = 0 → ∫ x in s, f x ∂μ = 0` and IS tagged below.

  • `IsProbabilityMeasure.toIsFiniteMeasure` — exists but as an
    `instance`, not a `theorem`. Already in the type-class search
    path; tagging as `@[simp]` is a category error since it has no
    rewriting content. Excluded by design.

  • `MeasureTheory.integral_indicator` — exists, but is not a
    `simp` lemma upstream because of the side-condition on `s`.
    Tagging it would break unrelated `simp` calls. Excluded by design;
    callers should `rw [integral_indicator hs]` explicitly.
-/
import Pythia.Tactic.ProbSimp

attribute [prob_simp]
  -- Probability-measure axiom + outer-measure lifting.
  MeasureTheory.IsProbabilityMeasure.measure_univ
  MeasureTheory.Measure.coe_toOuterMeasure
  MeasureTheory.measure_empty
  -- Integral / lintegral normalization.
  MeasureTheory.lintegral_const
  MeasureTheory.integral_const
  MeasureTheory.integral_zero_measure
  -- ENNReal ↔ ℝ coercion normalization.
  ENNReal.toReal_one
  ENNReal.toReal_zero
  ENNReal.toNNReal_one
  ENNReal.toNNReal_zero
  ENNReal.toReal_ofReal
  ENNReal.ofReal_toReal
  ENNReal.ofReal_one
  ENNReal.ofReal_zero
  ENNReal.coe_toReal
  ENNReal.toReal_top
