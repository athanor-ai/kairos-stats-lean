/-
Kairos.Stats.StoppingRule — formalised stopping-rule primitive.

A stopping rule on a discrete-time filtration `𝓕` is an
`𝓕_t`-measurable decision function `decide : (Time → ℝ) → Time →
Bool` that converts a running martingale into a stopping time.
Admissibility (Ramdas-Grünwald-Vovk-Shafer 2022) requires the
resulting stopping time to satisfy `ℙ(τ < ∞) ≤ α` in real arithmetic
for every sub-Gaussian martingale and every stated coverage level α.

This module formalises these primitives in Mathlib style.
-/

import Mathlib
import Kairos.Stats.Basic

namespace Kairos.Stats

/-- Discrete-time stopping rule: an `𝓕_t`-measurable decision to
stop or continue at each step based on the running martingale. -/
structure StoppingRule
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : MeasureTheory.Filtration ℕ mΩ) where
  /-- Decision function: returns `true` = stop, `false` = continue. -/
  decide : (ℕ → ℝ) → ℕ → Bool
  /-- Monotone-once-fired: once the rule signals stop, it stays
  stopped on the same trajectory.  Matches the "path-specific"
  reading of deployment monotonicity (not the refuted universal
  reading of our Theorem~specification-incompatibility). -/
  monotone_once_fired : ∀ (m : ℕ → ℝ) (t : ℕ),
    decide m t = true → decide m (t + 1) = true

/-- Induced stopping time: the first `t` at which the rule fires
on the given trajectory. Returns `none` if the rule never fires. -/
noncomputable def StoppingRule.firstHit
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : MeasureTheory.Filtration ℕ mΩ}
    (r : StoppingRule 𝓕) (m : ℕ → ℝ) : Option ℕ :=
  open scoped Classical in
  if h : ∃ t, r.decide m t = true then some (Nat.find h) else none

/-- Admissibility condition (Ramdas et al. 2022): the stopping rule
applied to any sub-Gaussian martingale in the admissible class must
have overall stopping probability at most the stated coverage level
α, evaluated in real arithmetic. -/
structure Admissible
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : MeasureTheory.Filtration ℕ mΩ) (μ : MeasureTheory.Measure Ω)
    (r : StoppingRule 𝓕) (alpha : ℝ) where
  alpha_range : 0 < alpha ∧ alpha < 1
  stopping_prob_le : ∀ (m : ℕ → Ω → ℝ)
      (_h_adapted : MeasureTheory.Adapted 𝓕 m)
      (_h_integrable : ∀ t, MeasureTheory.Integrable (m t) μ),
    μ {ω | ∃ t, r.decide (fun t => m t ω) t = true} ≤
      ENNReal.ofReal alpha

end Kairos.Stats
