/-
Pythia.Numerical.PicardLindelof — ODE existence + uniqueness.

Picard-Lindelöf (Cauchy-Lipschitz) theorem for the initial value
problem `y'(t) = f(t, y(t))`, `y(t₀) = y₀`. Mathlib has the basic
fixed-point machinery (`ContractionMapping`) but does not surface the
named ODE existence-uniqueness theorem in a form that engineers can
quote without re-proving.

This module ships scaffold theorem signatures matching standard
applied-math practice. Aristotle queue items 29-30 close the proofs.

## What ships

- `picard_lindelof_local`: local existence + uniqueness on a small
  time interval given Lipschitz f.
- `picard_lindelof_global`: global existence + uniqueness on all of
  ℝ given globally-Lipschitz f.
- `picard_lindelof_continuous_dependence`: continuous dependence on
  initial conditions (Gronwall consequence).

## Status

v0.5 scaffold. Theorem signatures defined; proofs are scaffold
sorries pending Aristotle. The signatures match the form a working
applied mathematician quotes (Hartman "Ordinary Differential
Equations" Ch. II.1).

## Dependencies

- Mathlib's `LipschitzWith` and `ContractionMapping` for the fixed-point step.
- `MeasureTheory.IntervalIntegrable` for the integral form.

-/
import Mathlib

namespace Pythia.Numerical.PicardLindelof

open MeasureTheory

/-- Picard-Lindelöf local existence + uniqueness: given `f : ℝ → ℝ → ℝ`
that is uniformly Lipschitz in its second argument with constant `K`
on a compact rectangle around `(t₀, y₀)`, the IVP `y' = f(t, y)`,
`y(t₀) = y₀` has a unique continuously differentiable solution on a
neighborhood of `t₀`. -/
theorem picard_lindelof_local
    (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (K : NNReal) (hK_lip : ∀ t ∈ Set.Icc (t₀ - a) (t₀ + a),
      LipschitzWith K (fun y => f t y))
    (M : ℝ) (hM_bound : ∀ t ∈ Set.Icc (t₀ - a) (t₀ + a),
      ∀ y ∈ Set.Icc (y₀ - b) (y₀ + b), |f t y| ≤ M) :
    ∃ (h : ℝ) (_ : 0 < h) (y : ℝ → ℝ),
      (∀ t ∈ Set.Icc (t₀ - h) (t₀ + h),
        HasDerivAt y (f t (y t)) t) ∧
      y t₀ = y₀ ∧
      ∀ (z : ℝ → ℝ),
        (∀ t ∈ Set.Icc (t₀ - h) (t₀ + h), HasDerivAt z (f t (z t)) t) →
        z t₀ = y₀ →
        ∀ t ∈ Set.Icc (t₀ - h) (t₀ + h), y t = z t := by
  sorry  -- v0.5 scaffold; Aristotle queue item 29

/-- Picard-Lindelöf global: when `f` is *globally* Lipschitz in `y`
(uniform constant for all `t`), the IVP has a unique solution on the
whole real line. -/
theorem picard_lindelof_global
    (f : ℝ → ℝ → ℝ) (y₀ : ℝ)
    (K : NNReal) (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (h_meas : ∀ y : ℝ, Measurable (fun t => f t y))
    (h_int : ∀ y : ℝ, IntervalIntegrable (fun t => f t y) volume 0 1) :
    ∃! y : ℝ → ℝ,
      (∀ t : ℝ, HasDerivAt y (f t (y t)) t) ∧ y 0 = y₀ := by
  sorry  -- v0.5 scaffold; Aristotle queue item 29

/-- Continuous dependence on initial conditions (Gronwall-driven).
Two solutions to the same ODE with initial conditions `y₀` and `z₀`
diverge at most exponentially with rate `K`. -/
theorem picard_lindelof_continuous_dependence
    (f : ℝ → ℝ → ℝ) (y₀ z₀ : ℝ) (K : NNReal)
    (y z : ℝ → ℝ)
    (hy_eq : ∀ t : ℝ, HasDerivAt y (f t (y t)) t) (hy_init : y 0 = y₀)
    (hz_eq : ∀ t : ℝ, HasDerivAt z (f t (z t)) t) (hz_init : z 0 = z₀)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      |y t - z t| ≤ |y₀ - z₀| * Real.exp ((K : ℝ) * t) := by
  sorry  -- v0.5 scaffold; Aristotle queue item 30

end Pythia.Numerical.PicardLindelof
