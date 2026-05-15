/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Logarithmic Barrier Function (interior-point methods)

The logarithmic barrier for the constraint `x > 0` is

    barrier(t, x) = -(1/t) * log(x)

where `t > 0` is the barrier parameter. Larger `t` corresponds to a
weaker barrier: the penalty for approaching the boundary `x = 0` shrinks
as `t` grows. The central path of an interior-point method is traced by
following the minimizer of `f(x) + barrier(t, x)` as `t → ∞`.

## Definitions

* `logBarrier` : `-(1/t) * Real.log x`

## Main results

* `logBarrier_pos_of_small_x`    : when `0 < x < 1` and `t > 0`, barrier > 0
* `logBarrier_zero_at_one`       : barrier is zero when `x = 1`
* `logBarrier_antitone_t`        : barrier is antitone in `t` for fixed `0 < x ≤ 1`
* `logBarrier_scale`             : barrier scales as `logBarrier (c*t) x = (1/c) * logBarrier t x`
* `logBarrier_nonneg_interior`   : barrier is nonneg for `0 < x ≤ 1` and `t > 0`

## References

* Boyd, S. and Vandenberghe, L. "Convex Optimization." Cambridge University
  Press (2004), Section 11.2.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization

open Real

/-! ### Definition -/

/-- The logarithmic barrier function for the constraint `x > 0`.

    logBarrier t x = -(1/t) * log(x)

The parameter `t > 0` controls the strength of the barrier: as `t → ∞`
the barrier vanishes pointwise, and the constrained minimizer approaches
the unconstrained minimizer. Marked `noncomputable` because it uses
`Real.log`. -/
noncomputable def logBarrier (t x : ℝ) : ℝ := -(1 / t) * Real.log x

/-! ### Lemma 1: positive barrier for small x -/

/-- **Positive barrier below one.**
When `0 < x < 1` and `t > 0`, the barrier is strictly positive.

The proof uses two sign observations:
- `Real.log x < 0` because `0 < x < 1` (via `Real.log_neg`).
- `-(1/t) < 0` because `t > 0`.

The product of two strictly negative reals is strictly positive
(`mul_pos_of_neg_of_neg`). -/
@[stat_lemma]
theorem logBarrier_pos_of_small_x {t x : ℝ}
    (ht : 0 < t) (hx0 : 0 < x) (hx1 : x < 1) :
    0 < logBarrier t x := by
  unfold logBarrier
  apply mul_pos_of_neg_of_neg
  · linarith [div_pos one_pos ht]
  · exact Real.log_neg hx0 hx1

/-! ### Lemma 2: barrier vanishes at x = 1 -/

/-- **Barrier is zero at x = 1.**
For any barrier parameter `t`, `logBarrier t 1 = 0`.
The logarithm of one is zero (`Real.log_one`), so the whole expression
vanishes regardless of `t`. -/
@[stat_lemma]
theorem logBarrier_zero_at_one (t : ℝ) :
    logBarrier t 1 = 0 := by
  unfold logBarrier
  simp [Real.log_one]

/-! ### Lemma 3: barrier is antitone in t -/

/-- **Antitone in the barrier parameter.**
For fixed `0 < x` with `x ≤ 1`, the barrier `logBarrier t x` is
antitone in `t`: increasing `t` weakens the barrier.

Concretely, for `0 < t₁ ≤ t₂`:

    logBarrier t₂ x ≤ logBarrier t₁ x.

Proof: write `logBarrier t x = (1/t) * (-log x)`. Since `x ≤ 1` and
`0 < x`, we have `-log x ≥ 0`. The coefficient `1/t` decreases as `t`
increases (`one_div_le_one_div_of_le`), so the product decreases. -/
@[stat_lemma]
theorem logBarrier_antitone_t {t₁ t₂ x : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : t₁ ≤ t₂)
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    logBarrier t₂ x ≤ logBarrier t₁ x := by
  unfold logBarrier
  have ht₂pos : 0 < t₂ := lt_of_lt_of_le ht₁ ht₂
  -- Rewrite as (1/t) * (-log x) to expose the decreasing coefficient.
  have key₁ : -(1 / t₁) * Real.log x = (1 / t₁) * (-Real.log x) := by ring
  have key₂ : -(1 / t₂) * Real.log x = (1 / t₂) * (-Real.log x) := by ring
  rw [key₁, key₂]
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_left zero_le_one ht₁ ht₂
  · linarith [Real.log_nonpos (le_of_lt hx0) hx1]

/-! ### Lemma 4: scaling the barrier parameter -/

/-- **Barrier scaling identity.**
Scaling the barrier parameter by `c > 0` scales the barrier value by
`1/c`:

    logBarrier (c * t) x = (1/c) * logBarrier t x.

This reflects the homogeneity of the barrier: doubling `t` halves the
penalty. Proof by `field_simp` + `ring` after discharging the
nonzero-denominator side conditions from `c ≠ 0` and `t ≠ 0`. -/
@[stat_lemma]
theorem logBarrier_scale {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (x : ℝ) :
    logBarrier (c * t) x = (1 / c) * logBarrier t x := by
  unfold logBarrier
  have hc' : c ≠ 0 := ne_of_gt hc
  have ht' : t ≠ 0 := ne_of_gt ht
  field_simp [hc', ht']

/-! ### Lemma 5: nonneg barrier on (0, 1] -/

/-- **Nonneg barrier on the interior (0, 1].**
When `0 < x`, `x ≤ 1`, and `t > 0`, the barrier is nonneg.

The proof uses two nonpositivity observations:
- `Real.log x ≤ 0` because `0 < x ≤ 1` (`Real.log_nonpos`).
- `-(1/t) ≤ 0` because `t > 0`.

The product of two nonpositive reals is nonneg
(`mul_nonneg_of_nonpos_of_nonpos`). -/
@[stat_lemma]
theorem logBarrier_nonneg_interior {t x : ℝ}
    (ht : 0 < t) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ logBarrier t x := by
  unfold logBarrier
  apply mul_nonneg_of_nonpos_of_nonpos
  · linarith [div_pos one_pos ht]
  · exact Real.log_nonpos (le_of_lt hx0) hx1

end Pythia.Optimization
