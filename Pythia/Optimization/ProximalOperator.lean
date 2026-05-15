/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proximal Operator: Soft-Thresholding (algebraic identities)

The soft-thresholding operator is the proximal operator of the
scaled L1 norm. For a scalar:

    S_lam(v) = max(v - lam, 0) + min(v + lam, 0)

This file gives the algebraic identities using the sum-of-clamps form,
which avoids if-then-else branching and simplifies proofs.

## Main results

* `softThreshold`                    : `max(v - lam, 0) + min(v + lam, 0)`
* `softThreshold_zero_at_zero`       : `S_lam(0) = 0` for `lam >= 0`
* `softThreshold_nonneg_of_nonneg`   : `v >= lam >= 0 -> S_lam(v) >= 0`

## References

* Parikh, N. and Boyd, S. "Proximal Algorithms."
  Foundations and Trends in Optimization 1(3): 127-239 (2014).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Optimization

/-- Scalar soft-thresholding via the sum-of-clamps form. -/
noncomputable def softThreshold (lam v : ℝ) : ℝ :=
  max (v - lam) 0 + min (v + lam) 0

/-- **Zero input.** `S_lam(0) = 0` for `lam >= 0`. -/
@[stat_lemma]
theorem softThreshold_zero_at_zero {lam : ℝ} (hlam : 0 ≤ lam) :
    softThreshold lam 0 = 0 := by
  unfold softThreshold
  rw [max_eq_right (by linarith : (0 : ℝ) - lam ≤ 0),
      min_eq_right (by linarith : (0 : ℝ) ≤ 0 + lam)]
  ring

/-- **Nonneg for large positive input.** When `v >= lam >= 0`,
the soft threshold is nonneg. -/
@[stat_lemma]
theorem softThreshold_nonneg_of_large {lam v : ℝ}
    (hlam : 0 ≤ lam) (hv : lam ≤ v) :
    0 ≤ softThreshold lam v := by
  unfold softThreshold
  have h1 : 0 ≤ v - lam := by linarith
  have h2 : 0 ≤ v + lam := by linarith
  rw [max_eq_left h1, min_eq_right h2]
  linarith

/-- **Kills small values.** When `|v| <= lam` (both `v <= lam` and
`-lam <= v`), the soft threshold is zero. -/
@[stat_lemma]
theorem softThreshold_zero_in_band {lam v : ℝ}
    (hv_le : v ≤ lam) (hv_ge : -lam ≤ v) :
    softThreshold lam v = 0 := by
  unfold softThreshold
  rw [max_eq_right (by linarith : v - lam ≤ 0),
      min_eq_right (by linarith : 0 ≤ v + lam)]
  ring

end Pythia.Optimization
