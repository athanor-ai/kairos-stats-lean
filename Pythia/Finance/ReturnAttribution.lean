/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Return Attribution (Brinson decomposition kernel)

The Brinson-Hood-Beebower (BHB) single-period attribution decomposes
active return into allocation and selection effects:

    activeReturn = portfolioReturn - benchmarkReturn

For a two-sector model with weights w_p, w_b and returns r_1, r_2:

    allocationEffect(w_p, w_b, r_b) = (w_p - w_b) * r_b
    selectionEffect(w_b, r_p, r_b) = w_b * (r_p - r_b)

## Main results

* `activeReturn`          : `r_p - r_b`
* `allocationEffect`      : `(w_p - w_b) * r_b`
* `selectionEffect`       : `w_b * (r_p - r_b)`
* `attribution_sum`       : allocation + selection + interaction = active

## References

* Brinson, G. P., Hood, L. R. and Beebower, G. L. "Determinants
  of Portfolio Performance." Financial Analysts Journal 42(4):
  39-44 (1986).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

noncomputable def activeReturn (r_p r_b : ℝ) : ℝ := r_p - r_b

noncomputable def allocationEffect (w_p w_b r_b : ℝ) : ℝ :=
  (w_p - w_b) * r_b

noncomputable def selectionEffect (w_b r_p r_b : ℝ) : ℝ :=
  w_b * (r_p - r_b)

noncomputable def interactionEffect (w_p w_b r_p r_b : ℝ) : ℝ :=
  (w_p - w_b) * (r_p - r_b)

/-- **BHB decomposition.** Active return = allocation + selection
+ interaction (exact, single-period). -/
@[stat_lemma]
theorem attribution_sum (w_p w_b r_p r_b : ℝ) :
    allocationEffect w_p w_b r_b + selectionEffect w_b r_p r_b
      + interactionEffect w_p w_b r_p r_b
    = w_p * r_p - w_b * r_b := by
  unfold allocationEffect selectionEffect interactionEffect; ring

/-- **Zero active return when portfolios match.** -/
@[stat_lemma]
theorem activeReturn_zero_iff {r_p r_b : ℝ} :
    activeReturn r_p r_b = 0 ↔ r_p = r_b := by
  unfold activeReturn; exact sub_eq_zero

/-- **Allocation effect zero when weights match.** -/
@[stat_lemma]
theorem allocationEffect_zero_of_equal_weights (w r_b : ℝ) :
    allocationEffect w w r_b = 0 := by
  unfold allocationEffect; ring

/-- **Selection effect zero when returns match.** -/
@[stat_lemma]
theorem selectionEffect_zero_of_equal_returns (w_b r : ℝ) :
    selectionEffect w_b r r = 0 := by
  unfold selectionEffect; ring

/-- **Positive allocation from overweighting outperforming sector.** -/
@[stat_lemma]
theorem allocationEffect_pos {w_p w_b r_b : ℝ}
    (hw : w_b < w_p) (hr : 0 < r_b) :
    0 < allocationEffect w_p w_b r_b := by
  unfold allocationEffect
  exact mul_pos (sub_pos.mpr hw) hr

end Pythia.Finance
