/-
  Pythia.Networking.RED
  RED drop probability is non-increasing in the minimum threshold.

  Floyd and Jacobson 1993; RFC 2309. In Random Early Detection,
  the drop probability is 0 below min_thresh, ramps linearly to 1
  at max_thresh, and is 1 above. Raising min_thresh (with max_thresh
  fixed) can only lower or preserve the drop probability for any
  given queue depth q.

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Pythia.Networking.RED

/-- RED piecewise-linear drop probability.
    Below min_thresh: 0. Above max_thresh: 1. In-between: linear ramp. -/
noncomputable def red_drop_prob (min_thresh max_thresh q : ℝ) : ℝ :=
  if q < min_thresh then 0
  else if max_thresh ≤ q then 1
  else (q - min_thresh) / (max_thresh - min_thresh)

/-- Raising the minimum threshold (min1 → min2 ≥ min1) can only lower or
    preserve the drop probability for any queue depth q. -/
theorem red_drop_probability_nonincreasing_in_minq
    (min1 min2 max_thresh q : ℝ)
    (h_order : min1 ≤ min2)
    (h_min1 : min1 < max_thresh)
    (h_min2 : min2 < max_thresh) :
    red_drop_prob min2 max_thresh q ≤ red_drop_prob min1 max_thresh q := by
  unfold red_drop_prob
  by_cases h_q_min2 : q < min2
  · rw [if_pos h_q_min2]
    by_cases h_q_min1 : q < min1
    · rw [if_pos h_q_min1]
    · push_neg at h_q_min1
      rw [if_neg (not_lt.mpr h_q_min1)]
      by_cases h_q_max : max_thresh ≤ q
      · rw [if_pos h_q_max]; norm_num
      · rw [if_neg h_q_max]
        apply div_nonneg <;> linarith
  · push_neg at h_q_min2
    rw [if_neg (not_lt.mpr h_q_min2)]
    by_cases h_q_min1 : q < min1
    · linarith
    · push_neg at h_q_min1
      rw [if_neg (not_lt.mpr h_q_min1)]
      by_cases h_q_max : max_thresh ≤ q
      · rw [if_pos h_q_max, if_pos h_q_max]
      · rw [if_neg h_q_max, if_neg h_q_max]
        -- Both in ramp: (q-min2)/(max-min2) ≤ (q-min1)/(max-min1).
        -- Cross-multiply: (q-min2)(max-min1) ≤ (q-min1)(max-min2).
        -- Rearranges to (q-max)(min2-min1) ≤ 0, which holds since
        -- q < max_thresh and min2 ≥ min1.
        have hd1 : 0 < max_thresh - min1 := by linarith
        have hd2 : 0 < max_thresh - min2 := by linarith
        push_neg at h_q_max
        rw [div_le_div_iff₀ hd2 hd1]
        nlinarith

end Pythia.Networking.RED
