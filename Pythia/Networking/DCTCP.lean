/-
  Pythia.Networking.DCTCP
  DCTCP mark probability is monotone in queue depth.

  Alizadeh et al. "Data Center TCP (DCTCP)", SIGCOMM 2010; RFC 8257.
  The ECN marking probability in DCTCP follows a piecewise-linear
  ramp: 0 below K_min, linear between K_min and K_max, 1 above K_max.
  We prove that this function is monotone non-decreasing in queue depth q.

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Pythia.Networking.DCTCP

/-- DCTCP ECN marking probability as a function of instantaneous queue depth q.
    K_min and K_max are the lower and upper marking thresholds. -/
noncomputable def mark_prob (K_min K_max q : ℝ) : ℝ :=
  if q < K_min then 0
  else if K_max ≤ q then 1
  else (q - K_min) / (K_max - K_min)

/-- mark_prob is monotone non-decreasing in queue depth q.
    A deeper queue never has strictly lower marking probability. -/
theorem dctcp_mark_probability_monotone
    (K_min K_max : ℝ)
    (h_thresh : K_min < K_max) :
    Monotone (mark_prob K_min K_max) := by
  intro q1 q2 hq
  unfold mark_prob
  by_cases h1 : q1 < K_min
  · rw [if_pos h1]
    by_cases h3 : q2 < K_min
    · simp [h3]
    · push_neg at h3
      rw [if_neg (not_lt.mpr h3)]
      by_cases h4 : K_max ≤ q2
      · rw [if_pos h4]; norm_num
      · rw [if_neg h4]
        apply div_nonneg <;> linarith
  · push_neg at h1
    rw [if_neg (not_lt.mpr h1)]
    by_cases h2 : K_max ≤ q1
    · rw [if_pos h2]
      have h4 : K_max ≤ q2 := le_trans h2 hq
      rw [if_neg (not_lt.mpr (le_trans (le_of_lt h_thresh) h4)), if_pos h4]
    · rw [if_neg h2]
      push_neg at h2
      by_cases h3 : q2 < K_min
      · linarith
      · push_neg at h3
        rw [if_neg (not_lt.mpr h3)]
        by_cases h4 : K_max ≤ q2
        · rw [if_pos h4]
          rw [div_le_one (by linarith)]; linarith
        · rw [if_neg h4]
          apply div_le_div_of_nonneg_right _ (by linarith)
          linarith

end Pythia.Networking.DCTCP
