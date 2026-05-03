/-
  Pythia.Networking.CoDel
  CoDel sojourn-time bound under low load: λ < μ ⟹ sojourn ≤ queue_len / λ.

  Nichols and Jacobson, "Controlling Queue Delay", ACM Queue 2012; RFC 8289.
  Under stable load (arrival rate λ < service rate μ), Little's Law gives
  sojourn_time = queue_len / λ.  We parametrize the queue-length bound in
  terms of the slack (μ - λ) and prove the sojourn inequality by direct
  algebraic manipulation.

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

set_option linter.unusedVariables false

namespace Pythia.Networking.CoDel

/-- CoDel sojourn-time bound under low load.
    If queue_len ≤ (μ-λ)·t + 1 and sojourn_time = queue_len / λ (Little's Law),
    then sojourn_time ≤ ((μ-λ)·t + 1) / λ. -/
theorem codel_sojourn_time_bounded_under_low_load
    (lambda mu queue_len sojourn_time t : ℝ)
    (h_stable : lambda < mu) (h_pos : 0 < mu)
    (h_queue : queue_len ≤ (mu - lambda) * t + 1)
    (h_little : sojourn_time = queue_len / lambda) (h_lambda_pos : 0 < lambda) :
    sojourn_time ≤ ((mu - lambda) * t + 1) / lambda := by
  rw [h_little]
  exact div_le_div_of_nonneg_right h_queue (le_of_lt h_lambda_pos)

end Pythia.Networking.CoDel
