/-
  Pythia.Networking.BBRBDP
  BBRv3 ProbeBW inflight cap: inflight ≤ 2 · (pacing_rate · min_rtt) + 3·MSS.

  Cardwell et al. BBRv3 draft (draft-ietf-ccwg-bbr-05) §4.6.4:
  during ProbeBW the congestion window is set to
  cwnd = cwnd_gain · BDP + 3·MSS, with cwnd_gain ≤ 2 and BDP = pacing_rate · min_rtt.
  We state the inflight cap as a hypothesis on a generic scalar state and
  unfold the bound arithmetic, avoiding the full BBR state machine.

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

set_option linter.unusedVariables false

namespace Pythia.Networking.BBRBDP

/-- BBRv3 ProbeBW inflight cap.
    Given that inflight ≤ cwnd_gain · pacing_rate · min_rtt + 3·MSS and cwnd_gain ≤ 2,
    we immediately obtain inflight ≤ 2 · (pacing_rate · min_rtt) + 3·MSS. -/
theorem bbr_bdp_inflight_cap
    (inflight pacing_rate min_rtt : ℝ) (MSS : ℕ) (cwnd_gain : ℝ)
    (h_gain : cwnd_gain ≤ 2)
    (h_rate : 0 ≤ pacing_rate) (h_minrtt : 0 ≤ min_rtt)
    (h_MSS : 0 ≤ (MSS : ℝ))
    (h_inflight_def : inflight ≤ cwnd_gain * pacing_rate * min_rtt + 3 * MSS) :
    inflight ≤ 2 * (pacing_rate * min_rtt) + 3 * MSS := by
  nlinarith [mul_nonneg h_rate h_minrtt]

end Pythia.Networking.BBRBDP
