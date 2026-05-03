/-
  Pythia.Networking.AIMDRate
  Reno/AIMD cwnd grows by exactly MSS per RTT during the additive-increase phase.

  Jacobson 1988; RFC 5681 §3.1: during congestion avoidance (AI phase),
  cwnd increases by one MSS per RTT. We prove the closed-form:
    cwnd after n AI steps = s_init + n * MSS.

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Pythia.Networking.AIMDRate

/-- One additive-increase step: increment cwnd by one MSS. -/
def ai_step (s : ℕ) (MSS : ℕ) : ℕ := s + MSS

/-- After n AI steps from initial cwnd s_init, the cwnd equals s_init + n * MSS. -/
theorem aimd_additive_increase_rate (s_init MSS : ℕ) (n : ℕ) :
    Nat.rec s_init (fun _ s => ai_step s MSS) n = s_init + n * MSS := by
  induction n with
  | zero => simp
  | succ k ih =>
      change ai_step (Nat.rec s_init (fun _ s => ai_step s MSS) k) MSS = s_init + (k + 1) * MSS
      rw [ih, ai_step]
      ring

end Pythia.Networking.AIMDRate
