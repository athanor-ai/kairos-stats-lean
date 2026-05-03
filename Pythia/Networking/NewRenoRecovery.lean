/-
  Pythia.Networking.NewRenoRecovery
  TCP New-Reno fast-retransmit cwnd recovery.

  RFC 6582 §3: after fast retransmit, ssthresh is set to cwnd/2 and the
  sender enters fast recovery.  Partial-ACKs reduce cwnd by one MSS per
  ACK until cwnd ≤ ssthresh, at which point recovery exits.

  We prove that this process terminates within (cwnd₀ - ssthresh).toNat + 1
  partial-ACK steps by well-founded descent on the gap (cwnd - ssthresh).toNat.

  Deviation from spec: the spec's outer bound k ≤ s0.cwnd.toNat is not
  provable when ssthresh = 0 (the base case yields k = 1 = cwnd.toNat when
  cwnd = 1 and ssthresh = 0, i.e., cwnd.toNat - 1 = 0 < 1 = k).  Per the
  spec's fallback instruction ("simplify to SUMMABLE form if non-trivial"),
  we state the correct bound k ≤ (cwnd₀ - ssthresh).toNat + 1, which equals
  the RFC's cwnd/MSS + 1 partial-ACK count.

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

set_option linter.unusedVariables false

namespace Pythia.Networking.NewRenoRecovery

structure RecoveryState where
  cwnd        : Int
  ssthresh    : Int
  in_recovery : Bool

/-- One partial-ACK step of New-Reno fast recovery.
    RFC 6582 §3: if cwnd > ssthresh, deflate cwnd by one MSS toward ssthresh;
    otherwise exit recovery. -/
def partial_ack_step (s : RecoveryState) (MSS : Int) : RecoveryState :=
  if s.cwnd ≤ s.ssthresh then { s with in_recovery := false }
  else { s with cwnd := max s.ssthresh (s.cwnd - MSS) }

-- Nat.recAux definitional unfolding at successor
private theorem recAux_succ (s : RecoveryState) (MSS : Int) (n : Nat) :
    Nat.recAux (motive := fun _ => RecoveryState) s (fun _ s' => partial_ack_step s' MSS) (n + 1) =
    partial_ack_step (Nat.recAux (motive := fun _ => RecoveryState) s
        (fun _ s' => partial_ack_step s' MSS) n) MSS := rfl

-- Shifting: iterating k steps on (step s) equals iterating (k+1) steps on s
private theorem recAux_prepend (s : RecoveryState) (MSS : Int) (k : Nat) :
    Nat.recAux (motive := fun _ => RecoveryState) (partial_ack_step s MSS)
        (fun _ s' => partial_ack_step s' MSS) k =
    Nat.recAux (motive := fun _ => RecoveryState) s
        (fun _ s' => partial_ack_step s' MSS) (k + 1) := by
  induction k with
  | zero => rfl
  | succ n ih => rw [recAux_succ, recAux_succ, ih]

-- The gap (cwnd - ssthresh) decreases by ≥ MSS per step (or collapses to 0)
private theorem new_gap_le (s : RecoveryState) (MSS : Int) (h_MSS : 0 < MSS)
    (h_above : s.ssthresh < s.cwnd) (m : Nat)
    (h_gap : (s.cwnd - s.ssthresh).toNat ≤ m + 1) :
    ((partial_ack_step s MSS).cwnd - (partial_ack_step s MSS).ssthresh).toNat ≤ m := by
  have h_not_le : ¬ (s.cwnd ≤ s.ssthresh) := Int.not_le.mpr h_above
  have h_ss : (partial_ack_step s MSS).ssthresh = s.ssthresh := by
    unfold partial_ack_step; simp [h_not_le]
  have h_cw : (partial_ack_step s MSS).cwnd = max s.ssthresh (s.cwnd - MSS) := by
    unfold partial_ack_step; simp [h_not_le]
  rw [h_ss, h_cw]
  have hgap : s.cwnd - s.ssthresh ≤ (m : ℤ) + 1 := by
    exact_mod_cast Int.toNat_le.mp h_gap
  by_cases h : s.ssthresh ≤ s.cwnd - MSS
  · -- cwnd - MSS ≥ ssthresh: new gap = cwnd - MSS - ssthresh ≤ m
    rw [Int.max_eq_right h]; apply Int.toNat_le.mpr; omega
  · -- cwnd - MSS < ssthresh: new gap = 0
    push_neg at h; rw [Int.max_eq_left (le_of_lt h)]; simp

-- Inductive core: starting from any state with gap ≤ n, exit within n + 1 steps
private theorem exists_exit_aux (n : Nat) :
    ∀ (s : RecoveryState) (MSS : Int), 0 < MSS →
    (s.cwnd - s.ssthresh).toNat ≤ n →
    ∃ k : Nat, k ≤ n + 1 ∧
      (Nat.recAux (motive := fun _ => RecoveryState) s
          (fun _ s' => partial_ack_step s' MSS) k).in_recovery = false := by
  induction n with
  | zero =>
    intro s MSS h_MSS h_gap
    have h_below : s.cwnd ≤ s.ssthresh := by
      have := Nat.le_zero.mp h_gap; rw [Int.toNat_eq_zero] at this; omega
    exact ⟨1, le_refl _,
      by rw [recAux_succ]; simp [Nat.recAux, partial_ack_step, h_below]⟩
  | succ m ih =>
    intro s MSS h_MSS h_gap
    by_cases h_below : s.cwnd ≤ s.ssthresh
    · -- Already at ssthresh: one step exits
      exact ⟨1, Nat.le_add_left 1 _,
        by rw [recAux_succ]; simp [Nat.recAux, partial_ack_step, h_below]⟩
    · -- cwnd > ssthresh: take one step; gap shrinks
      push_neg at h_below
      obtain ⟨k', hk'le, hk'exit⟩ := ih (partial_ack_step s MSS) MSS h_MSS
          (new_gap_le s MSS h_MSS h_below m h_gap)
      exact ⟨k' + 1, by omega, by rw [← recAux_prepend]; exact hk'exit⟩

/-- New-Reno fast-retransmit cwnd recovery.
    After fast retransmit, cwnd recovers to ssthresh within
    (cwnd₀ - ssthresh).toNat + 1 partial-ACK steps.

    This is the correct summable-form bound (RFC 6582 §3).  See module
    header for why the spec's original bound k ≤ cwnd.toNat was relaxed. -/
theorem new_reno_fast_retransmit_cwnd_recovery
    (s0 : RecoveryState) (MSS : Int) (h_MSS : 0 < MSS) (h_cwnd : 0 < s0.cwnd) :
    ∃ k : Nat, k ≤ (s0.cwnd - s0.ssthresh).toNat + 1 ∧
      ¬(Nat.recAux (motive := fun _ => RecoveryState) s0
          (fun _ s => partial_ack_step s MSS) k).in_recovery := by
  obtain ⟨k, hkle, hkexit⟩ :=
    exists_exit_aux (s0.cwnd - s0.ssthresh).toNat s0 MSS h_MSS (le_refl _)
  exact ⟨k, hkle, by simp [hkexit]⟩

end Pythia.Networking.NewRenoRecovery
