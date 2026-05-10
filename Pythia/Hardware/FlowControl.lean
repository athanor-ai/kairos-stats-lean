import Mathlib

-- Credit-based flow control correctness.
-- Common in NoC and interconnect designs.
-- Sender can only send when it has credits.
-- Receiver returns credits after consuming data.

structure FlowState where
  credits : ℕ
  max_credits : ℕ
  in_flight : ℕ

def canSend (s : FlowState) : Bool := decide (0 < s.credits)

def sendPacket (s : FlowState) (h : 0 < s.credits) : FlowState :=
  { s with credits := s.credits - 1, in_flight := s.in_flight + 1 }

def returnCredit (s : FlowState) (h : 0 < s.in_flight) : FlowState :=
  { s with credits := s.credits + 1, in_flight := s.in_flight - 1 }

-- Credits + in_flight = max_credits (conservation)
def creditsConserved (s : FlowState) : Prop :=
  s.credits + s.in_flight = s.max_credits

-- Send preserves conservation
theorem send_preserves_credits (s : FlowState)
    (h_cons : creditsConserved s) (h_send : 0 < s.credits) :
    creditsConserved (sendPacket s h_send) := by
  unfold creditsConserved at h_cons ⊢
  unfold sendPacket
  simp only
  omega

-- Return preserves conservation
theorem return_preserves_credits (s : FlowState)
    (h_cons : creditsConserved s) (h_ret : 0 < s.in_flight) :
    creditsConserved (returnCredit s h_ret) := by
  unfold creditsConserved at h_cons ⊢
  unfold returnCredit
  simp only
  omega

-- No send when no credits (deadlock freedom under conservation)
theorem no_send_zero_credits (s : FlowState)
    (h_cons : creditsConserved s) (h_full : s.in_flight = s.max_credits) :
    s.credits = 0 := by
  unfold creditsConserved at h_cons
  omega
