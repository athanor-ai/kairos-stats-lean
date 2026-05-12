import Mathlib

-- Interrupt controller safety: no interrupt is lost,
-- priorities are respected, and masking works correctly.
-- Common in SoC verification for production SoC designs.

variable {n : ℕ}

structure InterruptState (n : ℕ) where
  pending : Fin n → Bool
  mask    : Fin n → Bool
  priority : Fin n → ℕ

def isEnabled (s : InterruptState n) (i : Fin n) : Bool :=
  s.pending i && s.mask i

def highestPriority (s : InterruptState n) : Option (Fin n) :=
  (Finset.univ.filter (fun i => isEnabled s i)).image
    (fun i => toLex (s.priority i, i)) |>.max |>.map (Prod.snd ∘ ofLex)

def acknowledgeInterrupt (s : InterruptState n) (i : Fin n) : InterruptState n :=
  { s with pending := Function.update s.pending i false }

def maskInterrupt (s : InterruptState n) (i : Fin n) : InterruptState n :=
  { s with mask := Function.update s.mask i false }

-- Masking prevents interrupt from being enabled
theorem mask_disables (s : InterruptState n) (i : Fin n) :
    isEnabled (maskInterrupt s i) i = false := by
  unfold isEnabled maskInterrupt
  simp [Function.update_self]

-- Acknowledging clears the pending bit
theorem ack_clears_pending (s : InterruptState n) (i : Fin n) :
    (acknowledgeInterrupt s i).pending i = false := by
  unfold acknowledgeInterrupt
  simp [Function.update_self]

-- Masking one interrupt doesn't affect others
theorem mask_preserves_other (s : InterruptState n) (i j : Fin n) (h : i ≠ j) :
    isEnabled (maskInterrupt s i) j = isEnabled s j := by
  unfold isEnabled maskInterrupt
  simp [Function.update_of_ne h.symm]

-- Acknowledging one interrupt doesn't affect others
theorem ack_preserves_other (s : InterruptState n) (i j : Fin n) (h : i ≠ j) :
    isEnabled (acknowledgeInterrupt s i) j = isEnabled s j := by
  unfold isEnabled acknowledgeInterrupt
  simp [Function.update_of_ne h.symm]
