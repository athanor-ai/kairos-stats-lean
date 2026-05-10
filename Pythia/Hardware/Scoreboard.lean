import Mathlib

-- Scoreboard for out-of-order tracking.
-- Tracks which registers have pending writes.
-- Read must stall if source register has pending write.

variable {n : ℕ}

def Scoreboard (n : ℕ) := Fin n → Bool

def markPending (sb : Scoreboard n) (reg : Fin n) : Scoreboard n :=
  Function.update sb reg true

def clearPending (sb : Scoreboard n) (reg : Fin n) : Scoreboard n :=
  Function.update sb reg false

def hasDependency (sb : Scoreboard n) (src : Fin n) : Bool :=
  sb src

def emptyScoreboard : Scoreboard n := fun _ => false

-- Empty scoreboard has no dependencies
theorem empty_no_deps (src : Fin n) :
    hasDependency (emptyScoreboard : Scoreboard n) src = false := by
  rfl

-- After marking, that register has dependency
theorem mark_creates_dep (sb : Scoreboard n) (reg : Fin n) :
    hasDependency (markPending sb reg) reg = true := by
  simp [hasDependency, markPending, Function.update_self]

-- After clearing, that register has no dependency
theorem clear_removes_dep (sb : Scoreboard n) (reg : Fin n) :
    hasDependency (clearPending sb reg) reg = false := by
  simp [hasDependency, clearPending, Function.update_self]

-- Marking one register doesn't affect others
theorem mark_preserves_other (sb : Scoreboard n) (r1 r2 : Fin n) (h : r1 ≠ r2) :
    hasDependency (markPending sb r1) r2 = hasDependency sb r2 := by
  simp [hasDependency, markPending, Function.update_of_ne (Ne.symm h)]
