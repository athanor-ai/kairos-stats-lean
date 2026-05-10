import Mathlib

-- Address decoder correctness.
-- Maps addresses to device select signals.
-- Each address maps to exactly one device.

variable {n : ℕ}

structure AddrRange where
  base : ℕ
  size : ℕ
  h_pos : 0 < size

def inRange (r : AddrRange) (addr : ℕ) : Prop :=
  r.base ≤ addr ∧ addr < r.base + r.size

-- Non-overlapping ranges
def noOverlap (ranges : Fin n → AddrRange) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ addr, ¬(inRange (ranges i) addr ∧ inRange (ranges j) addr)

/-
Each address maps to at most one device
-/
theorem decoder_unique (ranges : Fin n → AddrRange)
    (h : noOverlap ranges) (addr : ℕ) (i j : Fin n)
    (hi : inRange (ranges i) addr) (hj : inRange (ranges j) addr) :
    i = j := by
  exact Classical.not_not.1 fun ij => h i j ij addr ⟨ hi, hj ⟩

-- Range containment is decidable for concrete values
instance range_membership_decidable (r : AddrRange) (addr : ℕ) :
    Decidable (inRange r addr) :=
  decidable_of_iff (r.base ≤ addr ∧ addr < r.base + r.size) Iff.rfl