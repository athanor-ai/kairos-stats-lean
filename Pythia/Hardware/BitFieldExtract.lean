import Mathlib

-- Bit field extraction and insertion correctness.
-- Fundamental for register access in SoC designs.
-- Extract bits [hi:lo] from a bitvector, insert back preserves other bits.

variable {n w : ℕ}

def extractBits (x : BitVec n) (lo hi : ℕ) (h : lo ≤ hi) (h2 : hi < n) : BitVec (hi - lo + 1) :=
  (x >>> lo).truncate (hi - lo + 1)

def insertBits (x : BitVec n) (lo : ℕ) (field : BitVec w) : BitVec n :=
  let mask := (BitVec.allOnes w).zeroExtend n <<< lo
  (x &&& ~~~mask) ||| ((field.zeroExtend n) <<< lo)

/-
Extract after insert returns the inserted value
-/
theorem extract_insert_roundtrip (x : BitVec n) (lo : ℕ) (field : BitVec w)
    (h : lo + w ≤ n) (hw : 0 < w) :
    extractBits (insertBits x lo field) lo (lo + w - 1) (by omega) (by omega) =
      field.cast (by omega) := by
  have h_eq : ∀ (i : Fin w), BitVec.getLsbD (insertBits x lo field) (lo + i.val) = field.getLsbD i := by
    unfold insertBits;
    grind;
  ext i;
  convert h_eq ⟨ i, by omega ⟩ using 1;
  grind +locals

/-
Insert preserves bits outside the field
-/
theorem insert_preserves_other (x : BitVec n) (lo : ℕ) (field : BitVec w)
    (i : ℕ) (h_below : i < lo) :
    (insertBits x lo field).getLsbD i = x.getLsbD i := by
  unfold insertBits;
  grind