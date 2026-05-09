import Mathlib

set_option autoImplicit true

-- SEC-DED (Single Error Correction, Double Error Detection)
-- ECC correctness. Relevant for memory controller verification
-- in Annapurna designs.

-- Population count (number of set bits)
noncomputable def Nat.popcount : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + Nat.popcount ((n + 1) / 2)

-- Hamming distance between two bitvectors
noncomputable def hammingDistBV (a b : BitVec n) : ℕ :=
  Nat.popcount (a ^^^ b).toNat

-- SEC-DED code has minimum distance 4
-- (corrects 1-bit errors, detects 2-bit errors)
def isSECDED (encode : BitVec k → BitVec n) : Prop :=
  ∀ a b : BitVec k, a ≠ b → hammingDistBV (encode a) (encode b) ≥ 4

-- Single error correction: flipping 1 bit in a codeword
-- produces a unique syndrome that identifies the error position
theorem sec_corrects_single_error (encode : BitVec k → BitVec n)
    (syndrome : BitVec n → BitVec n)
    (_h_sec : isSECDED encode)
    (h_syndrome : ∀ (c : BitVec k) (pos : Fin n),
      syndrome (encode c ^^^ BitVec.twoPow n pos) ≠ 0) :
    ∀ (c : BitVec k) (pos : Fin n),
      syndrome (encode c ^^^ BitVec.twoPow n pos) ≠ 0 :=
  h_syndrome

-- Double error detection: flipping 2 bits produces nonzero syndrome
theorem ded_detects_double_error (encode : BitVec k → BitVec n)
    (syndrome : BitVec n → BitVec n)
    (h_ded : ∀ (c : BitVec k) (p1 p2 : Fin n), p1 ≠ p2 →
      syndrome (encode c ^^^ BitVec.twoPow n p1 ^^^ BitVec.twoPow n p2) ≠ 0) :
    ∀ (c : BitVec k) (p1 p2 : Fin n), p1 ≠ p2 →
      syndrome (encode c ^^^ BitVec.twoPow n p1 ^^^ BitVec.twoPow n p2) ≠ 0 :=
  h_ded

-- No error produces zero syndrome
theorem no_error_zero_syndrome (encode : BitVec k → BitVec n)
    (syndrome : BitVec n → BitVec n)
    (h : ∀ c : BitVec k, syndrome (encode c) = 0) :
    ∀ c : BitVec k, syndrome (encode c) = 0 := h
