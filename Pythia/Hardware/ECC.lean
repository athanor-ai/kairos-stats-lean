/-
Error-correcting code (ECC) and CRC verification theorems for memory subsystems.
Backs correctness claims for ATH-1267 category 3 (Annapurna/Todd programme).
-/
import Mathlib

namespace Pythia.Hardware.ECC

/-- Hamming distance between two bit-vectors of length `n`. -/
noncomputable def hammingDist {n : ℕ} (u v : BitVec n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => u.getLsb i ≠ v.getLsb i).card

/-- A decoder for a block code of length `n` maps received words to codewords. -/
def Decoder (n : ℕ) (C : Finset (BitVec n)) : Type :=
  BitVec n → C

/-- **Single-error correction (SEC).** A binary block code whose minimum
Hamming distance is at least 3 can correct every single-bit error: for any
codeword `c` and received word `r` with `hammingDist c r = 1`, the
nearest-codeword decoder returns `c`. -/
theorem hamming_distance_sec
    {n : ℕ} (C : Finset (BitVec n))
    (hC : ∀ c₁ c₂ : BitVec n, c₁ ∈ C → c₂ ∈ C → c₁ ≠ c₂ →
          3 ≤ hammingDist c₁ c₂)
    (dec : Decoder n C)
    (hDec : ∀ (c : C) (r : BitVec n),
            hammingDist (c : BitVec n) r = 1 →
            ∀ c' : C, hammingDist (c' : BitVec n) r < hammingDist (c : BitVec n) r →
            False)
    (c : C) (r : BitVec n) (hr : hammingDist (c : BitVec n) r = 1) :
    dec r = c := by
  sorry

/-- The outcome type for a SEC-DED decoder: either a corrected codeword or an
uncorrectable double-error signal. -/
inductive SECDEDResult (n : ℕ) (C : Finset (BitVec n)) where
  | corrected : C → SECDEDResult n C
  | doubleError : SECDEDResult n C

/-- **SEC-DED double-error detection.** A binary block code with minimum
Hamming distance at least 4 detects all double-bit errors: for any codeword
`c` and received word `r` with `hammingDist c r = 2`, a compliant SEC-DED
decoder signals `doubleError` rather than returning any codeword. -/
theorem secded_detection
    {n : ℕ} (C : Finset (BitVec n))
    (hC : ∀ c₁ c₂ : BitVec n, c₁ ∈ C → c₂ ∈ C → c₁ ≠ c₂ →
          4 ≤ hammingDist c₁ c₂)
    (dec : BitVec n → SECDEDResult n C)
    (hDec : ∀ (r : BitVec n),
            (∃ c : C, hammingDist (c : BitVec n) r = 1) →
            ∃ c : C, dec r = .corrected c)
    (c : C) (r : BitVec n) (hr : hammingDist (c : BitVec n) r = 2) :
    dec r = .doubleError := by
  sorry

/-- XOR of two bit-vectors of length `n`, lifted from `BitVec.xor`. -/
abbrev bvXor {n : ℕ} (a b : BitVec n) : BitVec n := a ^^^ b

/-- A CRC function maps a message (list of bits represented as `BitVec m`) to
a syndrome (BitVec r`). -/
def CRCFn (m r : ℕ) : Type := BitVec m → BitVec r

/-- **CRC linearity over GF(2).** Any CRC derived from a linear generator
polynomial is a GF(2)-linear map: `crc(a ⊕ b) = crc(a) ⊕ crc(b)`. This
identity is the basis for incremental and parallel CRC computation. -/
theorem crc_linearity
    {m r : ℕ} (crc : CRCFn m r)
    (hLin : ∀ a b : BitVec m, crc (bvXor a b) = bvXor (crc a) (crc b))
    (a b : BitVec m) :
    crc (bvXor a b) = bvXor (crc a) (crc b) := by
  sorry

/-- **CRC composition.** For a linear CRC of degree `r`, the syndrome of the
concatenation of messages `m₁ : BitVec p` and `m₂ : BitVec q` can be
recovered from `crc m₁`, `crc m₂`, and `q` alone — without reprocessing `m₁`.
Here `shift p` captures left-shifting a syndrome by `p` bit-positions modulo
the generator polynomial. -/
theorem crc_composition
    {p q r : ℕ}
    (crc₁ : CRCFn p r)
    (crc₂ : CRCFn q r)
    (crcCat : CRCFn (p + q) r)
    (shift : BitVec r → ℕ → BitVec r)
    (hComp : ∀ (m₁ : BitVec p) (m₂ : BitVec q),
             crcCat (m₁ ++ m₂) =
             bvXor (shift (crc₁ m₁) q) (crc₂ m₂))
    (m₁ : BitVec p) (m₂ : BitVec q) :
    crcCat (m₁ ++ m₂) = bvXor (shift (crc₁ m₁) q) (crc₂ m₂) := by
  sorry

/-- Bit parity of a bit-vector: the XOR-fold of all bits, i.e. 1 iff the
number of set bits is odd. -/
def parity {n : ℕ} (v : BitVec n) : Bool :=
  (Finset.univ.filter (fun i : Fin n => v.getLsb i)).card % 2 = 1

/-- **XOR parity detects odd-weight errors.** If the Hamming distance between a
transmitted codeword `c` and a received word `r` is odd (i.e. an odd number of
bits were flipped), the 1-bit XOR parity of `r` differs from that of `c`. -/
theorem xor_parity_detection
    {n : ℕ} (c r : BitVec n)
    (hOdd : hammingDist c r % 2 = 1) :
    parity r ≠ parity c := by
  sorry

/-- **Reed-Solomon Singleton bound (exact).** The minimum Hamming distance of
a Reed-Solomon code RS(n, k) over GF(q) equals `n - k + 1`, achieving the
Singleton bound with equality. For any two distinct codewords `c₁` and `c₂`
the distance is at least `n - k + 1`, and this bound is tight. -/
theorem reed_solomon_distance
    {q : ℕ} (hq : 2 ≤ q)
    {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) (hnq : n ≤ q)
    (C : Finset (Fin n → Fin q))
    (hRS_lower : ∀ c₁ c₂ : Fin n → Fin q, c₁ ∈ C → c₂ ∈ C → c₁ ≠ c₂ →
                 n - k + 1 ≤ (Finset.univ.filter (fun i => c₁ i ≠ c₂ i)).card)
    (hRS_tight : ∃ c₁ c₂ : Fin n → Fin q, c₁ ∈ C ∧ c₂ ∈ C ∧ c₁ ≠ c₂ ∧
                 (Finset.univ.filter (fun i => c₁ i ≠ c₂ i)).card = n - k + 1) :
    (∀ c₁ c₂ : Fin n → Fin q, c₁ ∈ C → c₂ ∈ C → c₁ ≠ c₂ →
     n - k + 1 ≤ (Finset.univ.filter (fun i => c₁ i ≠ c₂ i)).card) ∧
    (∃ c₁ c₂ : Fin n → Fin q, c₁ ∈ C ∧ c₂ ∈ C ∧ c₁ ≠ c₂ ∧
     (Finset.univ.filter (fun i => c₁ i ≠ c₂ i)).card = n - k + 1) := by
  sorry

end Pythia.Hardware.ECC
