/-
Pythia.Hardware.ECC — Hamming distance error detection/correction
guarantees for linear codes.

Every ASIC memory controller relies on this: a (n, k, d) linear
code with minimum distance d detects all ≤(d-1)-bit errors and
corrects all ≤⌊(d-1)/2⌋-bit errors. Standard coding theory but
not in Mathlib or any Lean4 ecosystem library.

Aristotle target.
-/

import Mathlib

namespace Pythia.Hardware

/-- Hamming weight: number of 1-bits in a natural number. -/
noncomputable def hammingWeight (x : ℕ) : ℕ := (Nat.bits x).count true

/-- Hamming distance between two values. -/
noncomputable def hammingDist (x y : ℕ) : ℕ := hammingWeight (x ^^^ y)

/-- Hamming distance is a metric: triangle inequality. -/
theorem hamming_triangle (x y z : ℕ) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  sorry

/-- Hamming distance is symmetric. -/
theorem hamming_symm (x y : ℕ) :
    hammingDist x y = hammingDist y x := by
  sorry

/-- A code with minimum distance d detects all error patterns of
weight ≤ d - 1. No valid codeword is within d-1 of another, so
any perturbation of weight < d lands outside the codebook. -/
theorem detection_capacity
    (codewords : Finset ℕ)
    (d : ℕ) (hd : 2 ≤ d)
    (h_min_dist : ∀ c₁ ∈ codewords, ∀ c₂ ∈ codewords,
      c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (c : ℕ) (hc : c ∈ codewords)
    (e : ℕ) (he : 0 < hammingWeight e) (he_small : hammingWeight e ≤ d - 1) :
    c ^^^ e ∉ codewords := by
  sorry

/-- A code with minimum distance d corrects all error patterns of
weight ≤ ⌊(d-1)/2⌋. The Hamming spheres of radius t = ⌊(d-1)/2⌋
around each codeword are disjoint, so nearest-codeword decoding
uniquely recovers the original. -/
theorem correction_capacity
    (codewords : Finset ℕ)
    (d : ℕ) (hd : 3 ≤ d)
    (h_min_dist : ∀ c₁ ∈ codewords, ∀ c₂ ∈ codewords,
      c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (c : ℕ) (hc : c ∈ codewords)
    (e : ℕ) (he : hammingWeight e ≤ (d - 1) / 2) :
    ∀ c' ∈ codewords, c' ≠ c →
      hammingDist (c ^^^ e) c < hammingDist (c ^^^ e) c' := by
  sorry

/-- Singleton bound: a code of length n with minimum distance d
has at most 2^(n-d+1) codewords. -/
theorem singleton_bound (n d : ℕ) (hd : d ≤ n + 1)
    (codewords : Finset ℕ)
    (h_len : ∀ c ∈ codewords, c < 2 ^ n)
    (h_min_dist : ∀ c₁ ∈ codewords, ∀ c₂ ∈ codewords,
      c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
    codewords.card ≤ 2 ^ (n - d + 1) := by
  sorry

end Pythia.Hardware
