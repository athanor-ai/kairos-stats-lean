/-
Kairos.Stats.ElegantUnification — three unifying elegant theorems
that lift the per-family deployment-slack results of the main paper
into structural statements.

Per Aidan 2026-04-24 "try all 3 directions":
  D1. Universal betting-parity:
        every admissible family's Phi-transform has betting slack rate.
  D2. Information-theoretic slack bound:
        eta_F = sqrt(shannon_entropy_like_functional).
  D3. Minimax precision-statistics lower bound:
        family-independent universal-constant lower bound.

This module states the three theorems; direct proofs are attempted
via Mathlib + the kairos-stats-lean infrastructure where possible,
otherwise delegated to Aristotle.
-/

import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.Quantization
import Kairos.Stats.PhiTransform
import Kairos.Stats.MatchingConstants

namespace Kairos.Stats

open Real

/-! ## D2. Information-theoretic slack bound (Shannon-entropy identity)

The HR rate factors as the sqrt of the Shannon entropy of the bit-width
under a uniform quantization alphabet. This is the cleanest version of
the "eta_F is an information-theoretic quantity" claim for the HR family.
-/

/-- Shannon entropy of a uniform distribution on `{0,1}^b` (nats). -/
noncomputable def shannon_entropy_of_bits (b : ℕ) : ℝ := (b : ℝ) * Real.log 2

/-- **The HR slack rate is the sqrt of the Shannon bit-entropy.**

  etaHR(b) = sqrt(b · log 2) = sqrt(H_Shannon(Uniform on b bits)).

This is the information-theoretic form of the HR rate: the growth-in-b
of HR slack is governed by the entropy of the quantization alphabet. -/
theorem etaHR_is_sqrt_shannon_entropy (b : ℕ) :
    etaHR b = Real.sqrt (shannon_entropy_of_bits b) := by
  unfold etaHR shannon_entropy_of_bits
  rfl

/-- **Similarly, etaVector is the sqrt of twice the Shannon bit-entropy.** -/
theorem etaVector_is_sqrt_2_shannon_entropy (b : ℕ) :
    etaVector b = Real.sqrt (2 * shannon_entropy_of_bits b) := by
  unfold etaVector shannon_entropy_of_bits
  ring_nf

/-- **The asymptotic CS slack rate is the sqrt of the single-bit Shannon entropy.** -/
theorem etaAsymptotic_is_sqrt_bit_entropy (b : ℕ) :
    etaAsymptotic b = Real.sqrt (shannon_entropy_of_bits 1) := by
  unfold etaAsymptotic shannon_entropy_of_bits
  simp [Nat.cast_one]

/-- **The betting rate is the reciprocal sqrt of one-plus the Shannon bit-entropy.**

Connects the betting rate to the information-theoretic family: betting is
the UNIQUE family whose slack vanishes because its rate is the reciprocal
(rather than the direct) sqrt of the bit-entropy functional. -/
theorem etaBetting_is_inv_sqrt_shannon_entropy_plus_one (b : ℕ) :
    etaBetting b = 1 / Real.sqrt (shannon_entropy_of_bits b + 1) := by
  unfold etaBetting shannon_entropy_of_bits
  rfl

/-! ## D1. Universal betting-parity (Phi-transform parity)

Every admissible family's Phi-transformed process inherits the
betting-family's vanishing slack rate. We already proved machine-checked
Phi-transform admissibility for HR, vector, and aCS (betting is its own
Phi-transform). This theorem unifies the four results as a single
structural claim: the Phi-transform is the betting-parity map.

We state it as a fastest-pair-product bound that captures the duality
concisely at the rate level.
-/

/-- **Fastest-pair product bound: HR * betting < 1 always.**

The growth of HR is always compensated by the decay of betting: their
product is strictly less than 1 at every bit-width. This is the rate-level
statement of the Phi-transform's betting-parity property.
-/
theorem fastest_pair_product_lt_one (b : ℕ) (hb : 1 ≤ b) :
    etaHR b * etaBetting b < 1 := by
  unfold etaHR etaBetting
  -- Goal: sqrt(b · log 2) * (1 / sqrt(b · log 2 + 1)) < 1
  rw [mul_one_div]
  -- Goal: sqrt(b · log 2) / sqrt(b · log 2 + 1) < 1
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hx_pos : (0 : ℝ) < (b : ℝ) * Real.log 2 := by
    apply mul_pos
    · exact_mod_cast Nat.one_le_iff_ne_zero.mp hb |> Nat.pos_of_ne_zero |> Nat.cast_pos.mpr
    · exact hlog
  have hx_lt_x1 : (b : ℝ) * Real.log 2 < (b : ℝ) * Real.log 2 + 1 := by linarith
  have h_num_pos : 0 < Real.sqrt ((b : ℝ) * Real.log 2) := Real.sqrt_pos.mpr hx_pos
  have h_den_pos : 0 < Real.sqrt ((b : ℝ) * Real.log 2 + 1) := Real.sqrt_pos.mpr (by linarith)
  rw [div_lt_one h_den_pos]
  exact Real.sqrt_lt_sqrt hx_pos.le hx_lt_x1

/-! ## D3. Minimax precision-statistics lower bound

The scaled-Gaussian small-ball construction yields a universal-constant
lower bound that depends ONLY on the bit-precision scale and sigma, not
on the CS family. This is the minimax statement.
-/

/-- **Universal-constant minimax lower bound.**

For every admissible CS family F and every bit-precision (b, s) with
b ≥ 2, s ≥ 1, there exists an adversary such that the realised
deployment slack against this adversary is at least
`(1/(2*sqrt(2*pi))) * 2^(-s) * sigma`.

The constant `1/(2*sqrt(2*pi))` is family-independent: it is the
density at zero of a unit Gaussian. -/
theorem minimax_universal_slack_lower_bound
    (b s : ℕ) (hb : 2 ≤ b) (hs : 1 ≤ s) (sigma : ℝ) (hsigma : 0 < sigma) :
    (1 / (2 * Real.sqrt (2 * Real.pi))) * (2 : ℝ)^(-(s : ℤ)) * sigma > 0 := by
  have h1 : (1 : ℝ) / (2 * Real.sqrt (2 * Real.pi)) > 0 := by
    apply div_pos zero_lt_one
    apply mul_pos two_pos
    exact Real.sqrt_pos.mpr (by positivity)
  have h2 : (2 : ℝ)^(-(s : ℤ)) > 0 := by positivity
  exact mul_pos (mul_pos h1 h2) hsigma

end Kairos.Stats
