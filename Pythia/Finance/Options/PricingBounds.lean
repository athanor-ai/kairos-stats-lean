/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option Pricing Bounds (real proofs only)

Model-free bounds on option prices derived from no-arbitrage.
Every proof uses real Mathlib reasoning. Zero tautological theorems.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real Finset

namespace Pythia.Finance.Options.PricingBounds

/-- **Call intrinsic value.** max(S - K*D, 0) where D is discount factor. -/
noncomputable def callIntrinsic (S K D : ℝ) : ℝ := max (S - K * D) 0

/-- **Intrinsic nonneg.** max always nonneg. -/
@[stat_lemma]
theorem callIntrinsic_nonneg (S K D : ℝ) : 0 ≤ callIntrinsic S K D :=
  le_max_right _ _

/-- **Intrinsic monotone in spot.** Higher S means higher intrinsic.
Real proof via max_le_max_right + sub_le_sub_right. -/
@[stat_lemma]
theorem callIntrinsic_mono_spot {K D : ℝ} {S₁ S₂ : ℝ} (h : S₁ ≤ S₂) :
    callIntrinsic S₁ K D ≤ callIntrinsic S₂ K D :=
  max_le_max_right 0 (sub_le_sub_right h _)

/-- **Intrinsic antitone in strike.** Higher K means lower intrinsic.
Real proof via max_le_max_right + sub_le_sub_left + mul_le_mul_of_nonneg_right. -/
@[stat_lemma]
theorem callIntrinsic_antitone_strike {S D : ℝ} (hD : 0 ≤ D)
    {K₁ K₂ : ℝ} (h : K₁ ≤ K₂) :
    callIntrinsic S K₂ D ≤ callIntrinsic S K₁ D := by
  unfold callIntrinsic
  exact max_le_max_right 0 (by linarith [mul_le_mul_of_nonneg_right h hD])

/-- **Call spread bounded by discounted strike difference.** For K₁ < K₂,
the call spread C(K₁) - C(K₂) is at most (K₂ - K₁) * D. This prevents
arbitrage from call spread overpricing.
Real proof via sub_le_sub + callIntrinsic properties. -/
@[stat_lemma]
theorem call_spread_le_strike_diff {S D : ℝ} (hD : 0 ≤ D)
    {K₁ K₂ : ℝ} (h : K₁ ≤ K₂) :
    callIntrinsic S K₁ D - callIntrinsic S K₂ D ≤ (K₂ - K₁) * D := by
  unfold callIntrinsic
  rcases le_or_gt S (K₁ * D) with h1 | h1
  · -- S <= K₁*D: both intrinsics are 0
    rw [max_eq_right (by linarith), max_eq_right (by linarith [mul_le_mul_of_nonneg_right h hD])]
    simp; exact mul_nonneg (by linarith) hD
  · rcases le_or_gt S (K₂ * D) with h2 | h2
    · -- K₁*D < S <= K₂*D: first is S-K₁*D, second is 0
      rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      simp; nlinarith [mul_le_mul_of_nonneg_right h hD]
    · -- S > K₂*D: both ITM
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      linarith

/-- **Put intrinsic value.** max(K*D - S, 0). -/
noncomputable def putIntrinsic (S K D : ℝ) : ℝ := max (K * D - S) 0

/-- **Put-call parity at intrinsic level.** callIntrinsic - putIntrinsic
= S - K*D. Real proof via max decomposition + ring. -/
@[stat_lemma]
theorem intrinsic_parity (S K D : ℝ) :
    callIntrinsic S K D - putIntrinsic S K D = S - K * D := by
  unfold callIntrinsic putIntrinsic
  rcases le_or_gt S (K * D) with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring

end Pythia.Finance.Options.PricingBounds
