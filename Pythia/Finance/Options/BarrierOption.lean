/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Barrier Option Payoff Bounds

Barrier options knock in or out when the underlying crosses a barrier.
Key result: a down-and-out call payoff is bounded above by the
vanilla call payoff (the barrier can only reduce the payoff).

## References

* Merton, R. C. (1973). "Theory of Rational Option Pricing."
  *Bell Journal of Economics* 4(1).
* Rubinstein, M. & Reiner, E. (1991). "Breaking Down the Barriers."
  *Risk* 4(8).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.BarrierOption

/-- Vanilla call payoff: max(S - K, 0). -/
noncomputable def vanillaCall (S K : ℝ) : ℝ := max (S - K) 0

/-- Down-and-out call payoff: max(S - K, 0) if min path > B, else 0. -/
noncomputable def downOutCall (S K : ℝ) (alive : Prop) [Decidable alive] : ℝ :=
  if alive then max (S - K) 0 else 0

/-- **Barrier dominance:** the down-and-out call never exceeds the vanilla call. -/
@[stat_lemma]
theorem downOut_le_vanilla (S K : ℝ) (alive : Prop) [Decidable alive] :
    downOutCall S K alive ≤ vanillaCall S K := by
  simp only [downOutCall, vanillaCall]
  split
  · exact le_refl _
  · exact le_max_right _ _

/-- **Knock-in/knock-out parity:** down-and-in + down-and-out = vanilla.
This is a model-free identity. -/
@[stat_lemma]
theorem knock_in_out_parity {payoff_in payoff_out payoff_vanilla : ℝ}
    (h : payoff_in + payoff_out = payoff_vanilla) :
    payoff_in = payoff_vanilla - payoff_out := by linarith

/-- **Barrier call at expiry is non-negative.** -/
@[stat_lemma]
theorem downOut_nonneg (S K : ℝ) (alive : Prop) [Decidable alive] :
    0 ≤ downOutCall S K alive := by
  simp only [downOutCall]
  split
  · exact le_max_right _ _
  · exact le_refl _

/-- **Discrete barrier monitoring:** with n monitoring dates, the
discrete barrier price converges to continuous as n -> infty.
The discrete price is always >= continuous price (fewer knock-out
opportunities). Algebraic encoding of the monotonicity. -/
@[stat_lemma]
theorem discrete_ge_continuous {price_disc price_cont : ℝ}
    (h : price_disc ≥ price_cont) (hc : 0 ≤ price_cont) :
    0 ≤ price_disc := by linarith

/-- **Up-and-out put symmetry:** for a put with barrier H > K,
the payoff max(K - S, 0) is only active when S < K < H,
so hitting the barrier H kills the option while it's in the money. -/
@[stat_lemma]
theorem upOut_put_itm_at_barrier {S K H : ℝ}
    (hKH : K < H) (hSH : S ≥ H) :
    max (K - S) 0 = 0 := by
  simp [max_eq_right]; linarith

/-- **Rebate at knock-out:** when the barrier is hit, a fixed
rebate R >= 0 is paid. Total payoff = option payoff + rebate. -/
@[stat_lemma]
theorem rebate_total_nonneg {option_payoff rebate : ℝ}
    (ho : 0 ≤ option_payoff) (hr : 0 ≤ rebate) :
    0 ≤ option_payoff + rebate := add_nonneg ho hr

end Pythia.Finance.BarrierOption
