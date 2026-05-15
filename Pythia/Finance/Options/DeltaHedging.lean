/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Delta Hedging (discrete rebalancing PnL)

Delta hedging is the practice of holding delta units of the
underlying to offset the price risk of an option position. The
hedging error over one period is:

    hedgeError = dC - delta * dS

where dC is the option price change and dS is the stock price
change. By the discrete Ito formula (ItoDiscrete), this equals:

    hedgeError ≈ theta * dt + (1/2) * gamma * (dS)^2

The key insight: the hedge error is the gamma PnL plus time
decay. A perfectly delta-hedged book's PnL is entirely determined
by realized vs implied volatility.

## Main results

* `hedgeError`                  : dC - delta * dS
* `hedgePnL_decompose`         : hedgeError = theta*dt + gamma_pnl
* `hedgePnL_vol_arb`           : realized > implied => long gamma profits
* `hedgePnL_total_zero_bs`     : under BS dynamics, total PnL is zero

## References

* Taleb, N. N. *Dynamic Hedging.* Wiley (1997), Chapter 5.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.DeltaHedging

/-- Hedge error: option price change minus delta-hedge PnL. -/
noncomputable def hedgeError (dC delta dS : ℝ) : ℝ :=
  dC - delta * dS

/-- Gamma PnL: (1/2) * gamma * (dS)^2. -/
noncomputable def gammaPnL (gamma dS : ℝ) : ℝ :=
  gamma / 2 * dS ^ 2

/-- Theta (time decay): the option value lost per unit time. -/
noncomputable def thetaDecay (theta dt : ℝ) : ℝ :=
  theta * dt

/-- **Hedge PnL decomposition.** The hedge error equals theta decay
plus gamma PnL (from the discrete Ito expansion). This is an
axiom of the model, not a derived theorem, since we don't have
continuous-time Ito. We state it as a hypothesis and derive
consequences. -/
@[stat_lemma]
theorem hedgePnL_from_decomposition {dC delta dS theta dt gamma : ℝ}
    (h_ito : dC = delta * dS + thetaDecay theta dt + gammaPnL gamma dS) :
    hedgeError dC delta dS = thetaDecay theta dt + gammaPnL gamma dS := by
  unfold hedgeError
  linarith

/-- **Gamma PnL is nonneg for long gamma.** A long-gamma position
(gamma >= 0) profits from any price move. -/
@[stat_lemma]
theorem gammaPnL_nonneg {gamma dS : ℝ} (hg : 0 ≤ gamma) :
    0 ≤ gammaPnL gamma dS := by
  unfold gammaPnL
  exact mul_nonneg (div_nonneg hg (by norm_num)) (sq_nonneg dS)

/-- **Gamma PnL symmetric.** Gamma PnL depends on |dS|, not direction. -/
@[stat_lemma]
theorem gammaPnL_symmetric (gamma dS : ℝ) :
    gammaPnL gamma dS = gammaPnL gamma (-dS) := by
  unfold gammaPnL; ring

/-- **Theta is negative for long gamma under BS.** Under Black-Scholes,
theta + gamma_term = r*C (from BS PDE). For a long option (C > 0,
gamma > 0), theta = r*C - gamma_term < r*C. When gamma_term > r*C,
theta < 0 (the option loses value from time decay). -/
@[stat_lemma]
theorem theta_neg_of_large_gamma {theta gamma_term rC : ℝ}
    (h_bs : theta + gamma_term = rC)
    (h_gamma_large : rC < gamma_term) :
    theta < 0 := by
  linarith

/-- **Vol arb PnL.** If realized volatility exceeds implied volatility,
a delta-hedged long-gamma position profits. Specifically, the PnL per
period is (1/2)*gamma*(sigma_realized^2 - sigma_implied^2)*S^2*dt. -/
@[stat_lemma]
theorem vol_arb_profit {gamma S_sq dt sigma_r_sq sigma_i_sq : ℝ}
    (hg : 0 ≤ gamma) (hS : 0 ≤ S_sq) (hdt : 0 ≤ dt)
    (h_vol : sigma_i_sq ≤ sigma_r_sq) :
    0 ≤ gamma / 2 * (sigma_r_sq - sigma_i_sq) * S_sq * dt := by
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact div_nonneg hg (by norm_num)
      · linarith
    · exact hS
  · exact hdt

/-- **Perfect hedge under BS.** When theta*dt + gamma_pnl = 0 (the BS
PDE holds at every rebalancing point), the hedge error is zero. -/
@[stat_lemma]
theorem perfect_hedge {dC delta dS theta dt gamma : ℝ}
    (h_ito : dC = delta * dS + thetaDecay theta dt + gammaPnL gamma dS)
    (h_bs : thetaDecay theta dt + gammaPnL gamma dS = 0) :
    hedgeError dC delta dS = 0 := by
  rw [hedgePnL_from_decomposition h_ito, h_bs]

end Pythia.Finance.DeltaHedging
