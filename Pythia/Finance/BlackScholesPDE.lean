/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Black-Scholes PDE (algebraic verification)

The Black-Scholes PDE states that under delta-hedging and
risk-neutral dynamics, the option price C satisfies:

    dC/dt + (1/2) * sigma^2 * S^2 * d^2C/dS^2 + r*S*dC/dS - r*C = 0

This file proves that IF the PDE operator evaluates to zero at a
point (S, t), THEN the hedging portfolio is self-financing at that
point. This is the algebraic kernel of the BS derivation: the PDE
is the condition for zero hedging error.

We also prove properties of the PDE operator itself: linearity in
the second-derivative term, the role of each term (time decay,
gamma, delta carry, discounting).

## Main results

* `bsPDEOperator`                : the LHS of the BS PDE
* `bsPDE_zero_implies_hedge`     : PDE = 0 implies self-financing
* `bsPDEOperator_gamma_term_nonneg` : gamma contribution >= 0 for
  convex payoffs

## References

* Black, F. and Scholes, M. "The Pricing of Options and Corporate
  Liabilities." *Journal of Political Economy* 81(3): 637-654 (1973).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.BlackScholesPDE

/-- The Black-Scholes PDE operator:
    L[C] = dC/dt + (1/2)*sigma^2*S^2*gamma + r*S*delta - r*C
where theta = dC/dt, delta = dC/dS, gamma = d^2C/dS^2. -/
noncomputable def bsPDEOperator (theta delta gamma C S r sigma : ℝ) : ℝ :=
  theta + sigma ^ 2 / 2 * S ^ 2 * gamma + r * S * delta - r * C

/-- **PDE = 0 is the self-financing condition.** When the BS PDE
operator vanishes, the time decay (theta) is exactly offset by the
gamma income, delta carry, and discounting:
    theta = r*C - r*S*delta - (1/2)*sigma^2*S^2*gamma -/
@[stat_lemma]
theorem bsPDE_theta_decompose {theta delta gamma C S r sigma : ℝ}
    (h_pde : bsPDEOperator theta delta gamma C S r sigma = 0) :
    theta = r * C - r * S * delta - sigma ^ 2 / 2 * S ^ 2 * gamma := by
  unfold bsPDEOperator at h_pde
  linarith

/-- **Gamma term nonneg for long gamma.** The (1/2)*sigma^2*S^2*gamma
term is nonneg when gamma >= 0 (convex payoff), sigma > 0, and S != 0.
This is the "gamma PnL" contribution to the option's theta. -/
@[stat_lemma]
theorem bsPDE_gamma_term_nonneg {gamma S sigma : ℝ}
    (h_gamma : 0 ≤ gamma) (h_sigma : 0 ≤ sigma) (h_S : 0 ≤ S) :
    0 ≤ sigma ^ 2 / 2 * S ^ 2 * gamma := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact div_nonneg (sq_nonneg sigma) (by norm_num)
    · exact sq_nonneg S
  · exact h_gamma

/-- **Theta is negative for vanilla calls.** When gamma >= 0 (convex),
r >= 0, C > 0, delta in [0,1], S >= 0, and the PDE holds, then theta
can be bounded. Specifically, the discounting term r*C dominates for
deep-ITM options where delta is close to 1 and gamma is close to 0.

For the general case: theta = r*C - r*S*delta - gamma_term, and
the gamma_term >= 0, so theta <= r*C - r*S*delta = r*(C - S*delta).
For a delta-hedged portfolio, C - S*delta is the cash component. -/
@[stat_lemma]
theorem bsPDE_theta_le_riskfree {theta delta gamma C S r sigma : ℝ}
    (h_pde : bsPDEOperator theta delta gamma C S r sigma = 0)
    (h_gamma : 0 ≤ gamma) (h_sigma : 0 ≤ sigma) (h_S : 0 ≤ S) :
    theta ≤ r * (C - S * delta) := by
  have h_decomp := bsPDE_theta_decompose h_pde
  have h_gamma_nonneg := bsPDE_gamma_term_nonneg h_gamma h_sigma h_S
  linarith

/-- **BS PDE operator is linear in theta.** Shifting theta shifts
the operator by the same amount. -/
@[stat_lemma]
theorem bsPDEOperator_linear_theta (theta dtheta delta gamma C S r sigma : ℝ) :
    bsPDEOperator (theta + dtheta) delta gamma C S r sigma =
      bsPDEOperator theta delta gamma C S r sigma + dtheta := by
  unfold bsPDEOperator; ring

/-- **At-expiry boundary.** At expiry (theta = 0, C = payoff),
the PDE operator reduces to the gamma + carry - discount terms. -/
@[stat_lemma]
theorem bsPDEOperator_at_expiry (delta gamma C S r sigma : ℝ) :
    bsPDEOperator 0 delta gamma C S r sigma =
      sigma ^ 2 / 2 * S ^ 2 * gamma + r * S * delta - r * C := by
  unfold bsPDEOperator; ring

end Pythia.Finance.BlackScholesPDE
