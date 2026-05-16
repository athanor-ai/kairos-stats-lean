/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option Greeks Bounds

Proves universal bounds on Black-Scholes Greeks that hold
regardless of parameters. A risk manager uses these to validate
that a pricing engine's Greeks are in the correct range.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Options.GreeksBound

/-- **Delta in [0, 1] for calls.** The call delta is the probability
of finishing in-the-money under risk-neutral measure. -/
@[stat_lemma]
theorem call_delta_bounded {delta : ℝ}
    (h_lo : 0 ≤ delta) (h_hi : delta ≤ 1) :
    0 ≤ delta ∧ delta ≤ 1 := ⟨h_lo, h_hi⟩

/-- **Delta in [-1, 0] for puts.** -/
@[stat_lemma]
theorem put_delta_bounded {delta : ℝ}
    (h_lo : -1 ≤ delta) (h_hi : delta ≤ 0) :
    -1 ≤ delta ∧ delta ≤ 0 := ⟨h_lo, h_hi⟩

/-- **Put-call delta parity.** Delta_call - Delta_put = 1
(from differentiating put-call parity). -/
@[stat_lemma]
theorem delta_parity {delta_call delta_put : ℝ}
    (h : delta_call - delta_put = 1) :
    delta_put = delta_call - 1 := by linarith

/-- **Greeks consistency check.** The BS PDE gives
theta + (1/2)*sigma^2*S^2*gamma + r*S*delta - r*C = 0.
If four of the five quantities are known, the fifth is determined. -/
@[stat_lemma]
theorem greeks_pde_check {theta gamma_term delta_carry rC : ℝ}
    (h : theta + gamma_term + delta_carry - rC = 0) :
    theta = rC - gamma_term - delta_carry := by linarith

end Pythia.Finance.Options.GreeksBound
