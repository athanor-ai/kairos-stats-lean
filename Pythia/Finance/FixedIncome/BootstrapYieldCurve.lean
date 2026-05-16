/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Yield Curve Bootstrap (algebraic identities)

Given discount factors D(0,T_i), spot rates satisfy
D(0,T) = exp(-r(T)*T) and forward rates satisfy
D(0,T2)/D(0,T1) = exp(-f(T1,T2)*(T2-T1)).

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, Ch. 4.
* Brigo, D. & Mercurio, F. *Interest Rate Models*, Ch. 1.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance.BootstrapYieldCurve

/-- Forward rate consistency: D(0,T2) = D(0,T1) * exp(-f*(T2-T1)). -/
@[stat_lemma]
theorem forward_rate_consistency {D1 D2 f T1 T2 : ℝ}
    (h : D2 = D1 * exp (-(f * (T2 - T1)))) :
    D2 / D1 = exp (-(f * (T2 - T1))) ∨ D1 = 0 := by
  by_cases hD1 : D1 = 0
  · right; exact hD1
  · left; rw [h, mul_div_cancel_left₀ _ hD1]

/-- Par rate: coupon rate c such that bond prices at par.
sum(c * D_i) + D_n = 1 implies c = (1 - D_n) / sum(D_i). -/
@[stat_lemma]
theorem par_rate {c Dn sumD : ℝ}
    (hsumD : sumD ≠ 0)
    (h : c * sumD + Dn = 1) :
    c = (1 - Dn) / sumD := by
  field_simp at h ⊢; linarith

/-- Discount factor is product of forward discount factors:
D(0,T2) = D(0,T1) * D(T1,T2). -/
axiom discount_chain {D02 D01 D12 : ℝ}
    (h : D02 = D01 * D12) :
    D02 = D01 * D12

/-- Continuously compounded spot rate from discount factor:
r = -ln(D) / T. -/
@[stat_lemma]
theorem spot_rate_from_discount {D T r : ℝ}
    (hT : T ≠ 0) (hD : 0 < D)
    (h : r = -Real.log D / T) :
    D = exp (-r * T) := by
  rw [h]; ring_nf; rw [mul_assoc, mul_inv_cancel₀ hT, mul_one, Real.exp_log hD]

end Pythia.Finance.BootstrapYieldCurve
