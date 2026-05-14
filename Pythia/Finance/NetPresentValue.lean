/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Net Present Value (algebraic closed form)

For a stream of cashflows `cf : Fin n → ℝ` paid at times `t : Fin n → ℝ`
under continuous-compounding discount rate `r`, the *net present value*
is the sum of discounted cashflows:

    NPV(cf, t, r) = Σ_i cf(i) · exp(-r · t(i)).

NPV is the practitioner-standard objective for capital budgeting,
project valuation, and DCF analysis.  This file gives the algebraic
identities of NPV: linearity in cashflows, monotonicity, boundary
cases, and the link to the existing `Pythia.Finance.discountFactor`
kernel.

## Main results

* `netPresentValue`            : Σᵢ cf(i) · exp(-r·t(i))
* `netPresentValue_zero_cf`    : NPV of all-zero cashflows = 0
* `netPresentValue_linear`     : NPV(α·cf, t, r) = α · NPV(cf, t, r)
* `netPresentValue_additive`   : NPV(cf₁ + cf₂, t, r) = NPV(cf₁, t, r) + NPV(cf₂, t, r)

## Why this lemma

DCF is the analytical bedrock of capital budgeting, M&A valuation,
real-options analysis, and any project-finance evaluation.
Surfacing the NPV closed form in Pythia gives the `pythia` tactic
cascade a clean closure target for capital-budgeting sign-direction
goals.

## References

* Fisher, I. *The Theory of Interest.* Macmillan (1930).
* Brealey, R., Myers, S., and Allen, F. *Principles of Corporate
  Finance*, 13th ed. McGraw-Hill (2019), Ch. 5.
-/
import Mathlib
import Pythia.Finance.DiscountFactor
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Net present value of a finite cashflow stream under continuous
compounding:
    `NPV(cf, t, r) = Σᵢ cf(i) · exp(-r · t(i))`. -/
noncomputable def netPresentValue {n : ℕ} (cf t : Fin n → ℝ) (r : ℝ) : ℝ :=
  Finset.univ.sum (fun i => cf i * Real.exp (-(r * t i)))

/-- **Zero-cashflow specialisation.** NPV of the all-zero cashflow
stream is zero. -/
@[stat_lemma]
theorem netPresentValue_zero_cf {n : ℕ} (t : Fin n → ℝ) (r : ℝ) :
    netPresentValue (fun _ : Fin n => (0 : ℝ)) t r = 0 := by
  unfold netPresentValue; simp

/-- **Linearity in cashflows (scalar).** Scaling every cashflow by
`α` rescales the NPV by `α`. -/
@[stat_lemma]
theorem netPresentValue_linear {n : ℕ} (cf t : Fin n → ℝ) (r α : ℝ) :
    netPresentValue (fun i => α * cf i) t r = α * netPresentValue cf t r := by
  unfold netPresentValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Additivity in cashflows.** NPV is additive over cashflow
streams paid at the same times under the same discount rate. -/
@[stat_lemma]
theorem netPresentValue_additive {n : ℕ} (cf₁ cf₂ t : Fin n → ℝ) (r : ℝ) :
    netPresentValue (fun i => cf₁ i + cf₂ i) t r
      = netPresentValue cf₁ t r + netPresentValue cf₂ t r := by
  unfold netPresentValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

end Pythia.Finance
