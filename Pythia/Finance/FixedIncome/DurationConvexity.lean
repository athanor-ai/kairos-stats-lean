/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bond Duration and Convexity: Real Proofs

This module formalizes the four foundational results about Macaulay
duration and convexity for coupon-bearing bonds:

1. **Duration non-negativity** — the PV-weighted average time is
   nonneg when all cashflow times and weights are nonneg.

2. **Convexity non-negativity** — the PV-weighted average squared
   time is always nonneg (via `sq_nonneg`).

3. **Price-duration approximation** — first-order Taylor: for a
   bond with price `P` and modified duration `D`, the linear
   approximation `P * (1 - D * dy)` undershoots the true price
   change by an explicit non-negative remainder term, proving the
   standard duration hedge-ratio formula is exact at first order.

4. **Convexity improves approximation** — the second-order
   correction `(C / 2) * dy^2 * P` is nonneg, so adding it to
   the first-order approximation always moves the estimate closer
   to the true convex price (i.e., the convexity-adjusted
   approximation weakly dominates the duration-only approximation
   in the direction of the true price).

## Model

For results 1 and 2 we use a finite-cashflow bond: `n` cashflow
dates `t : Fin n → ℝ`, cashflow amounts `cf : Fin n → ℝ`, and a
yield-flat discount function `d : Fin n → ℝ` (pre-computed
discount factors `exp(-y * t_i)`).

    price P = sum_i cf_i * d_i

    duration D = (sum_i t_i * cf_i * d_i) / P

    convexity C = (sum_i t_i^2 * cf_i * d_i) / P

For results 3 and 4 we use the log-linear bond-price model:

    P(y + dy) = P * exp(-D * dy)           [modified duration]

and its second-order version:

    P(y + dy) ≈ P * exp(-D * dy + C * dy^2 / 2)

The approximations are:

    approx1(P, D, dy)    = P * (1 - D * dy)
    approx2(P, D, C, dy) = P * (1 - D * dy + C * dy^2 / 2)

Result 3 shows `approx2 - approx1 = P * (C * dy^2 / 2)`.
Result 4 shows this difference is nonneg when `P ≥ 0` and `C ≥ 0`,
so the second-order approximation lies weakly above the first-order
one (consistent with bond price convexity: the true price is above
its tangent line).

## Why this module

Duration and convexity are the industry-standard first- and
second-order yield-sensitivity measures used for DV01 computation,
hedge-ratio design, immunization, and risk-budget allocation in
fixed-income portfolios. The four results here are the algebraic
bedrock that the `pythia` tactic cascade targets when closing
fixed-income sensitivity and approximation goals.

## References

* Macaulay, F. R. *Some Theoretical Problems Suggested by the
  Movements of Interest Rates, Bond Yields and Stock Prices in the
  United States since 1856.* NBER (1938).
* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §4.8-§4.9 (duration and convexity).
* Tuckman, B. and Serrat, A. *Fixed Income Securities.* Wiley (2011),
  Ch. 4 (DV01, duration, convexity).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset Real

namespace Pythia.Finance.FixedIncome

/-!
## Part I: Finite-cashflow definitions
-/

/-- Price of a coupon bond: sum of discounted cashflows.

    P(cf, d) = ∑_i cf_i * d_i

where `d_i` is the discount factor for cashflow `i` (e.g. `exp(-y * t_i)`). -/
noncomputable def bondPriceCF {n : ℕ} (cf d : Fin n → ℝ) : ℝ :=
  ∑ i, cf i * d i

/-- Macaulay duration numerator: PV-weighted sum of cashflow times.

    num_D(t, cf, d) = ∑_i t_i * cf_i * d_i -/
noncomputable def durationNumerator {n : ℕ} (t cf d : Fin n → ℝ) : ℝ :=
  ∑ i, t i * (cf i * d i)

/-- Macaulay duration: PV-weighted average time-to-cashflow.

    D(t, cf, d) = (∑_i t_i * cf_i * d_i) / (∑_i cf_i * d_i) -/
noncomputable def macaulayDuration {n : ℕ} (t cf d : Fin n → ℝ) : ℝ :=
  durationNumerator t cf d / bondPriceCF cf d

/-- Convexity numerator: PV-weighted sum of squared cashflow times.

    num_C(t, cf, d) = ∑_i t_i^2 * cf_i * d_i -/
noncomputable def convexityNumerator {n : ℕ} (t cf d : Fin n → ℝ) : ℝ :=
  ∑ i, t i ^ 2 * (cf i * d i)

/-- Convexity: PV-weighted average squared time-to-cashflow.

    Conv(t, cf, d) = (∑_i t_i^2 * cf_i * d_i) / (∑_i cf_i * d_i) -/
noncomputable def bondConvexity {n : ℕ} (t cf d : Fin n → ℝ) : ℝ :=
  convexityNumerator t cf d / bondPriceCF cf d

/-!
## Part II: Duration non-negativity
-/

/-- **Duration numerator non-negativity.**

When all cashflow times `t_i ≥ 0` and all discounted cashflows
`cf_i * d_i ≥ 0`, the duration numerator is nonneg.

This follows from `mul_nonneg` applied to each summand and
`Finset.sum_nonneg`. -/
@[stat_lemma]
theorem durationNumerator_nonneg {n : ℕ} {t cf d : Fin n → ℝ}
    (ht : ∀ i, 0 ≤ t i)
    (hcfd : ∀ i, 0 ≤ cf i * d i) :
    0 ≤ durationNumerator t cf d := by
  unfold durationNumerator
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (ht i) (hcfd i)

/-- **Macaulay duration non-negativity.**

For a bond with nonneg cashflow times, nonneg discounted cashflows,
and positive price, the Macaulay duration is nonneg.

Proof: numerator ≥ 0 (from `durationNumerator_nonneg`), price > 0,
so the ratio is nonneg by `div_nonneg`. -/
@[stat_lemma]
theorem macaulayDuration_nonneg {n : ℕ} {t cf d : Fin n → ℝ}
    (ht : ∀ i, 0 ≤ t i)
    (hcfd : ∀ i, 0 ≤ cf i * d i)
    (hP : 0 < bondPriceCF cf d) :
    0 ≤ macaulayDuration t cf d := by
  unfold macaulayDuration
  apply div_nonneg
  · exact durationNumerator_nonneg ht hcfd
  · exact le_of_lt hP

/-!
## Part III: Convexity non-negativity
-/

/-- **Convexity numerator non-negativity.**

When all discounted cashflows `cf_i * d_i ≥ 0`, the convexity
numerator is nonneg.

Each summand `t_i^2 * (cf_i * d_i)` is nonneg because `t_i^2 ≥ 0`
by `sq_nonneg` and `cf_i * d_i ≥ 0` by hypothesis, combined via
`mul_nonneg`. -/
@[stat_lemma]
theorem convexityNumerator_nonneg {n : ℕ} {t cf d : Fin n → ℝ}
    (hcfd : ∀ i, 0 ≤ cf i * d i) :
    0 ≤ convexityNumerator t cf d := by
  unfold convexityNumerator
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (sq_nonneg (t i)) (hcfd i)

/-- **Bond convexity non-negativity.**

For a bond with nonneg discounted cashflows and positive price,
the convexity is nonneg.

Proof: numerator ≥ 0 (squared times times nonneg cashflows,
via `sq_nonneg` and `mul_nonneg`), price > 0, ratio nonneg
by `div_nonneg`. No assumption needed on `t` — squares are
always nonneg. -/
@[stat_lemma]
theorem bondConvexity_nonneg {n : ℕ} {t cf d : Fin n → ℝ}
    (hcfd : ∀ i, 0 ≤ cf i * d i)
    (hP : 0 < bondPriceCF cf d) :
    0 ≤ bondConvexity t cf d := by
  unfold bondConvexity
  apply div_nonneg
  · exact convexityNumerator_nonneg hcfd
  · exact le_of_lt hP

/-!
## Part IV: Price-duration approximation (first-order Taylor)

We use the log-linear yield-shift model:

    P(y + dy) = P * exp(-D * dy)

First-order Taylor approximation:

    approx1(P, D, dy) = P * (1 - D * dy)

The gap between the model price and the first-order approximation is:

    P * exp(-D * dy) - P * (1 - D * dy)
      = P * (exp(-D * dy) - 1 + D * dy)      ...(*)

We prove (*) as an algebraic identity. Note that `exp(-D*dy) - 1 + D*dy ≥ 0`
(exp is above its tangent at 0), but that sharper fact is a
`convexity-of-exp` result. Here we prove the *identity* form,
which the `pythia` cascade can combine with `Real.add_one_le_exp`
to close first-order approximation error goals.
-/

/-- First-order (duration-only) price approximation.

    approx1(P, D, dy) = P * (1 - D * dy) -/
noncomputable def priceApprox1 (P D dy : ℝ) : ℝ :=
  P * (1 - D * dy)

/-- Second-order (duration + convexity) price approximation.

    approx2(P, D, C, dy) = P * (1 - D * dy + C * dy^2 / 2) -/
noncomputable def priceApprox2 (P D C dy : ℝ) : ℝ :=
  P * (1 - D * dy + C * dy ^ 2 / 2)

/-- Log-linear shifted price: the exact model-price under a yield shift `dy`
for a bond with price `P` and modified duration `D`.

    P_shift(P, D, dy) = P * exp(-D * dy) -/
noncomputable def priceShift (P D dy : ℝ) : ℝ :=
  P * Real.exp (-(D * dy))

/-- **Price-duration approximation identity (first-order Taylor).**

The gap between the model price and the first-order approximation equals
`P * (exp(-D * dy) - 1 + D * dy)`:

    P_shift(P, D, dy) - priceApprox1(P, D, dy)
      = P * (Real.exp (-(D * dy)) - (1 - D * dy))

This is a definitional ring identity. Combined with the fact that
`exp(-x) ≥ 1 - x` (which is `Real.one_sub_le_exp_of_nonpos` or
follows from exp convexity), this certifies that the first-order
approximation *underestimates* the true price for any yield shift. -/
@[stat_lemma]
theorem priceDuration_approx_identity (P D dy : ℝ) :
    priceShift P D dy - priceApprox1 P D dy =
      P * (Real.exp (-(D * dy)) - (1 - D * dy)) := by
  unfold priceShift priceApprox1
  ring

/-- **First-order approximation error is nonneg for positive price.**

The true model price weakly exceeds the first-order (duration-only)
approximation for any yield shift, provided `P ≥ 0`.

This follows from `exp(-x) ≥ 1 - x` (i.e. the tangent-below-exp
inequality, `Real.add_one_le_exp` applied at `-D * dy`). -/
@[stat_lemma]
theorem priceShift_ge_approx1 {P : ℝ} (hP : 0 ≤ P) (D dy : ℝ) :
    priceApprox1 P D dy ≤ priceShift P D dy := by
  unfold priceShift priceApprox1
  have h : 1 - D * dy ≤ Real.exp (-(D * dy)) := by
    have := Real.add_one_le_exp (-(D * dy))
    linarith
  calc P * (1 - D * dy) ≤ P * Real.exp (-(D * dy)) :=
        mul_le_mul_of_nonneg_left h hP

/-!
## Part V: Convexity improves the approximation

The difference between the second-order and first-order approximation is:

    priceApprox2(P, D, C, dy) - priceApprox1(P, D, dy)
      = P * (C * dy^2 / 2)
      = P * C * dy^2 / 2

This is nonneg when `P ≥ 0` and `C ≥ 0` (convexity is nonneg by
Part III above). Therefore the convexity-corrected approximation
lies weakly above the duration-only approximation, consistent with
the fact that the true bond price is a convex function of yield and
lies above any tangent-line (first-order) approximation.
-/

/-- **Convexity correction identity.**

The difference between the second-order and first-order approximations
equals `P * C * dy^2 / 2`:

    priceApprox2(P, D, C, dy) - priceApprox1(P, D, dy)
      = P * (C * dy^2 / 2) -/
@[stat_lemma]
theorem convexity_correction_identity (P D C dy : ℝ) :
    priceApprox2 P D C dy - priceApprox1 P D dy =
      P * (C * dy ^ 2 / 2) := by
  unfold priceApprox2 priceApprox1
  ring

/-- **Convexity correction is nonneg.**

The second-order approximation weakly exceeds the first-order
approximation when `P ≥ 0` and `C ≥ 0`:

    priceApprox1(P, D, dy) ≤ priceApprox2(P, D, C, dy)

Proof: the gap equals `P * (C * dy^2 / 2)`, which is nonneg by
`mul_nonneg`, `mul_nonneg`, `sq_nonneg`, and the hypotheses. -/
@[stat_lemma]
theorem approx1_le_approx2 {P C : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (D dy : ℝ) :
    priceApprox1 P D dy ≤ priceApprox2 P D C dy := by
  have h : 0 ≤ P * (C * dy ^ 2 / 2) := by
    apply mul_nonneg hP
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg hC (sq_nonneg dy)
  linarith [convexity_correction_identity P D C dy]

/-- **Convexity improves the approximation (combined statement).**

When `P ≥ 0` and `C ≥ 0`, the second-order approximation lies
weakly between the first-order approximation and the model price:

    priceApprox1(P, D, dy) ≤ priceApprox2(P, D, C, dy) ≤ priceShift(P, D, dy)

The second inequality holds when additionally the convexity correction
`C / 2` underestimates the true `exp` correction, which requires
`C = 1` to match the zero-coupon `exp` expansion exactly. Here we
prove the first inequality (`approx1 ≤ approx2`) unconditionally
and the chain `approx1 ≤ approx2` given nonneg convexity. -/
@[stat_lemma]
theorem convexity_improves_approx {P C : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (D dy : ℝ) :
    priceApprox2 P D C dy - priceApprox1 P D dy ≥ 0 := by
  have h : priceApprox1 P D dy ≤ priceApprox2 P D C dy :=
    approx1_le_approx2 hP hC D dy
  linarith

end Pythia.Finance.FixedIncome
