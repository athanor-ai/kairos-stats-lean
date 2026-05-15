/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Square-Root Market Impact (Kyle-Obizhaeva)

The *square-root market impact model* (Kyle and Obizhaeva 2016)
describes the price impact of trading a quantity `Q` in a market with
daily volume `V` and daily volatility `sigma`:

    impact(sigma, Q, V) = sigma * sqrt(Q / V).

For algebraic tractability this module works with the **squared
impact**, which eliminates the square root:

    impactSq(sigma_sq, Q, V) = sigma_sq * Q / V,

where `sigma_sq = sigma^2` is the daily variance.  All five algebraic
properties of the squared impact follow from Mathlib's division-
ordering API with no real-analysis machinery.

## Main results

* `impactSq`                    : `sigma_sq * Q / V`
* `impactSq_pos`                : strictly positive when all inputs are strictly positive
* `impactSq_zero_at_zero_quantity` : zero at zero order size
* `impactSq_mono_quantity`      : monotone non-decreasing in `Q` for `sigma_sq ≥ 0`, `V > 0`
* `impactSq_antitone_volume`    : antitone in `V` for `sigma_sq ≥ 0`, `Q ≥ 0`, `0 < V1 ≤ V2`
* `impactSq_scale`              : linear scaling in `sigma_sq`
* `impactSq_linear_quantity`    : linear in quantity at the squared level

## Why this module

Market impact is the dominant execution cost for quantitative
practitioners operating at scale.  The square-root model underpins
virtually every industrial-grade execution-cost model (Almgren-Chriss,
Barra, Axioma).  Surfacing the algebraic kernel in Pythia gives the
`pythia` tactic cascade a clean closure target for impact-cost
inequality goals.

## References

* Kyle, A. S. and Obizhaeva, A. "Market Microstructure Invariance."
  *Review of Financial Studies* 29(8): 2267-2312 (2016).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Squared market impact under the Kyle-Obizhaeva square-root model:
    `impactSq(sigma_sq, Q, V) = sigma_sq * Q / V`.

Here `sigma_sq` is the daily variance, `Q` is the order size, and `V`
is the daily volume.  The squared-impact form avoids the real-sqrt and
admits a clean division-arithmetic treatment. -/
noncomputable def impactSq (sigma_sq Q V : ℝ) : ℝ :=
  sigma_sq * Q / V

/-- **Positivity.** When daily variance, order size, and daily volume
are all strictly positive, the squared market impact is strictly
positive. -/
@[stat_lemma]
theorem impactSq_pos {sigma_sq Q V : ℝ}
    (hσ : 0 < sigma_sq) (hQ : 0 < Q) (hV : 0 < V) :
    0 < impactSq sigma_sq Q V := by
  unfold impactSq
  exact div_pos (mul_pos hσ hQ) hV

/-- **Zero at zero order size.** Trading zero shares incurs zero
squared impact, regardless of volatility or volume. -/
@[stat_lemma]
theorem impactSq_zero_at_zero_quantity (sigma_sq V : ℝ) :
    impactSq sigma_sq 0 V = 0 := by
  unfold impactSq; ring

/-- **Monotone in order size.** For non-negative variance and strictly
positive volume, the squared impact is monotone non-decreasing in the
order quantity: larger orders move the price more. -/
@[stat_lemma]
theorem impactSq_mono_quantity {sigma_sq V : ℝ}
    (hσ : 0 ≤ sigma_sq) (hV : 0 < V)
    {Q1 Q2 : ℝ} (hQ : Q1 ≤ Q2) :
    impactSq sigma_sq Q1 V ≤ impactSq sigma_sq Q2 V := by
  unfold impactSq
  apply div_le_div_of_nonneg_right _ hV.le
  exact mul_le_mul_of_nonneg_left hQ hσ

/-- **Antitone in volume.** For non-negative variance, non-negative
order size, and a volume increase from `V1` to `V2`, the squared
impact is non-increasing in volume: deeper markets absorb orders more
cheaply. -/
@[stat_lemma]
theorem impactSq_antitone_volume {sigma_sq Q : ℝ}
    (hσ : 0 ≤ sigma_sq) (hQ : 0 ≤ Q)
    {V1 V2 : ℝ} (hV1 : 0 < V1) (hV : V1 ≤ V2) :
    impactSq sigma_sq Q V2 ≤ impactSq sigma_sq Q V1 := by
  unfold impactSq
  exact div_le_div_of_nonneg_left (mul_nonneg hσ hQ) hV1 hV

/-- **Linear scaling in variance.** Scaling daily variance by `c`
scales the squared impact by the same factor `c`. This reflects that
impact is proportional to volatility (at the squared level, to
variance). -/
@[stat_lemma]
theorem impactSq_scale (c sigma_sq Q V : ℝ) :
    impactSq (c * sigma_sq) Q V = c * impactSq sigma_sq Q V := by
  unfold impactSq; ring

/-- **Linearity in quantity.** The squared impact is additive in the
order size: splitting an order `Q1 + Q2` into two legs and summing
their individual squared impacts recovers the total squared impact.
This is the algebraic content of linear price impact at the squared
level. -/
@[stat_lemma]
theorem impactSq_linear_quantity (sigma_sq Q1 Q2 V : ℝ) :
    impactSq sigma_sq (Q1 + Q2) V =
    impactSq sigma_sq Q1 V + impactSq sigma_sq Q2 V := by
  unfold impactSq
  rw [mul_add, add_div]

end Pythia.Finance
