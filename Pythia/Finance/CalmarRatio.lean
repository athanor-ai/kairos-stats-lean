/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Calmar Ratio (algebraic form)

The Calmar ratio measures risk-adjusted return using the *maximum
drawdown* as the risk denominator, rather than volatility:

    Calmar(R, MDD) = R / MDD_abs,

where `R` is the (typically annualised) realised return and
`MDD_abs > 0` is the absolute magnitude of the maximum drawdown.
This is the practitioner-standard fund-evaluation metric when
drawdown is the binding risk constraint (e.g. CTAs, managed futures).

## Main results

* `calmarRatio`                  : `R / MDD_abs`
* `calmarRatio_pos`              : `0 < calmarRatio` when `0 < R` and `0 < MDD_abs`
* `calmarRatio_nonneg`           : `0 ≤ calmarRatio` when `0 ≤ R` and `0 < MDD_abs`
* `calmarRatio_mono_return`      : monotone in `R` for `0 < MDD_abs`
* `calmarRatio_antitone_mdd`     : antitone in `MDD_abs` for `0 ≤ R`

## Why this lemma

Drawdown-based risk-adjusted-return metrics are the practitioner
standard when path-dependent loss matters more than volatility
(managed futures, hedge funds, leveraged strategies).  Surfacing the
Calmar identities in Pythia gives the `pythia` tactic cascade a clean
closure target for path-risk reporting.

## References

* Young, T. W. "Calmar Ratio: A Smoother Tool."
  *Futures* 20(1): 40 (1991).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Calmar ratio (algebraic form): `R / MDD_abs`. -/
noncomputable def calmarRatio (R MDD_abs : ℝ) : ℝ :=
  R / MDD_abs

/-- **Positivity.** Strictly positive when both return and absolute
max drawdown are strictly positive. -/
@[stat_lemma]
theorem calmarRatio_pos {R MDD_abs : ℝ} (hR : 0 < R) (hM : 0 < MDD_abs) :
    0 < calmarRatio R MDD_abs := by
  unfold calmarRatio; exact div_pos hR hM

/-- **Non-negativity.** Non-negative when return is non-negative and
absolute max drawdown is strictly positive. -/
@[stat_lemma]
theorem calmarRatio_nonneg {R MDD_abs : ℝ} (hR : 0 ≤ R) (hM : 0 < MDD_abs) :
    0 ≤ calmarRatio R MDD_abs := by
  unfold calmarRatio; exact div_nonneg hR hM.le

/-- **Monotone in return.** For fixed positive absolute max drawdown,
the Calmar ratio is monotone non-decreasing in the realised return. -/
@[stat_lemma]
theorem calmarRatio_mono_return {MDD_abs : ℝ} (hM : 0 < MDD_abs)
    {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) :
    calmarRatio R₁ MDD_abs ≤ calmarRatio R₂ MDD_abs := by
  unfold calmarRatio; exact div_le_div_of_nonneg_right h hM.le

/-- **Antitone in absolute max drawdown.** For non-negative return
and strictly positive drawdowns, the Calmar ratio is non-increasing
in the drawdown magnitude. -/
@[stat_lemma]
theorem calmarRatio_antitone_mdd {R : ℝ} (hR : 0 ≤ R)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM : M₁ ≤ M₂) :
    calmarRatio R M₂ ≤ calmarRatio R M₁ := by
  unfold calmarRatio
  exact div_le_div_of_nonneg_left hR hM₁ hM

end Pythia.Finance
