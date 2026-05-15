/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Treynor Ratio (systematic-risk-adjusted excess return)

The *Treynor ratio* (Treynor 1965) is the risk-adjusted-return ratio
that divides excess return by the asset's systematic-risk-exposure
measure `β` (CAPM beta), rather than total volatility `σ` (the
Sharpe-ratio denominator):

    T(r_p, r_f, β) = (r_p - r_f) / β.

Unlike Sharpe, Treynor uses only the *systematic* (market-correlated)
component of risk — appropriate for a well-diversified portfolio
where idiosyncratic risk has been (asymptotically) diversified away.

## Main results

* `treynorRatio`             : (r_p - r_f) / β
* `treynorRatio_zero_excess` : at `r_p = r_f` the ratio is zero
* `treynorRatio_linear_rp`   : linear shift of `r_p` translates `T` by `Δr/β`
* `treynorRatio_translation` : equal shift on both `r_p` and `r_f` cancels

## Why this lemma

Treynor is the canonical "diversified-portfolio" risk-adjusted-return
score (vs Sharpe's "any-portfolio" total-variance score) and the input
to mutual-fund / pension-fund benchmark comparison.  Surfacing the
algebraic Treynor closed form in Pythia gives the `pythia` tactic
cascade a clean closure target for fund-performance comparisons.

## References

* Treynor, J. L. "How to Rate Management of Investment Funds."
  *Harvard Business Review* 43(1): 63-75 (1965).
* Bodie, Z., Kane, A., and Marcus, A. J. *Investments*, 11th ed.
  McGraw-Hill (2017), Ch. 24.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Treynor ratio: systematic-risk-adjusted excess return. -/
noncomputable def treynorRatio (rp rf β : ℝ) : ℝ :=
  (rp - rf) / β

/-- **Zero-excess specialisation.** When the portfolio return equals
the risk-free rate the Treynor ratio is zero. -/
@[stat_lemma]
theorem treynorRatio_zero_excess (rf β : ℝ) :
    treynorRatio rf rf β = 0 := by
  unfold treynorRatio; simp

/-- **Linear in portfolio return.** Shifting `r_p` by `Δr` shifts
the Treynor ratio by `Δr / β`. -/
@[stat_lemma]
theorem treynorRatio_linear_rp (rp Δr rf β : ℝ) :
    treynorRatio (rp + Δr) rf β
      = treynorRatio rp rf β + Δr / β := by
  unfold treynorRatio
  field_simp
  ring

/-- **Cash-rate translation invariance.** Adding the same `c` to
both the portfolio return and the risk-free rate cancels in the
numerator. -/
@[stat_lemma]
theorem treynorRatio_translation (rp rf c β : ℝ) :
    treynorRatio (rp + c) (rf + c) β = treynorRatio rp rf β := by
  unfold treynorRatio
  ring_nf

end Pythia.Finance
