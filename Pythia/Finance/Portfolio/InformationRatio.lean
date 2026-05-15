/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Information Ratio (algebraic form)

The Information ratio is the active-return Sharpe ratio relative to
a benchmark:

    IR(R_p, R_b, σ_a) = (R_p - R_b) / σ_a,

where `R_p` is the portfolio return, `R_b` is the benchmark return,
and `σ_a` is the tracking error (volatility of active return
`R_p - R_b`).  Structurally identical to the Sharpe ratio with
`R_b` in place of the risk-free rate; semantically distinguishes
*alpha generation versus benchmark* from *Sharpe under cash-rate*.

## Main results

* `informationRatio`                  : `(R_p - R_b) / σ_a`
* `informationRatio_pos`              :
  `0 < IR` when `R_b < R_p` and `0 < σ_a`
* `informationRatio_diff_eq_active`   :
  `IR(R_p) - IR(R_q) = (R_p - R_q) / σ_a`  (structural identity)
* `informationRatio_scale_invariant`  :
  `IR (α·R_p) (α·R_b) (α·σ_a) = IR R_p R_b σ_a` for `α > 0`

## Why this lemma

Active-management evaluation uses Information ratio to separate
alpha generation from passive market exposure.  The structural
identity `informationRatio_diff_eq_active` makes the ratio
1/σ_a-Lipschitz in `R_p - R_q`, parallel to
`Pythia.Finance.SharpeBridge.sharpe_diff_eq_excess_over_sigma`.
That parallel enables anytime-valid Information-ratio confidence
sequences via the same `Pythia.HowardRamdasCS` infrastructure used
for Sharpe.

## References

* Treynor, J. L. and Black, F. "How to Use Security Analysis to
  Improve Portfolio Selection." *Journal of Business* 46(1): 66-86 (1973).
* Goodwin, T. H. "The Information Ratio."
  *Financial Analysts Journal* 54(4): 34-43 (1998).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Information ratio (algebraic form): `(R_p - R_b) / σ_a`. -/
noncomputable def informationRatio (R_p R_b σ_a : ℝ) : ℝ :=
  (R_p - R_b) / σ_a

/-- **Positivity.** Strictly positive when the portfolio return
exceeds the benchmark and the tracking error is strictly positive. -/
@[stat_lemma]
theorem informationRatio_pos {R_p R_b σ_a : ℝ}
    (h_excess : R_b < R_p) (hσ : 0 < σ_a) :
    0 < informationRatio R_p R_b σ_a := by
  unfold informationRatio; exact div_pos (sub_pos.mpr h_excess) hσ

/-- **Structural identity.** Difference of two information ratios at
the same benchmark and tracking error equals the active-return
difference divided by the tracking error:

    IR R_p R_b σ_a - IR R_q R_b σ_a = (R_p - R_q) / σ_a.

This is the 1/σ_a-Lipschitz property in the portfolio-return
argument; it parallels `sharpe_diff_eq_excess_over_sigma`. -/
@[stat_lemma]
theorem informationRatio_diff_eq_active (R_p R_q R_b σ_a : ℝ) :
    informationRatio R_p R_b σ_a - informationRatio R_q R_b σ_a
      = (R_p - R_q) / σ_a := by
  unfold informationRatio
  rw [← sub_div]
  congr 1
  ring

/-- **Scale invariance.** Rescaling all three arguments by a strictly
positive constant leaves the information ratio unchanged. -/
@[stat_lemma]
theorem informationRatio_scale_invariant {α : ℝ} (hα : 0 < α)
    (R_p R_b σ_a : ℝ) :
    informationRatio (α * R_p) (α * R_b) (α * σ_a)
      = informationRatio R_p R_b σ_a := by
  unfold informationRatio
  rw [← mul_sub]
  exact mul_div_mul_left (R_p - R_b) σ_a hα.ne'

end Pythia.Finance
