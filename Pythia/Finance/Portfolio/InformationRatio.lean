/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Information Ratio and Sharpe Ratio Decomposition

The Information Ratio (IR) is the active-return analogue of the Sharpe
ratio, evaluated relative to a benchmark rather than a risk-free rate:

    IR(alpha, te) = alpha / te,

where `alpha = R_p - R_b` is the *active return* (portfolio return minus
benchmark return) and `te > 0` is the *tracking error* (volatility of the
active-return series).  The benchmark-relative return decomposition is:

    R_p = R_b + alpha,    alpha = IR * te.

## Main results

* `informationRatio`                  : `alpha / te`  (definition)
* `ir_eq_alpha_div_tracking_error`    : `IR alpha te = alpha / te`  (rfl)
* `ir_nonneg`                         : `0 ≤ IR alpha te` when `0 ≤ alpha` and `0 < te`
  (via `div_nonneg`)
* `ir_pos`                            : `0 < IR alpha te` when `0 < alpha` and `0 < te`
* `ir_mono_alpha`                     : `IR alpha₁ te ≤ IR alpha₂ te` when `alpha₁ ≤ alpha₂`
  and `0 < te` (via `div_le_div_of_nonneg_right`)
* `benchmark_return_decomp`           : `R_p = R_b + alpha` when `alpha = R_p - R_b`
* `active_return_eq_ir_mul_te`        : `alpha = IR alpha te * te` when `0 < te`
* `ir_tracking_error_recover_alpha`   : `IR alpha te * te = alpha` when `0 < te`
* `informationRatio_diff_eq_active`   : `IR alpha₁ te - IR alpha₂ te = (alpha₁ - alpha₂) / te`
* `informationRatio_scale_invariant`  : scale invariance under `c > 0`

## Design note

`alpha` here is the *active return* (excess over benchmark), not Jensen's
alpha (excess over CAPM prediction).  When the benchmark is the risk-free
rate the IR collapses to the Sharpe ratio; when the benchmark is the CAPM-
predicted return `alpha` equals Jensen's alpha.  Both interpretations share
the same algebra captured here.

## References

* Treynor, J. L. and Black, F. "How to Use Security Analysis to Improve
  Portfolio Selection." *Journal of Business* 46(1): 66-86 (1973).
* Goodwin, T. H. "The Information Ratio."
  *Financial Analysts Journal* 54(4): 34-43 (1998).
-/
import Mathlib
import Pythia.Tactic.Pythia
import Pythia.Finance.Portfolio.SharpeRatio

namespace Pythia.Finance

/-! ### Core definition -/

/-- Information ratio: `alpha / te`, where `alpha` is the active return
(portfolio return minus benchmark return) and `te` is the tracking error. -/
noncomputable def informationRatio (alpha te : ℝ) : ℝ :=
  alpha / te

/-! ### Definitional equality -/

/-- **Definitional equality.** The information ratio is exactly `alpha / te`
by definition. This lemma makes the equation explicit so downstream goals
can name it without unfolding. -/
@[stat_lemma]
theorem ir_eq_alpha_div_tracking_error (alpha te : ℝ) :
    informationRatio alpha te = alpha / te :=
  rfl

/-! ### Sign properties -/

/-- **Non-negativity.** The information ratio is non-negative when the active
return is non-negative and the tracking error is strictly positive.  Proof
uses `div_nonneg` directly. -/
@[stat_lemma]
theorem ir_nonneg {alpha te : ℝ} (h_alpha : 0 ≤ alpha) (h_te : 0 < te) :
    0 ≤ informationRatio alpha te := by
  unfold informationRatio
  exact div_nonneg h_alpha h_te.le

/-- **Strict positivity.** The information ratio is strictly positive when
the active return is strictly positive and the tracking error is strictly
positive. -/
@[stat_lemma]
theorem ir_pos {alpha te : ℝ} (h_alpha : 0 < alpha) (h_te : 0 < te) :
    0 < informationRatio alpha te := by
  unfold informationRatio
  exact div_pos h_alpha h_te

/-! ### Monotonicity in alpha -/

/-- **Monotone in active return.** For fixed positive tracking error, the
information ratio is monotone non-decreasing in the active return `alpha`.
Proof uses `div_le_div_of_nonneg_right`. -/
@[stat_lemma]
theorem ir_mono_alpha {te : ℝ} (h_te : 0 < te)
    {alpha₁ alpha₂ : ℝ} (h : alpha₁ ≤ alpha₂) :
    informationRatio alpha₁ te ≤ informationRatio alpha₂ te := by
  unfold informationRatio
  exact div_le_div_of_nonneg_right h h_te.le

/-- **Strict monotonicity.** A strictly larger active return yields a
strictly larger information ratio for fixed positive tracking error. -/
@[stat_lemma]
theorem ir_strictMono_alpha {te : ℝ} (h_te : 0 < te)
    {alpha₁ alpha₂ : ℝ} (h : alpha₁ < alpha₂) :
    informationRatio alpha₁ te < informationRatio alpha₂ te := by
  unfold informationRatio
  exact div_lt_div_of_pos_right h h_te

/-! ### Benchmark-relative return decomposition -/

/-- **Benchmark decomposition.** The portfolio return decomposes as
benchmark return plus active return:

    R_p = R_b + alpha,

where `alpha = R_p - R_b` is the definition of active return. This is the
*benchmark-relative return decomposition* stated as a rewrite lemma. -/
@[stat_lemma]
theorem benchmark_return_decomp (R_p R_b : ℝ) :
    R_p = R_b + (R_p - R_b) := by ring

/-- **Active return recovery from IR and tracking error.** When the tracking
error is strictly positive, the active return can be recovered from the
information ratio:

    IR(alpha, te) * te = alpha.

This is the identity that links the ratio back to the numerator. -/
@[stat_lemma]
theorem ir_tracking_error_recover_alpha {alpha te : ℝ} (h_te : 0 < te) :
    informationRatio alpha te * te = alpha := by
  unfold informationRatio
  exact div_mul_cancel₀ alpha h_te.ne'

/-- **Active return equals IR times tracking error.** Symmetric form of
`ir_tracking_error_recover_alpha`: `alpha = IR * te`. -/
@[stat_lemma]
theorem active_return_eq_ir_mul_te {alpha te : ℝ} (h_te : 0 < te) :
    alpha = informationRatio alpha te * te := by
  rw [ir_tracking_error_recover_alpha h_te]

/-- **Portfolio return in IR-tracking-error units.** Putting together the
decomposition and the recovery identity: for any active return `alpha = R_p - R_b`
the portfolio return satisfies

    R_p = R_b + IR(R_p - R_b, te) * te.

This is the full benchmark-relative return decomposition in IR units. -/
@[stat_lemma]
theorem portfolio_return_ir_decomp (R_p R_b te : ℝ) (h_te : 0 < te) :
    R_p = R_b + informationRatio (R_p - R_b) te * te := by
  rw [ir_tracking_error_recover_alpha h_te]
  ring

/-! ### Structural identity and scale invariance -/

/-- **Difference identity.** The difference of two information ratios at
the same tracking error equals the difference of the active returns divided
by the tracking error:

    IR alpha₁ te - IR alpha₂ te = (alpha₁ - alpha₂) / te.

This is the 1/te-Lipschitz property in the active-return argument. -/
@[stat_lemma]
theorem informationRatio_diff_eq_active (alpha₁ alpha₂ te : ℝ) :
    informationRatio alpha₁ te - informationRatio alpha₂ te
      = (alpha₁ - alpha₂) / te := by
  unfold informationRatio
  rw [← sub_div]

/-- **Scale invariance.** Rescaling both the active return and the tracking
error by a strictly positive constant `c` leaves the information ratio
unchanged:

    IR (c * alpha) (c * te) = IR alpha te.

Scale invariance implies the IR measures *risk-adjusted* performance in
units that are invariant to the choice of return frequency (daily vs annual). -/
@[stat_lemma]
theorem informationRatio_scale_invariant {c : ℝ} (hc : 0 < c)
    (alpha te : ℝ) :
    informationRatio (c * alpha) (c * te) = informationRatio alpha te := by
  unfold informationRatio
  exact mul_div_mul_left alpha te hc.ne'

/-! ### Sharpe ratio collapse -/

/-- **Collapse to Sharpe ratio.** When the benchmark is the risk-free rate
`rf` and the tracking error is the portfolio volatility `sigma`, the
information ratio equals the Sharpe ratio:

    IR (R_p - rf) sigma = sharpeRatio R_p rf sigma.

This makes explicit that the Sharpe ratio is the special case of the
information ratio with a cash benchmark. -/
@[stat_lemma]
theorem ir_eq_sharpe_at_cash_benchmark (R_p rf sigma : ℝ) :
    informationRatio (R_p - rf) sigma = sharpeRatio R_p rf sigma := by
  unfold informationRatio sharpeRatio
  rfl

end Pythia.Finance
