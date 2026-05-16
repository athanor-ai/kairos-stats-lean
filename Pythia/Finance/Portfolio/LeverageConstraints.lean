/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Leverage Constraints

Proves properties of leverage limits: margin requirements,
gross/net exposure bounds, and leverage ratio monotonicity.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Portfolio.LeverageConstraints

/-- **Gross leverage = sum of |weights|.** Always >= 1 for fully
invested long-only, can exceed 1 for levered portfolios. -/
@[stat_lemma]
theorem gross_leverage_nonneg {n : ℕ} (w : Fin n → ℝ) :
    0 ≤ ∑ i, |w i| :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

/-- **Gross >= |net|.** Triangle inequality on weights. -/
@[stat_lemma]
theorem gross_ge_abs_net {n : ℕ} (w : Fin n → ℝ) :
    |∑ i, w i| ≤ ∑ i, |w i| :=
  Finset.abs_sum_le_sum_abs _ _

/-- **Margin requirement.** For a position of value V with margin
rate m, required margin = m * |V|. Nonneg. -/
@[stat_lemma]
theorem margin_nonneg {m V : ℝ} (hm : 0 ≤ m) :
    0 ≤ m * |V| := mul_nonneg hm (abs_nonneg V)

/-- **Leverage ratio = gross exposure / equity.** Bounded by limit. -/
@[stat_lemma]
theorem leverage_within_limit {gross equity limit : ℝ}
    (h_eq : 0 < equity) (h : gross ≤ limit * equity) :
    gross / equity ≤ limit := by
  rwa [div_le_iff₀ h_eq]

/-- **Deleveraging reduces exposure.** Selling reduces gross. -/
@[stat_lemma]
theorem deleverage_reduces {gross_old reduction gross_new : ℝ}
    (h_red : 0 ≤ reduction) (h : gross_new = gross_old - reduction) :
    gross_new ≤ gross_old := by linarith

end Pythia.Finance.Portfolio.LeverageConstraints
