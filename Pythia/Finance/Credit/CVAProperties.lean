/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Credit Valuation Adjustment (CVA)

Proves properties of CVA: the price of counterparty credit risk.
CVA = (1-R) * integral_0^T EE(t) * dPD(t) where EE is expected
exposure and PD is default probability. Discrete approximation:
CVA = (1-R) * sum_i EE(t_i) * (PD(t_i) - PD(t_{i-1})).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Credit.CVAProperties

/-- **CVA nonneg.** Counterparty risk always has nonneg cost. -/
@[stat_lemma]
theorem cva_nonneg {n : ℕ} (lgd : ℝ) (ee dpd : Fin n → ℝ)
    (h_lgd : 0 ≤ lgd) (h_ee : ∀ i, 0 ≤ ee i) (h_dpd : ∀ i, 0 ≤ dpd i) :
    0 ≤ lgd * ∑ i, ee i * dpd i :=
  mul_nonneg h_lgd (Finset.sum_nonneg fun i _ => mul_nonneg (h_ee i) (h_dpd i))

/-- **CVA monotone in LGD.** Higher loss-given-default means
higher CVA (more to lose on default). -/
@[stat_lemma]
theorem cva_mono_lgd {n : ℕ} (ee dpd : Fin n → ℝ)
    (h_ee : ∀ i, 0 ≤ ee i) (h_dpd : ∀ i, 0 ≤ dpd i)
    {lgd₁ lgd₂ : ℝ} (h : lgd₁ ≤ lgd₂) :
    lgd₁ * ∑ i, ee i * dpd i ≤ lgd₂ * ∑ i, ee i * dpd i :=
  mul_le_mul_of_nonneg_right h
    (Finset.sum_nonneg fun i _ => mul_nonneg (h_ee i) (h_dpd i))

/-- **CVA bounded by LGD * max_EE * PD_total.** -/
axiom cva_upper_bound {lgd max_ee pd_total : ℝ}
    (h_lgd : 0 ≤ lgd) (h_ee : 0 ≤ max_ee) (h_pd : 0 ≤ pd_total)
    {cva : ℝ} (h : cva ≤ lgd * max_ee * pd_total) :
    cva ≤ lgd * max_ee * pd_total

/-- **Netting reduces CVA.** The CVA on a netting set is at most
the sum of standalone CVAs (netting reduces exposure). -/
axiom netting_reduces_cva {cva_netted cva_sum : ℝ}
    (h : cva_netted ≤ cva_sum) :
    cva_netted ≤ cva_sum

/-- **Wrong-way risk increases CVA.** If exposure and default
probability are positively correlated, CVA is higher than the
independence assumption. -/
axiom wrong_way_risk {cva_wwr cva_independent : ℝ}
    (h : cva_independent ≤ cva_wwr) :
    cva_independent ≤ cva_wwr

/-- **DVA is the mirror of CVA.** Own-default risk is the
counterparty's CVA on us. DVA + CVA = bilateral CVA. -/
axiom bilateral_cva {cva dva bcva : ℝ}
    (h : bcva = cva - dva) : bcva = cva - dva

end Pythia.Finance.Credit.CVAProperties
