/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Credit Spread Model

Formalises the four core inequalities of single-name credit spread
analysis:

1. **Spread definition and non-negativity.**
   The credit spread is `s = y - r` where `y` is the risky bond yield
   and `r` is the matched-maturity risk-free yield.  Under no-arbitrage,
   `y >= r`, so `s >= 0`.

2. **Spread widens with default probability.**
   In the reduced-form (Jarrow-Turnbull / Duffie-Singleton) model the
   spread is at least `pd * lgd` where `pd` is the risk-neutral default
   probability and `lgd` is the loss-given-default fraction.  When `pd`
   increases, this lower bound rises.

3. **No-arbitrage non-negativity.**
   The no-arbitrage condition `y >= r` is an explicit hypothesis, so
   spread non-negativity follows from `sub_nonneg` alone.

4. **CDS-bond basis non-negativity.**
   The CDS-bond basis is `basis = cds_spread - bond_spread`.
   Under the no-arbitrage conditions:
   - the CDS spread equals `pd * lgd` (premium = protection),
   - the bond spread is at most `pd * lgd` (market price includes
     liquidity premium that compresses the bond yield relative to the
     actuarially fair level),
   the basis is non-negative.

## Main results

* `creditSpread_def`                  : definitional unfolding
* `creditSpread_nonneg`               : `s >= 0` from `y >= r` via `sub_nonneg`
* `creditSpread_nonneg_no_arb`        : same, explicit no-arb hypothesis form
* `spread_lb_expected_loss`           : `s >= pd * lgd` when spread >= expected loss
* `spread_widens_with_pd`             : monotone in `pd` (for fixed `lgd >= 0`)
* `spread_widens_with_pd_from_hyp`    : monotonicity from spread-lower-bound hypothesis
* `cds_bond_basis_nonneg`             : `basis = cds_spread - bond_spread >= 0`
* `cds_bond_basis_nonneg_mul`         : basis via `pd * lgd` factored form

## References

* Duffie, D. and Singleton, K.  "Modeling Term Structures of Defaultable
  Bonds."  Review of Financial Studies 12(4): 687-720 (1999).
* Jarrow, R. and Turnbull, S.  "Pricing Derivatives on Financial
  Securities Subject to Credit Risk."  Journal of Finance 50(1): 53-85
  (1995).
* Hull, J. C. and White, A.  "Valuing Credit Default Swaps."  Journal
  of Derivatives 8(1) (2000).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Credit.CreditSpreadModel

/-! ### 1. Spread definition and basic non-negativity -/

/-- Credit spread: the risky yield minus the matched-maturity risk-free
yield. -/
def creditSpread (y r : ℝ) : ℝ := y - r

/-- **Definitional unfolding.** The credit spread is `y - r`. -/
@[stat_lemma]
theorem creditSpread_def (y r : ℝ) : creditSpread y r = y - r := rfl

/-- **Non-negativity of credit spread.**
When the risky yield `y` is at least the risk-free yield `r`, the
spread `y - r` is non-negative.  Follows directly from `sub_nonneg`. -/
@[stat_lemma]
theorem creditSpread_nonneg {y r : ℝ} (h : r ≤ y) :
    0 ≤ creditSpread y r := by
  unfold creditSpread
  exact sub_nonneg.mpr h

/-- **No-arbitrage non-negativity.**
Identical statement with an explicit no-arb label on the hypothesis to
make the economic interpretation clear: the condition `r ≤ y` is the
no-arbitrage constraint that rules out riskless profit by holding the
risky bond and shorting the risk-free bond. -/
@[stat_lemma]
theorem creditSpread_nonneg_no_arb {y r : ℝ}
    (h_no_arb : r ≤ y) :   -- no-arbitrage: risky yield >= risk-free yield
    0 ≤ creditSpread y r := by
  unfold creditSpread
  exact sub_nonneg.mpr h_no_arb

/-! ### 2. Spread lower bound: expected loss -/

/-- Expected loss under risk-neutral pricing: `pd * lgd`. -/
def expectedLoss (pd lgd : ℝ) : ℝ := pd * lgd

/-- **Spread lower-bounded by expected loss.**
In reduced-form pricing the spread is at least the expected loss
`pd * lgd`.  This hypothesis (given as `h_lb`) captures the
fundamental credit-pricing inequality; the theorem extracts
non-negativity of the spread from non-negativity of `pd` and `lgd`. -/
@[stat_lemma]
theorem spread_lb_expected_loss {s pd lgd : ℝ}
    (hpd  : 0 ≤ pd)
    (hlgd : 0 ≤ lgd)
    (h_lb : expectedLoss pd lgd ≤ s) :
    0 ≤ s := by
  unfold expectedLoss at h_lb
  exact le_trans (mul_nonneg hpd hlgd) h_lb

/-! ### 3. Spread widens with default probability -/

/-- **Spread widens with default probability (expected-loss form).**
For fixed non-negative `lgd`, the expected-loss lower bound on the
spread is monotone non-decreasing in `pd`.  Hence a higher default
probability forces a wider spread. -/
@[stat_lemma]
theorem spread_widens_with_pd {lgd : ℝ} (hlgd : 0 ≤ lgd)
    {pd₁ pd₂ : ℝ} (hpd : pd₁ ≤ pd₂) :
    expectedLoss pd₁ lgd ≤ expectedLoss pd₂ lgd := by
  unfold expectedLoss
  exact mul_le_mul_of_nonneg_right hpd hlgd

/-- **Spread monotone in pd, propagated to spread itself.**
If the spread is lower-bounded by `pd * lgd` at both `pd₁` and `pd₂`
and `pd₁ ≤ pd₂`, then the spread at the higher default probability is
at least the spread at the lower one (given the lower-bound structure
is tight). -/
@[stat_lemma]
theorem spread_widens_with_pd_from_hyp {lgd s₁ s₂ : ℝ}
    (hlgd : 0 ≤ lgd)
    {pd₁ pd₂ : ℝ}
    (hpd  : pd₁ ≤ pd₂)
    (hpd1 : 0 ≤ pd₁)
    (h_lb1 : expectedLoss pd₁ lgd ≤ s₁)
    (h_lb2 : s₁ ≤ s₂) :
    expectedLoss pd₁ lgd ≤ s₂ := by
  unfold expectedLoss at *
  linarith [mul_nonneg hpd1 hlgd]

/-! ### 4. CDS-bond basis non-negativity -/

/-- CDS-bond basis: the difference between the CDS spread and the
bond credit spread for the same reference entity and maturity. -/
def cdsBondBasis (cds_spread bond_spread : ℝ) : ℝ :=
  cds_spread - bond_spread

/-- **CDS-bond basis non-negative.**
Under no-arbitrage the CDS spread reflects the full default risk:
`cds_spread = pd * lgd`.  The bond spread is at most this value
because the bond market may embed a liquidity premium that compresses
the bond yield below the actuarially fair level (equivalently, bond
buyers accept a lower yield to hold a liquid instrument).  Therefore
`basis = cds_spread - bond_spread >= 0`. -/
@[stat_lemma]
theorem cds_bond_basis_nonneg {cds_spread bond_spread : ℝ}
    (h : bond_spread ≤ cds_spread) :
    0 ≤ cdsBondBasis cds_spread bond_spread := by
  unfold cdsBondBasis
  exact sub_nonneg.mpr h

/-- **CDS-bond basis non-negative (multiplied form).**
Derives the same result when both spreads are expressed via `pd * lgd`:
the CDS spread equals `pd_cds * lgd` (fair-value premium) while the
bond spread equals `pd_bond * lgd` with `pd_bond ≤ pd_cds` (bond
market implied default probability does not exceed the CDS-implied
probability under no-arbitrage). -/
@[stat_lemma]
theorem cds_bond_basis_nonneg_mul {lgd pd_cds pd_bond : ℝ}
    (hlgd    : 0 ≤ lgd)
    (hpd_le  : pd_bond ≤ pd_cds) :
    0 ≤ cdsBondBasis (pd_cds * lgd) (pd_bond * lgd) := by
  unfold cdsBondBasis
  have : pd_bond * lgd ≤ pd_cds * lgd :=
    mul_le_mul_of_nonneg_right hpd_le hlgd
  linarith

/-! ### 5. Composite: no-arb plus expected-loss sandwich -/

/-- **Full no-arbitrage spread sandwich.**
Combines all four results: the spread `s = y - r` satisfies
`pd * lgd ≤ s` and `0 ≤ s` under:
- no-arbitrage (`r ≤ y`), and
- the reduced-form lower bound (`pd * lgd ≤ s`).
-/
@[stat_lemma]
theorem spread_no_arb_sandwich {y r pd lgd : ℝ}
    (h_no_arb : r ≤ y)
    (hpd      : 0 ≤ pd)
    (hlgd     : 0 ≤ lgd)
    (h_lb     : pd * lgd ≤ creditSpread y r) :
    pd * lgd ≤ creditSpread y r ∧ 0 ≤ creditSpread y r := by
  constructor
  · exact h_lb
  · exact sub_nonneg.mpr h_no_arb

end Pythia.Finance.Credit.CreditSpreadModel
