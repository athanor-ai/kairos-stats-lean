/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Modigliani-Miller Proposition I (capital-structure invariance)

The *Modigliani-Miller theorem* (1958, with the 1963 tax-correction)
states that under frictionless markets the value of a firm is
independent of its capital structure, and under a corporate-tax wedge
`τ_c` the levered firm value adds a tax-shield term:

    V_L = V_U                (no-tax baseline)
    V_L = V_U + τ_c · D      (with corporate-tax shield)

This file gives the algebraic kernel.  The closed form is
intentionally minimal — the *economic content* (no-arbitrage between
levered/unlevered claims) is captured at the cashflow level via
`Pythia.Finance.NetPresentValue`; this module surfaces the M-M
identity as a `pythia`-closable algebraic shape.

## Main results

* `leveredValue`                : `V_U + τ_c · D`
* `leveredValue_zero_tax`       : `τ_c = 0` ⇒ `V_L = V_U` (M-M I, 1958)
* `leveredValue_zero_debt`      : `D = 0` ⇒ `V_L = V_U` (no leverage, no shield)
* `leveredValue_linear_debt`    : shifting `D` by `ΔD` shifts `V_L` by `τ_c·ΔD`

## Why this lemma

The M-M propositions are the foundational result of modern corporate
finance — the entire WACC / cost-of-capital framework is a corollary.
Surfacing the M-M closed form in Pythia gives the `pythia` tactic
cascade a clean closure target for capital-structure / leverage-
adjustment computations.

## References

* Modigliani, F. and Miller, M. H.
  "The Cost of Capital, Corporation Finance and the Theory of
   Investment."
  *American Economic Review* 48(3): 261-297 (1958).
* Modigliani, F. and Miller, M. H.
  "Corporate Income Taxes and the Cost of Capital: A Correction."
  *American Economic Review* 53(3): 433-443 (1963).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Levered firm value under a corporate-tax shield:
    `V_L = V_U + τ_c · D`. -/
noncomputable def leveredValue (Vu τc D : ℝ) : ℝ :=
  Vu + τc * D

/-- **Zero-tax M-M I (1958).** Without a corporate-tax wedge the
levered firm value equals the unlevered firm value — capital
structure is irrelevant. -/
@[stat_lemma]
theorem leveredValue_zero_tax (Vu D : ℝ) :
    leveredValue Vu 0 D = Vu := by
  unfold leveredValue; ring

/-- **Zero-debt specialisation.** An all-equity firm has no
tax shield: `V_L = V_U`. -/
@[stat_lemma]
theorem leveredValue_zero_debt (Vu τc : ℝ) :
    leveredValue Vu τc 0 = Vu := by
  unfold leveredValue; ring

/-- **Linear in debt.** Adding `ΔD` of debt adds `τ_c · ΔD` to
firm value (the marginal tax-shield from each unit of additional
debt). -/
@[stat_lemma]
theorem leveredValue_linear_debt (Vu τc D ΔD : ℝ) :
    leveredValue Vu τc (D + ΔD) = leveredValue Vu τc D + τc * ΔD := by
  unfold leveredValue; ring

end Pythia.Finance
