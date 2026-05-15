/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Currency Hedging: Unhedged vs Hedged Return Decomposition

For an international portfolio held in a foreign market, the *unhedged return*
in domestic currency is the compounded product of the local-currency asset
return and the currency return:

    r_unhedged = (1 + r_local) * (1 + r_fx) - 1.

Expanding gives `r_local + r_fx + r_local * r_fx`.  The *currency contribution*
is the portion of the unhedged return attributable solely to FX:

    currencyContrib = r_unhedged - r_local = r_fx + r_local * r_fx.

The hedged return eliminates FX exposure by substituting the covered-interest
differential (domestic risk-free rate minus foreign risk-free rate) for the
realized spot move, but the algebra of the unhedged decomposition is the
prerequisite for understanding what the hedge removes.

## Main results

* `unhedgedReturn`                      : `(1 + r_local) * (1 + r_fx) - 1`
* `currencyContrib`                     : `unhedgedReturn r_local r_fx - r_local`
* `unhedgedReturn_zero_fx`              : zero FX return leaves the domestic return unchanged
* `unhedgedReturn_zero_local`           : zero local return leaves the FX return unchanged
* `unhedgedReturn_comm`                 : symmetry in `r_local` and `r_fx`
* `currencyContrib_decompose`           : `currencyContrib = r_fx + r_local * r_fx`
* `currencyContrib_zero_fx`             : no FX move implies zero currency contribution
* `currencyContrib_nonneg_of_same_sign` : non-negative currency contribution when both returns are non-negative

## Why this module

International equity and fixed-income portfolios carry both asset risk and
currency risk.  The decomposition into local and FX components is the
starting point for currency-overlay strategies, attribution analysis, and
risk budgeting.  Surfacing the algebraic kernel in Pythia gives the `pythia`
tactic cascade a clean closure target for currency-return attribution goals.

## References

* Solnik, B. and McLeavey, D. "International Investments." Pearson (2014),
  Chapter 4.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Unhedged return in domestic currency for an international portfolio.
    `unhedgedReturn r_local r_fx = (1 + r_local) * (1 + r_fx) - 1`.

Here `r_local` is the asset return in the foreign local currency and `r_fx`
is the return on the foreign currency itself (spot appreciation against the
domestic currency).  The product `(1 + r_local) * (1 + r_fx)` is the gross
domestic-currency return; subtracting one gives the net rate of return. -/
def unhedgedReturn (r_local r_fx : ℝ) : ℝ :=
  (1 + r_local) * (1 + r_fx) - 1

/-- Currency contribution to the unhedged return: the portion of
    `unhedgedReturn r_local r_fx` that is not explained by the local return.

    `currencyContrib r_local r_fx = unhedgedReturn r_local r_fx - r_local`.

This equals `r_fx + r_local * r_fx` (see `currencyContrib_decompose`), which
shows that the FX contribution includes a cross term `r_local * r_fx`
reflecting the interaction between asset appreciation and currency appreciation. -/
def currencyContrib (r_local r_fx : ℝ) : ℝ :=
  unhedgedReturn r_local r_fx - r_local

/-- **Zero FX return.** When the foreign currency does not move against the
domestic currency (`r_fx = 0`), the unhedged return equals the local return. -/
@[stat_lemma]
theorem unhedgedReturn_zero_fx (r_local : ℝ) :
    unhedgedReturn r_local 0 = r_local := by
  unfold unhedgedReturn; ring

/-- **Zero local return.** When the underlying asset does not move in its
local currency (`r_local = 0`), the unhedged return equals the currency
return `r_fx`. -/
@[stat_lemma]
theorem unhedgedReturn_zero_local (r_fx : ℝ) :
    unhedgedReturn 0 r_fx = r_fx := by
  unfold unhedgedReturn; ring

/-- **Symmetry.** The unhedged return is symmetric in `r_local` and `r_fx`.
This reflects the algebraic fact that the compounded gross return
`(1 + a)(1 + b)` is commutative. -/
@[stat_lemma]
theorem unhedgedReturn_comm (r_local r_fx : ℝ) :
    unhedgedReturn r_local r_fx = unhedgedReturn r_fx r_local := by
  unfold unhedgedReturn; ring

/-- **Currency contribution decomposition.** The currency contribution
decomposes as the sum of the direct FX return and a cross term:

    currencyContrib r_local r_fx = r_fx + r_local * r_fx.

The cross term `r_local * r_fx` arises because currency appreciation also
scales up the already-appreciated local-currency asset value. -/
@[stat_lemma]
theorem currencyContrib_decompose (r_local r_fx : ℝ) :
    currencyContrib r_local r_fx = r_fx + r_local * r_fx := by
  unfold currencyContrib unhedgedReturn; ring

/-- **Zero FX, zero contribution.** When there is no currency move, the
currency contribution to the unhedged return is zero. -/
@[stat_lemma]
theorem currencyContrib_zero_fx (r_local : ℝ) :
    currencyContrib r_local 0 = 0 := by
  unfold currencyContrib unhedgedReturn; ring

/-- **Non-negativity for same-sign returns.** When both the local asset
return and the FX return are non-negative, the currency contribution is
non-negative:

    0 ≤ r_local → 0 ≤ r_fx → 0 ≤ currencyContrib r_local r_fx.

This follows from `currencyContrib_decompose`: both `r_fx` and `r_local * r_fx`
are non-negative under the hypotheses. -/
@[stat_lemma]
theorem currencyContrib_nonneg_of_same_sign {r_local r_fx : ℝ}
    (hl : 0 ≤ r_local) (hf : 0 ≤ r_fx) :
    0 ≤ currencyContrib r_local r_fx := by
  rw [currencyContrib_decompose]
  exact add_nonneg hf (mul_nonneg hl hf)

end Pythia.Finance
