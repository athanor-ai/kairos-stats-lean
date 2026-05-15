/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gordon Growth Model (constant-dividend-growth equity valuation)

The *Gordon growth model* (Gordon-Shapiro 1956) values a perpetual
dividend stream growing at constant rate `g < r` as

    P_0 = D_1 / (r − g),

where `D_1` is next-period's dividend, `r` is the required return on
equity, and `g` is the constant dividend growth rate.

This is the foundational equity-valuation closed form behind DCF
terminal-value calculations (where post-explicit-period cashflows
are capitalised at a perpetual-growth rate).  When `g = 0` it
reduces to the simple perpetuity formula `P = D / r`
(see `Pythia.Finance.Perpetuity`).

## Main results

* `gordonGrowthPrice`             : `D₁ / (r − g)`
* `gordonGrowthPrice_zero_growth` : at `g = 0` ⇒ `P = D₁ / r` (perpetuity)
* `gordonGrowthPrice_linear_D`    : linear in `D₁`
* `gordonGrowthPrice_scale_D`     : scaling `D₁` by `α` scales price by `α`

## Why this lemma

Gordon-Shapiro is the canonical equity-valuation closed form for
mature dividend-paying firms and the *standard* DCF terminal-value
formula across investment banking, equity research, and corporate-
finance practice.  Surfacing the algebraic Gordon closed form in
Pythia gives the `pythia` tactic cascade a clean closure target for
constant-growth equity-valuation analytics.

## References

* Gordon, M. J. and Shapiro, E. "Capital Equipment Analysis: The
  Required Rate of Profit." *Management Science* 3(1): 102-110 (1956).
* Brealey, R., Myers, S., and Allen, F. *Principles of Corporate
  Finance*, 13th ed. McGraw-Hill (2019), Ch. 4.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Gordon growth equity price: constant-growth perpetuity. -/
noncomputable def gordonGrowthPrice (D₁ r g : ℝ) : ℝ :=
  D₁ / (r - g)

/-- **Zero-growth specialisation.** With `g = 0` Gordon reduces to
the simple perpetuity formula `P = D₁ / r`. -/
@[stat_lemma]
theorem gordonGrowthPrice_zero_growth (D₁ r : ℝ) :
    gordonGrowthPrice D₁ r 0 = D₁ / r := by
  unfold gordonGrowthPrice; simp

/-- **Linear in next-period dividend.** Shifting `D₁` by `ΔD`
shifts the price by `ΔD / (r − g)`. -/
@[stat_lemma]
theorem gordonGrowthPrice_linear_D (D₁ ΔD r g : ℝ) :
    gordonGrowthPrice (D₁ + ΔD) r g
      = gordonGrowthPrice D₁ r g + ΔD / (r - g) := by
  unfold gordonGrowthPrice
  ring

/-- **Scale-invariance in dividend.** Scaling `D₁` by `α` scales
the price by `α`. -/
@[stat_lemma]
theorem gordonGrowthPrice_scale_D (D₁ α r g : ℝ) :
    gordonGrowthPrice (α * D₁) r g = α * gordonGrowthPrice D₁ r g := by
  unfold gordonGrowthPrice
  ring

end Pythia.Finance
