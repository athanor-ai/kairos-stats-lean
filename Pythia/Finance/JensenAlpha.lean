/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Jensen's Alpha (CAPM excess-return abnormality)

*Jensen's alpha* (Jensen 1968) is the portfolio-performance metric
that compares realised return against the CAPM-predicted return:

    α_J = r_p − (r_f + β · (r_m − r_f)).

A positive `α_J` indicates the portfolio outperformed its CAPM-
benchmark on a systematic-risk-adjusted basis — the canonical test
for active-manager skill (after-fees and after-style-controls).

## Main results

* `jensenAlpha`                 : `r_p − (r_f + β · (r_m − r_f))`
* `jensenAlpha_at_capm`         : if `r_p = r_f + β·(r_m − r_f)` then `α = 0`
* `jensenAlpha_linear_rp`       : shifting `r_p` by `Δr` shifts `α_J` by `Δr`
* `jensenAlpha_zero_beta`       : `β = 0` ⇒ `α_J = r_p − r_f`

## Why this lemma

Jensen's alpha is the canonical "active-management value-add" metric
and the foundational object behind the entire performance-attribution
literature (Brinson-Hood-Beebower, Fama-French factor models extend it).
Surfacing the algebraic Jensen closed form in Pythia gives the `pythia`
tactic cascade a clean closure target for manager-skill / abnormal-
return computations.

## References

* Jensen, M. C. "The Performance of Mutual Funds in the Period
  1945-1964." *Journal of Finance* 23(2): 389-416 (1968).
* Bodie, Z., Kane, A., and Marcus, A. J. *Investments*, 11th ed.
  McGraw-Hill (2017), Ch. 24.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Jensen's alpha: CAPM-benchmark excess return. -/
noncomputable def jensenAlpha (rp rf rm β : ℝ) : ℝ :=
  rp - (rf + β * (rm - rf))

/-- **CAPM-on-the-line specialisation.** If the portfolio return
matches its CAPM-predicted return exactly then Jensen's alpha is zero. -/
@[stat_lemma]
theorem jensenAlpha_at_capm (rf rm β : ℝ) :
    jensenAlpha (rf + β * (rm - rf)) rf rm β = 0 := by
  unfold jensenAlpha; ring

/-- **Linear in portfolio return.** Shifting `r_p` by `Δr` shifts
Jensen's alpha by `Δr`. -/
@[stat_lemma]
theorem jensenAlpha_linear_rp (rp Δr rf rm β : ℝ) :
    jensenAlpha (rp + Δr) rf rm β = jensenAlpha rp rf rm β + Δr := by
  unfold jensenAlpha; ring

/-- **Zero-beta specialisation.** A market-neutral portfolio
(`β = 0`) has Jensen's alpha equal to the simple excess return
`r_p − r_f` — no systematic-risk-correction needed. -/
@[stat_lemma]
theorem jensenAlpha_zero_beta (rp rf rm : ℝ) :
    jensenAlpha rp rf rm 0 = rp - rf := by
  unfold jensenAlpha; ring

end Pythia.Finance
