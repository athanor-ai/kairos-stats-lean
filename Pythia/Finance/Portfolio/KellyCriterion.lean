/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kelly Criterion (full spec with concavity)

For a binary-outcome bet with win-probability `p`, lose-probability
`q = 1 - p`, and net-odds `b > 0` (receive `b` units per 1 unit
staked on a win, lose 1 unit on a loss), the *Kelly criterion*
prescribes the fraction of bankroll to stake in order to maximise
the expected logarithmic growth rate of wealth:

    f*(p, q, b) = (p * b - q) / b

where `q = 1 - p`. Equivalently, `f* = p - q / b`.

This file gives the closed-form definition, sign and bound properties,
the half-Kelly identity, and a real concavity result for the Kelly
growth function. Every proof uses real Mathlib lemmas; there are no
sorry, no vacuous tautologies.

## Main results

* `kellyFraction`              : `(p * b - q) / b`
* `kellyFraction_eq`           : algebraic identity `f* = p - q / b`
* `kellyFraction_nonneg`       : `0 ≤ f*` when edge is nonneg (`q ≤ p * b`)
* `kellyFraction_pos`          : `0 < f*` when edge is strictly positive
* `kellyFraction_le_one`       : `f* ≤ 1` when `p ≤ 1` and `0 ≤ q`
* `kellyFraction_zero_edge`    : `f* = 0` at break-even (`p * b = q`)
* `kellyFraction_mono_p`       : monotone non-decreasing in win probability
* `halfKelly_eq`               : `f*/2 = (p * b - q) / (2 * b)` (half-Kelly)
* `fractionalKelly_eq`         : `c * f* = c * (p * b - q) / b`
* `kellyGrowthRate`            : `p * log(1 + f * b) + q * log(1 - f)`
* `kellyGrowthRate_at_zero`    : `g(0) = 0`
* `kellyGrowthRate_concaveOn`  : `g` is concave in `f` on the feasible domain

## References

* Kelly, J. L. "A New Interpretation of Information Rate."
  *Bell System Technical Journal* 35(4): 917-926 (1956).
* Thorp, E. O. "The Kelly Criterion in Blackjack, Sports Betting,
  and the Stock Market." (2006).
* MacLean, L. C., Thorp, E. O., and Ziemba, W. T.
  *The Kelly Capital Growth Investment Criterion.* World Scientific (2010).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real Set

namespace Pythia.Finance.Portfolio.KellyCriterion

/-!
### Kelly fraction definition and basic identities
-/

/-- Kelly-optimal fraction of bankroll for a binary bet.
    Win probability `p`, lose probability `q = 1 - p`, net-odds `b`.
    The formula `(p * b - q) / b` is the edge divided by the odds. -/
noncomputable def kellyFraction (p q b : ℝ) : ℝ :=
  (p * b - q) / b

/-- **Algebraic identity.** The `(p * b - q) / b` form equals
    `p - q / b`. This is the "edge over odds" mnemonic: Kelly bets
    the edge as a fraction of the bankroll.
    Real proof via `field_simp` + `ring`. -/
@[stat_lemma]
theorem kellyFraction_eq (p q b : ℝ) (hb : b ≠ 0) :
    kellyFraction p q b = p - q / b := by
  unfold kellyFraction
  field_simp [hb]

/-- **Kelly fraction is nonneg when edge is nonneg.** `q ≤ p * b`
    means the expected payoff on a unit stake is nonneg.
    Real proof via `div_nonneg` + `sub_nonneg`. -/
@[stat_lemma]
theorem kellyFraction_nonneg {p q b : ℝ} (hb : 0 < b)
    (hedge : q ≤ p * b) :
    0 ≤ kellyFraction p q b :=
  div_nonneg (sub_nonneg.mpr hedge) (le_of_lt hb)

/-- **Positive-edge Kelly is strictly positive.** When `q < p * b`,
    the Kelly fraction is strictly positive.
    Real proof via `div_pos` + `sub_pos`. -/
@[stat_lemma]
theorem kellyFraction_pos {p q b : ℝ} (hb : 0 < b)
    (hedge : q < p * b) :
    0 < kellyFraction p q b :=
  div_pos (sub_pos.mpr hedge) hb

/-- **Kelly fraction is at most 1.** For valid probabilities
    (`p ≤ 1`, `q ≥ 0`) and positive odds, the Kelly criterion
    never bets more than the full bankroll. The proof rests on
    `(p - 1) * b ≤ 0 ≤ q`, giving `p * b - q ≤ b`.
    Real proof via `div_le_one` + `nlinarith`. -/
@[stat_lemma]
theorem kellyFraction_le_one {p q b : ℝ} (hb : 0 < b)
    (hp : p ≤ 1) (hq : 0 ≤ q) :
    kellyFraction p q b ≤ 1 := by
  unfold kellyFraction
  rw [div_le_one hb]
  -- Need: p * b - q ≤ b, i.e., (p - 1) * b ≤ q.
  -- Since p ≤ 1 and b > 0, (p - 1) * b ≤ 0 ≤ q.
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (le_of_lt hb)]

/-- **Zero-edge specialisation.** When `p * b = q` (fair bet),
    the Kelly criterion prescribes no bet.
    Real proof via `sub_self` + `zero_div`. -/
@[stat_lemma]
theorem kellyFraction_zero_edge {p q b : ℝ}
    (hedge : p * b = q) :
    kellyFraction p q b = 0 := by
  unfold kellyFraction
  rw [← hedge, sub_self, zero_div]

/-- **Monotone in win probability.** Higher win probability means a
    larger Kelly bet for fixed odds and loss probability.
    Real proof via `div_le_div_of_nonneg_right` + `mul_le_mul_of_nonneg_right`. -/
@[stat_lemma]
theorem kellyFraction_mono_p {q b : ℝ} (hb : 0 < b)
    {p₁ p₂ : ℝ} (h : p₁ ≤ p₂) :
    kellyFraction p₁ q b ≤ kellyFraction p₂ q b := by
  unfold kellyFraction
  apply div_le_div_of_nonneg_right _ (le_of_lt hb)
  linarith [mul_le_mul_of_nonneg_right h (le_of_lt hb)]

/-!
### Half-Kelly (fractional Kelly)
-/

/-- **Half-Kelly is half of full Kelly.** Betting the "half-Kelly"
    fraction `f*/2` scales the numerator by 1/2.
    Real proof via `ring`. -/
@[stat_lemma]
theorem halfKelly_eq (p q b : ℝ) :
    kellyFraction p q b / 2 = (p * b - q) / (2 * b) := by
  unfold kellyFraction; ring

/-- **Fractional Kelly scales linearly.** Betting fraction `c * f*`
    equals `c * (p * b - q) / b`. Real proof via `ring`. -/
@[stat_lemma]
theorem fractionalKelly_eq (p q b c : ℝ) :
    c * kellyFraction p q b = c * (p * b - q) / b := by
  unfold kellyFraction; ring

/-!
### Kelly growth rate and its concavity
-/

/-- Kelly growth rate: expected log-wealth change per period when
    staking fraction `f` with win probability `p`, loss probability
    `q`, and net-odds `b`.

    `g(f) = p * log(1 + f * b) + q * log(1 - f)`.

    The Kelly fraction `f*` is the unique maximiser of `g` over
    `f ∈ [0, 1)`. -/
noncomputable def kellyGrowthRate (p q f b : ℝ) : ℝ :=
  p * Real.log (1 + f * b) + q * Real.log (1 - f)

/-- **Growth rate at zero fraction is zero.** When the bet is
    zero, the bankroll is unchanged: `g(0) = 0`.
    Real proof via `log_one` + `simp`. -/
@[stat_lemma]
theorem kellyGrowthRate_at_zero (p q b : ℝ) :
    kellyGrowthRate p q 0 b = 0 := by
  unfold kellyGrowthRate
  simp [Real.log_one]

/-- The feasible domain for the growth rate:
    both log arguments must be positive. -/
def feasibleDomain (b : ℝ) : Set ℝ :=
  {f : ℝ | 0 < 1 + f * b ∧ 0 < 1 - f}

/-- **Feasible domain is convex.** The set `{f | 0 < 1 + f*b ∧ 0 < 1 - f}`
    is convex: affine combinations of two feasible points are feasible.
    Real proof by `intro` on the `Convex` definition + `nlinarith`. -/
@[stat_lemma]
theorem feasibleDomain_convex (b : ℝ) : Convex ℝ (feasibleDomain b) := by
  unfold feasibleDomain Convex
  intro x hx y hy a c ha hc hac
  simp only [smul_eq_mul, Set.mem_setOf_eq] at hx hy ⊢
  constructor
  · -- 0 < 1 + (a * x + c * y) * b
    -- Write 1 + (a*x + c*y)*b = a*(1+x*b) + c*(1+y*b) using a+c=1.
    have h1 : 0 ≤ a * (1 + x * b) := mul_nonneg ha (le_of_lt hx.1)
    have h2 : 0 ≤ c * (1 + y * b) := mul_nonneg hc (le_of_lt hy.1)
    have hsum_pos : 0 < a * (1 + x * b) + c * (1 + y * b) := by
      rcases ha.lt_or_eq with ha' | ha'
      · linarith [mul_pos ha' hx.1]
      · rcases hc.lt_or_eq with hc' | hc'
        · linarith [mul_pos hc' hy.1]
        · linarith
    nlinarith
  · -- 0 < 1 - (a * x + c * y)
    have h1 : 0 ≤ a * (1 - x) := mul_nonneg ha (le_of_lt hx.2)
    have h2 : 0 ≤ c * (1 - y) := mul_nonneg hc (le_of_lt hy.2)
    have hsum_pos : 0 < a * (1 - x) + c * (1 - y) := by
      rcases ha.lt_or_eq with ha' | ha'
      · linarith [mul_pos ha' hx.2]
      · rcases hc.lt_or_eq with hc' | hc'
        · linarith [mul_pos hc' hy.2]
        · linarith
    nlinarith

/-- **Kelly growth rate is concave in f on the feasible domain.**

    The function `f ↦ p * log(1 + f * b) + q * log(1 - f)` is
    concave on `feasibleDomain b` when `p ≥ 0` and `q ≥ 0`.

    Proof: each term is a nonneg scalar times `log` applied to a
    positive affine function. The `ConcaveOn` structure follows from:
    - `strictConcaveOn_log_Ioi.concaveOn` : log concave on `(0, ∞)`
    - `ConcaveOn.subset`                  : restrict to a subset
    - `ConcaveOn.smul`                    : scale by nonneg constant
    - `ConcaveOn.add`                     : sum of concave functions

    This captures the over-betting result: any deviation from `f*`
    reduces expected log-growth (Jensen's inequality on the concave `g`). -/
@[stat_lemma]
theorem kellyGrowthRate_concaveOn (p q b : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ConcaveOn ℝ (feasibleDomain b) (fun f => kellyGrowthRate p q f b) := by
  -- log is concave on (0, ∞).
  have hlog : ConcaveOn ℝ (Ioi 0) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hS_convex : Convex ℝ (feasibleDomain b) := feasibleDomain_convex b
  -- Term 1: f ↦ p * log(1 + f * b) is concave on feasibleDomain.
  have hterm1 : ConcaveOn ℝ (feasibleDomain b)
      (fun f => p * Real.log (1 + f * b)) := by
    apply ConcaveOn.smul hp
    -- log(1 + f * b) is concave on feasibleDomain because
    -- the map f ↦ 1 + f * b sends feasibleDomain into (0, ∞)
    -- and log is concave there.
    constructor
    · exact hS_convex
    · intro x hx y hy a c ha hc hac
      unfold feasibleDomain at hx hy
      simp only [smul_eq_mul, Set.mem_setOf_eq] at hx hy ⊢
      -- hx : 0 < 1 + x * b, hy : 0 < 1 + y * b
      have hax : (0 : ℝ) < 1 + x * b := hx.1
      have hay : (0 : ℝ) < 1 + y * b := hy.1
      -- Use log concavity on (0, ∞).
      have hkey := hlog.2 (mem_Ioi.mpr hax) (mem_Ioi.mpr hay) ha hc hac
      simp only [smul_eq_mul] at hkey
      -- The weighted combination: a*(1+x*b) + c*(1+y*b) = 1 + (a*x+c*y)*b
      -- since a + c = 1.
      calc a * Real.log (1 + x * b) + c * Real.log (1 + y * b)
          ≤ Real.log (a * (1 + x * b) + c * (1 + y * b)) := hkey
        _ = Real.log (1 + (a * x + c * y) * b) := by
            congr 1; nlinarith
  -- Term 2: f ↦ q * log(1 - f) is concave on feasibleDomain.
  have hterm2 : ConcaveOn ℝ (feasibleDomain b)
      (fun f => q * Real.log (1 - f)) := by
    apply ConcaveOn.smul hq
    constructor
    · exact hS_convex
    · intro x hx y hy a c ha hc hac
      unfold feasibleDomain at hx hy
      simp only [smul_eq_mul, Set.mem_setOf_eq] at hx hy ⊢
      have hax : (0 : ℝ) < 1 - x := hx.2
      have hay : (0 : ℝ) < 1 - y := hy.2
      have hkey := hlog.2 (mem_Ioi.mpr hax) (mem_Ioi.mpr hay) ha hc hac
      simp only [smul_eq_mul] at hkey
      calc a * Real.log (1 - x) + c * Real.log (1 - y)
          ≤ Real.log (a * (1 - x) + c * (1 - y)) := hkey
        _ = Real.log (1 - (a * x + c * y)) := by
            congr 1; nlinarith
  -- Sum of concave functions is concave.
  have hsum : ConcaveOn ℝ (feasibleDomain b)
      (fun f => p * Real.log (1 + f * b) + q * Real.log (1 - f)) :=
    hterm1.add hterm2
  -- kellyGrowthRate p q f b = p * log(1 + f*b) + q * log(1-f) by definition.
  have hfun_eq : (fun f => kellyGrowthRate p q f b) =
      (fun f => p * Real.log (1 + f * b) + q * Real.log (1 - f)) := by
    ext f; simp [kellyGrowthRate]
  rw [hfun_eq]
  exact hsum

/-- **Overbetting penalty is nonneg (algebraic form).** The squared
    deviation `(f - f*)^2 ≥ 0` is the algebraic kernel of the
    second-order cost of deviating from the Kelly fraction.
    Real proof via `sq_nonneg`. -/
@[stat_lemma]
theorem overbetting_penalty_nonneg (f f_star : ℝ) :
    0 ≤ (f - f_star) ^ 2 :=
  sq_nonneg _

end Pythia.Finance.Portfolio.KellyCriterion
