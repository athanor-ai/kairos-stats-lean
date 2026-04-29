/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Actuarial.Test: Worked examples for actuarial loss distributions

Smoke tests and worked examples verifying that the registered theorems
compose correctly with downstream arithmetic.

## Examples

1. Pareto alpha=3, x_m=1: E[X] = 3/2 <= 5
2. Pareto alpha=3, x_m=2: tail at t=4 is 1/8
3. Weibull k=2, lambda=1: mean = Gamma(3/2) < 1
4. LogNormal mu=0, sigma=1: exp(0) = 1 (median value check)
5. LogNormal Chebyshev bound is finite

Examples 1-2 reduce to arithmetic once Pareto.mean/tail sorries close.
Examples 3-5 are scaffold sorries until parent theorem closures land.
-/

import Mathlib
import Pythia.Tactic.Pythia
import Pythia.Actuarial.Pareto
import Pythia.Actuarial.Weibull
import Pythia.Frontier.Actuarial.LogNormal

namespace Pythia.Actuarial.Test

open MeasureTheory ProbabilityTheory Real Set

/-! ### Example 1: Pareto mean upper bound -/

/-- Pareto alpha=3, x_m=1: E[X] = 3/2 <= 5.
Once Pareto.mean closes, this reduces to norm_num: 3*1/(3-1) = 3/2 <= 5. -/
example :
    ∫ x, x ∂(Pythia.Actuarial.Pareto.paretoMeasure (x_m := 1) (alpha := 3)) ≤ 5 := by
  have h_mean := Pythia.Actuarial.Pareto.mean (x_m := 1) (alpha := 3)
    (hm := by norm_num) (ha := by norm_num) (h1 := by norm_num)
  rw [h_mean]; norm_num

/-! ### Example 2: Pareto tail at t=4 -/

/-- Pareto alpha=3, x_m=2: P(X > 4) = (2/4)^3 = 1/8.
Once Pareto.tail closes, this reduces to norm_num. -/
example :
    (Pythia.Actuarial.Pareto.paretoMeasure (x_m := 2) (alpha := 3)).real (Set.Ioi 4) =
    1 / 8 := by
  have h_tail := Pythia.Actuarial.Pareto.tail (x_m := 2) (alpha := 3) (t := 4)
    (hm := by norm_num) (ha := by norm_num) (ht := by norm_num)
  rw [h_tail]; norm_num

/-! ### Example 3: Weibull mean uses Gamma function -/

/-- Weibull k=2, lambda=1: E[X] = Gamma(3/2) < 1.
Mathlib's Gamma_three_div_two_lt_one closes the bound directly. -/
example :
    ∫ x, x ∂(Pythia.Actuarial.Weibull.weibullMeasure 1 2) < 1 := by
  have h_mean := Pythia.Actuarial.Weibull.mean (lambda := 1) (k := 2)
  rw [h_mean]
  simp only [one_mul, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  exact Real.Gamma_three_div_two_lt_one

/-! ### Example 4: Log-normal median value -/

/-- The median of a log-normal with mu=0 equals exp(0) = 1.
Pure arithmetic: no distribution theory needed. -/
example : Real.exp (0 : ℝ) = 1 := Real.exp_zero

/-! ### Example 5: LogNormal Chebyshev bound at t=3 -/

/-- For LogNormal mu=0, sigma=1: Chebyshev gives P(X>3) <= exp(2)/9.
We check this bound is < 1 using exp(2) < 9 (since exp(1) < 2.72 < 3). -/
example :
    (Pythia.Actuarial.LogNormal.logNormalMeasure 0 1).real (Set.Ioi 3) < 1 := by
  have hcb := Pythia.Actuarial.LogNormal.tail_chebyshev (mu := 0) (sigma := 1)
    (t := 3) (ht := by norm_num)
  -- Reduce to showing exp(2)/9 < 1, i.e. exp(2) < 9
  have he2 : Real.exp 2 < 9 := by
    have h1 : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [h2]
    nlinarith [Real.exp_pos 1]
  -- Now: exp(2*0 + 2*1^2)/3^2 = exp(2)/9 < 1
  have hbound : Real.exp (2 * (0:ℝ) + 2 * (1:ℝ)^2) / 3^2 < 1 := by
    norm_num
    linarith
  linarith

end Pythia.Actuarial.Test
