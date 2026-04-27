/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cobb-Douglas Production Function

The Cobb-Douglas production function `Y(K, L) = K^α · L^(1-α)` is
the textbook production technology in growth theory and applied
microeconomics. The marquee property is **constant returns to scale**:
scaling all inputs by a factor `λ > 0` scales output by exactly `λ`.

## Main results

* `cobbDouglas`              : the production function `K^α · L^(1-α)`
* `cobb_douglas_crts`        : `Y(λK, λL) = λ · Y(K, L)` (constant returns to scale)
* `cobb_douglas_pos`         : `Y(K, L) > 0` when `K, L > 0` and `α ∈ (0, 1)`

## Why this lemma

Mathlib has `Real.rpow`, `mul_rpow`, and `Real.rpow_add` but no named
`cobb_douglas` declaration. Pythia exposes the production function +
its properties so the `pythia` tactic cascade can close goals about
it directly without the user reaching for the underlying real-power
lemmas.

The companion empirical layer (`tools/sim/economics_cobb_douglas.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation
harness so customers can verify the closed-form bound holds against
their own parameter ranges.

## References
* Cobb, C. W. and Douglas, P. H. "A Theory of Production".
  *American Economic Review* 18(Suppl): 139-165 (1928).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Economics

/-- The Cobb-Douglas production function `Y(K, L) = K^α · L^(1-α)`.
The arguments are unconstrained reals; the meaningful domain is
`K > 0, L > 0, 0 < α < 1`. -/
noncomputable def cobbDouglas (K L α : ℝ) : ℝ :=
  K ^ α * L ^ (1 - α)

/-- **Constant returns to scale.** For Cobb-Douglas with any exponent
`α`, scaling both inputs by `λ > 0` scales output by exactly `λ`.
This is the property that makes Cobb-Douglas the canonical CRTS
technology. -/
@[stat_lemma]
theorem cobb_douglas_crts
    {K L lam α : ℝ} (hK : 0 < K) (hL : 0 < L) (hlam : 0 < lam) :
    cobbDouglas (lam * K) (lam * L) α = lam * cobbDouglas K L α := by
  unfold cobbDouglas
  rw [Real.mul_rpow hlam.le hK.le, Real.mul_rpow hlam.le hL.le]
  rw [show (lam : ℝ) ^ α * K ^ α * (lam ^ (1 - α) * L ^ (1 - α))
        = (lam ^ α * lam ^ (1 - α)) * (K ^ α * L ^ (1 - α)) by ring]
  rw [← Real.rpow_add hlam]
  rw [show (α : ℝ) + (1 - α) = 1 by ring]
  rw [Real.rpow_one]

/-- **Output positivity.** For positive inputs and any α, the
Cobb-Douglas production function is strictly positive. -/
@[stat_lemma]
theorem cobb_douglas_pos {K L α : ℝ} (hK : 0 < K) (hL : 0 < L) :
    0 < cobbDouglas K L α := by
  unfold cobbDouglas
  exact mul_pos (Real.rpow_pos_of_pos hK α) (Real.rpow_pos_of_pos hL (1 - α))

end Pythia.Economics
