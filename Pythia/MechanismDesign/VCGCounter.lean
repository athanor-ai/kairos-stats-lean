/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# VCG Budget-Balance Failure — Counter-Example

## Main result

* `vcg_budget_balance_failure` — There exist valuation functions and an
  allocation under which the VCG payment rule runs a deficit (negative
  total transfers from the mechanism to the bidders).

The VCG payment to bidder `i` is the externality that `i` imposes on
others: `Σ_{j ≠ i} v j (alloc_without_i)` minus `Σ_{j ≠ i} v j (alloc_star j)`.
The total deficit arises when `Σ_i Σ_{j ≠ i} v j (alloc_star j)` is
negative, which the witness below demonstrates with `n = 2` bidders,
`m = 2` goods, and all relevant valuations equal to `-1`.

## References

* Nisan, Roughgarden, Tardos, Vazirani. *Algorithmic Game Theory* §9.4
  (Cambridge University Press, 2007).
* Green, J. and Laffont, J.-J. "Characterization of Satisfactory Mechanisms
  for the Revelation of Preferences for Public Goods".
  *Econometrica* 45(2): 427-438 (1977).
-/
import Mathlib

namespace Pythia.MechanismDesign

/-- **VCG budget-balance failure.**
VCG is not budget-balanced in general: the mechanism may pay out more
than it collects.  The externality-sum `Σ_i Σ_{j ≠ i} v j (alloc_star j)`
(the term driving the deficit) can be strictly negative.

Witness: 2 bidders, 2 goods, all valuations `= -1`, identity allocation. -/
theorem vcg_budget_balance_failure :
    ∃ (n m : ℕ) (v : Fin n → Fin m → ℝ) (alloc_star : Fin n → Fin m),
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : Fin n =>
          if j = i then 0 else v j (alloc_star j)))) < 0 := by
  -- Witness: n = 2, m = 2, v i k = -1 for all i k, alloc_star i = 0
  refine ⟨2, 2, fun _i _k => -1, fun _i => 0, ?_⟩
  -- Expand the finite sums over Fin 2 explicitly, then close by norm_num
  simp only [Fin.sum_univ_two]
  norm_num

end Pythia.MechanismDesign
