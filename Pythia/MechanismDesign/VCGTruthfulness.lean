/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# VCG Mechanism — Dominant-Strategy Incentive Compatibility

## Main result

* `vcg_truthfulness` — The Vickrey-Clarke-Groves mechanism with the Clarke
  pivot payment rule is dominant-strategy incentive compatible (DSIC):
  for every bidder `i`, truthful reporting maximizes `i`'s utility
  regardless of the reports submitted by the other bidders.

## Clarke pivot payment

Under the Clarke pivot rule the payment charged to bidder `i` is

  `p_i(a) = h_i − Σ_{j ≠ i} v_j(a_j)`

where `h_i` is a term that depends only on the reports of bidders other
than `i` (e.g. optimal social welfare of the others when `i` is absent)
and `a` is the chosen allocation. Because `h_i` is independent of `i`'s
own report it cancels when comparing utility under truthful reporting
vs. any deviation:

  `u_i(a) = v_i(a_i) − p_i(a) = Σ_j v_j(a_j) − h_i`

The VCG allocation `alloc_star` maximises `Σ_j v_j(a_j)`, so
`u_i(alloc_star) ≥ u_i(alloc_dev)` for every alternative `alloc_dev`.

## References

* Nisan, Roughgarden, Tardos, Vazirani. *Algorithmic Game Theory*,
  Theorem 9.16 (Cambridge University Press, 2007).
* Clarke, E.H. "Multipart pricing of public goods".
  *Public Choice* 11: 17-33 (1971).
* Groves, T. "Incentives in Teams".
  *Econometrica* 41(4): 617-631 (1973).
-/
import Mathlib

namespace Pythia.MechanismDesign

/-! ### Utility under the Clarke pivot rule -/

/-- Clarke pivot payment charged to bidder `i` given allocation `a`.
`h_i` is an arbitrary real that depends only on the other bidders' reports. -/
noncomputable def clarkePivotPayment
    {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (i : Fin n) (h_i : ℝ) (a : Fin n → Finset (Fin m)) : ℝ :=
  h_i - Finset.univ.sum (fun j => if j = i then 0 else v j (a j))

/-- Quasi-linear utility of bidder `i`: value for own bundle minus payment. -/
noncomputable def vcgUtility
    {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (i : Fin n) (h_i : ℝ) (a : Fin n → Finset (Fin m)) : ℝ :=
  v i (a i) - clarkePivotPayment v i h_i a

/-
The VCG utility of bidder `i` equals the total social welfare minus
the Clarke base term `h_i`.
-/
lemma vcgUtility_eq_socialWelfare_sub
    {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (i : Fin n) (h_i : ℝ) (a : Fin n → Finset (Fin m)) :
    vcgUtility v i h_i a =
      Finset.univ.sum (fun j => v j (a j)) - h_i := by
  unfold vcgUtility clarkePivotPayment;
  simp +decide [ Finset.sum_ite, Finset.filter_ne' ];
  ring

/-
**VCG dominant-strategy incentive compatibility (Theorem 9.16, NRTV).**

Under the Clarke pivot payment rule, truthful reporting is a (weakly)
dominant strategy for every bidder.  Concretely, for any bidder `i`,
the VCG utility under the welfare-maximising allocation `alloc_star`
is at least as large as under any alternative allocation `alloc_dev`
(which models what would result from a unilateral deviation by `i`).

The proof is that `h_i` cancels and the comparison reduces to
`SW(alloc_star) ≥ SW(alloc_dev)`, which is the defining property of
`alloc_star`.
-/
theorem vcg_truthfulness
    {n m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ)
    (alloc_star : Fin n → Finset (Fin m))
    (hmax : ∀ a : Fin n → Finset (Fin m),
        Finset.univ.sum (fun j => v j (alloc_star j)) ≥
        Finset.univ.sum (fun j => v j (a j)))
    (i : Fin n)
    (h_i : ℝ)
    (alloc_dev : Fin n → Finset (Fin m)) :
    vcgUtility v i h_i alloc_star ≥ vcgUtility v i h_i alloc_dev := by
  rw [ vcgUtility_eq_socialWelfare_sub, vcgUtility_eq_socialWelfare_sub ];
  exact sub_le_sub_right ( hmax alloc_dev ) _

end Pythia.MechanismDesign