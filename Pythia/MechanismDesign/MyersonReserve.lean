/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Myerson Optimal Reserve Price

## Main result

* `myerson_optimal_reserve_price` — If the virtual value function is
  monotone non-decreasing on `[0, ∞)` and equals zero at the reserve
  price `r*`, then every type `v < r*` has non-positive virtual value.

## Design note

The classical statement says "strictly negative" below `r*`, but
`MonotoneOn` provides only `≤` order preservation, not strict.
The strict version would require `StrictMonoOn` as a hypothesis,
which is a stronger regularity assumption.  We prove the weaker
`virtualValue F f v ≤ 0` form; a separate variant with
`StrictMonoOn` is left for future work.

## Proof sketch

`v < r*` implies `v ∈ Set.Ici 0` and `r* ∈ Set.Ici 0`; applying
`MonotoneOn` gives `φ(v) ≤ φ(r*)` = 0.

## References

* Myerson, R.B. "Optimal Auction Design".
  *Mathematics of Operations Research* 6(1): 58-73 (1981). Theorem 6.
* Nisan, Roughgarden, Tardos, Vazirani. *Algorithmic Game Theory* Ch. 3 §3.5
  (Cambridge University Press, 2007).
-/
import Mathlib

namespace Pythia.MechanismDesign

/-- The **virtual value** (or virtual surplus) associated with a distribution
with CDF `F` and density `f`.  This is the key quantity in Myerson's optimal
auction design: a bidder of type `v` contributes virtual value `φ(v)` to
the seller's revenue. -/
noncomputable def virtualValue (F f : ℝ → ℝ) (v : ℝ) : ℝ :=
  v - (1 - F v) / f v

/-- **Myerson optimal reserve price (monotone regularity, weak form).**
Under the regularity assumption that the virtual value function `φ` is
monotone non-decreasing on `[0, ∞)`, and given that `φ(r*) = 0` at the
reserve price `r*`, every type `v ∈ [0, r*)` has non-positive virtual value:
`φ(v) ≤ 0`.

Note: the classical Myerson theorem concludes `φ(v) < 0` (strictly negative)
below the reserve price.  `MonotoneOn` provides only `≤` preservation;
recovering strict monotonicity requires the hypothesis `StrictMonoOn`, which
is a stronger form of regularity.  The strict variant is deferred to a future
theorem `myerson_optimal_reserve_price_strict`. -/
theorem myerson_optimal_reserve_price
    (F f : ℝ → ℝ)
    (hregular : MonotoneOn (virtualValue F f) (Set.Ici 0))
    (r_star : ℝ) (hr_pos : 0 ≤ r_star)
    (hr : virtualValue F f r_star = 0) :
    ∀ v : ℝ, 0 ≤ v → v < r_star → virtualValue F f v ≤ 0 := by
  intro v hv hlt
  have hv_mem : v ∈ Set.Ici (0 : ℝ) := hv
  have hr_mem : r_star ∈ Set.Ici (0 : ℝ) := hr_pos
  have hmono := hregular hv_mem hr_mem (le_of_lt hlt)
  linarith [hr ▸ hmono]

end Pythia.MechanismDesign
