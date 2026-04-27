/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Walras' Law (clearing-prices form)

In an n-good economy with prices `p : Fin n -> ℝ` and excess-demand
functions `z : Fin n -> ℝ`, market clearing requires that the inner
product of prices and excess demands is zero:

    ∑ i, p i * z i = 0.

This module models clearing as a hypothesis: when all individual
markets clear (z i = 0 for every good i), the Walras sum is zero.

## Main results

* `walrasLawSum`                        : the function `∑ i, p i * z i`
* `walras_clearing_implies_zero_sum`    : market clearing implies the sum is zero

## Why this lemma

Mathlib has `Finset.sum_eq_zero` but no named `walras` or
`excess_demand` declaration. Pythia exposes the Walras sum and its
clearing property so the `pythia` tactic cascade can close
general-equilibrium goals without the user reaching for the
underlying finset lemmas.

The companion empirical layer (`tools/sim/economics_walras.py`)
runs a PBT harness and a mutation suite to confirm the property
holds across all price scales and market sizes.

## References

* Walras, L. "Elements d'economie politique pure." L. Corbaz, Lausanne (1874).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Economics

/-- The Walras inner product of prices and excess demands.
    `walrasLawSum p z = ∑ i : Fin n, p i * z i`. -/
noncomputable def walrasLawSum {n : ℕ} (p z : Fin n → ℝ) : ℝ :=
  ∑ i, p i * z i

/-- **Walras' Law (clearing-prices form).** When every market clears
(`z i = 0` for all goods `i`), the Walras sum of price-weighted
excess demands is zero. -/
@[stat_lemma]
theorem walras_clearing_implies_zero_sum {n : ℕ} (p z : Fin n → ℝ)
    (h : ∀ i, z i = 0) : walrasLawSum p z = 0 := by
  unfold walrasLawSum
  apply Finset.sum_eq_zero
  intro i _
  rw [h i]
  ring

end Pythia.Economics
