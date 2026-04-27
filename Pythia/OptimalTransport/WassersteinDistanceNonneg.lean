/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Discrete L1 Wasserstein-style cost non-negativity

The L1 Wasserstein distance `W_1(μ, ν)` between two probability
measures is non-negative by construction. This module proves the
discrete simplification: for two real-valued maps `p q : Fin n → ℝ`
(thought of as probability mass functions over `n` atoms), the
discrete transport cost `∑ i, |p i - q i|` is non-negative. This is
the absolute-value form of the discrete W_1 distance and the bound
holds for arbitrary `p`, `q` (no probability-distribution hypothesis
is needed for non-negativity, only for total-mass identities).

## Main results

* `wasserstein_distance_nonneg` — `∑ i, |p i - q i| ≥ 0` for any
  `p q : Fin n → ℝ`.

## Why this lemma

Mathlib has `Finset.sum_nonneg` and `abs_nonneg` as primitives but
no named lemma packaging the discrete W_1 cost positivity. Pythia
exposes the bound under its OT-flavored name so the `pythia` tactic
cascade can close transport-style goals without the user reaching
for the underlying summation lemmas.

## References

* Vaserstein, L.N. "Markov processes over denumerable products of
  spaces describing large system of automata." Problemy Peredachi
  Informatsii 5(3): 64-72 (1969).
* Kantorovich, L.V. "On the translocation of masses." Doklady
  Akademii Nauk SSSR 37: 199-201 (1942).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.OptimalTransport

/-- **Discrete L1 Wasserstein-style cost non-negativity.** For any
two real-valued maps `p q : Fin n → ℝ`, the absolute-difference sum
`∑ i, |p i - q i|` is non-negative. Closes by `Finset.sum_nonneg`
applied to the term-wise non-negativity from `abs_nonneg`. -/
@[stat_lemma]
theorem wasserstein_distance_nonneg {n : ℕ} (p q : Fin n → ℝ) :
    0 ≤ ∑ i, |p i - q i| :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (p i - q i))

end Pythia.OptimalTransport
