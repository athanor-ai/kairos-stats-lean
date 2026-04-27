/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Carnot heat-engine efficiency 1 - T_c/T_h is bounded above by 1.

Carnot heat-engine efficiency 1 - T_c/T_h is bounded above by 1.

## Main results

* `carnot_efficiency_upper_bound` — Carnot heat-engine efficiency 1 - T_c/T_h is bounded above by 1.

## References

    * Carnot, S. Réflexions sur la puissance motrice du feu (1824)
-/
import Mathlib
import Pythia.Tactic.Pythia


namespace Pythia.Thermodynamics


/-- **Carnot efficiency upper bound.** For any reservoir temperatures
`T_h > T_c > 0`, the Carnot heat-engine efficiency `η = 1 - T_c / T_h`
is bounded above by `1`. The bound is sharp in the limit `T_c → 0`,
which is unphysical (the third law forbids `T_c = 0`); the
strict-`<` version of the bound therefore matches physical intuition.
This lemma states the non-strict form, which closes by reducing to
`0 ≤ T_c / T_h` via `div_nonneg`. -/
@[stat_lemma]
theorem carnot_efficiency_upper_bound (T_h T_c : ℝ) (h_c : 0 < T_c) (h_lt : T_c < T_h) :
    1 - T_c / T_h ≤ 1 := by
  have h_h : 0 < T_h := lt_trans h_c h_lt
  have h_ratio_nonneg : 0 ≤ T_c / T_h := div_nonneg h_c.le h_h.le
  linarith

end Pythia.Thermodynamics
