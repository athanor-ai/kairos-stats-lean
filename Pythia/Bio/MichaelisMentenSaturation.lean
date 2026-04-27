/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Michaelis-Menten reaction velocity v = Vmax*S/(Km+S) is bounded above by Vmax.

Michaelis-Menten reaction velocity v = Vmax*S/(Km+S) is bounded above by Vmax.

## Main results

* `michaelis_menten_saturation` — Michaelis-Menten reaction velocity v = Vmax*S/(Km+S) is bounded above by Vmax.

## References

    * Michaelis, L. and Menten, M.L. Biochem. Z. 49: 333-369 (1913)
-/
import Mathlib
import Pythia.Tactic.Pythia


namespace Pythia.Bio


/-- **Michaelis-Menten saturation.** For non-negative `Vmax`,
positive Michaelis constant `Km`, and non-negative substrate
concentration `S`, the Michaelis-Menten reaction velocity
`v = Vmax * S / (Km + S)` is bounded above by `Vmax`. The bound is
saturated only in the limit `S → ∞`. The proof reduces the inequality
to `0 ≤ Vmax * Km` via `div_le_iff` on the strictly-positive
denominator, and closes by `nlinarith` from non-negativity of the
factors. -/
@[stat_lemma]
theorem michaelis_menten_saturation (Vmax Km S : ℝ)
    (h_vmax : 0 ≤ Vmax) (h_km : 0 < Km) (h_s : 0 ≤ S) :
    Vmax * S / (Km + S) ≤ Vmax := by
  have h_denom : 0 < Km + S := by linarith
  rw [div_le_iff₀ h_denom]
  nlinarith [mul_nonneg h_vmax h_km.le, mul_nonneg h_vmax h_s]

end Pythia.Bio
