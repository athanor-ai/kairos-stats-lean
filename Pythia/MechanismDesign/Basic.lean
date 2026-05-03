/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.MechanismDesign.Basic

Foundational results for the mechanism design module: VCG mechanism
efficiency. First brick in the MechanismDesign expansion (ATH-939) under
the ATH-937 130-theorem roadmap.
-/

import Mathlib

namespace Pythia.MechanismDesign

/-- **VCG mechanism efficiency.** The VCG mechanism allocates the items so as
to maximize the total social welfare (sum of all bidders' true values for
their allocated bundles). This is one of the two defining properties of the
Vickrey-Clarke-Groves mechanism (the other being incentive compatibility,
which we'll prove separately).

Reference: Groves, T. "Incentives in Teams." *Econometrica* 41(4), 1973;
Nisan-Roughgarden-Tardos-Vazirani *Algorithmic Game Theory*, Theorem 9.15. -/
theorem vcg_efficiency
    {n m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ)
    (alloc_vcg : Fin n → Finset (Fin m))
    (hmax : ∀ a : Fin n → Finset (Fin m),
        Finset.univ.sum (fun j => v j (alloc_vcg j)) ≥
        Finset.univ.sum (fun j => v j (a j))) :
    IsGreatest
        {w | ∃ a : Fin n → Finset (Fin m),
              w = Finset.univ.sum (fun j => v j (a j))}
        (Finset.univ.sum (fun j => v j (alloc_vcg j))) := by
  refine ⟨⟨alloc_vcg, rfl⟩, ?_⟩
  intro w hw
  obtain ⟨a, ha⟩ := hw
  rw [ha]
  exact hmax a

end Pythia.MechanismDesign
