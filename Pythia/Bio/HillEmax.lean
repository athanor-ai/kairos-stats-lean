/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hill Emax Saturation Limit

The Hill equation for pharmacodynamic effect with maximal effect E_max,
Hill coefficient n, and half-maximal concentration EC50 is:

    E(c) = E_max · c^n / (EC50^n + c^n)

## Main result

* `hill_emax_saturation_limit` — E(c) → E_max as c → ∞.

## Proof strategy

Write E(c) = E_max · c^n / (EC50^n + c^n) = E_max · (1 - EC50^n/(EC50^n + c^n)).
Since EC50^n + c^n → ∞ as c → ∞ (because c^n → ∞), the ratio EC50^n/(EC50^n + c^n) → 0.
Therefore E(c) → E_max · (1 - 0) = E_max.

The `hillSaturation` definition from `Pythia.Frontier.Bio.HillKinetics` is
`c^n / (EC50^n + c^n)`, so the theorem is stated in terms of that definition.

## References

* Hill, A.V. "The possible effects of the aggregation of the molecules of
  haemoglobin on its dissociation curves." J. Physiol. (1910) 40 (Suppl): iv-vii.
* Holford, N.H.G. and Sheiner, L.B. "Understanding the dose-effect relationship."
  Clin. Pharmacokinet. (1981) 6: 429-453.
-/
import Mathlib
import Pythia.Tactic.Pythia
import Pythia.Frontier.Bio.HillKinetics

namespace Pythia.Bio.HillEmax

/-- **Hill Emax saturation limit.**
The E_max model `E(c) = E_max · hillSaturation(n, EC50, c)` converges to `E_max`
as the concentration c → ∞.

The limit is proved by writing the expression as `E_max · (1 - EC50^n/(EC50^n + c^n))`
and using that EC50^n/(EC50^n + c^n) → 0 as c → ∞. -/
@[stat_lemma]
theorem hill_emax_saturation_limit
    (Emax EC50 : ℝ) (n : ℕ)
    (hE : 0 < Emax) (hEC : 0 < EC50) (hn : 1 ≤ n) :
    Filter.Tendsto
      (fun c : ℝ => Emax * Pythia.Frontier.Bio.hillSaturation n EC50 c)
      Filter.atTop
      (nhds Emax) := by
  unfold Pythia.Frontier.Bio.hillSaturation
  -- c^n → ∞ as c → ∞ (using c^n = c^(n:ℝ) and rpow_atTop)
  have h_pow_atTop : Filter.Tendsto (fun c : ℝ => c ^ n) Filter.atTop Filter.atTop := by
    simp_rw [← Real.rpow_natCast]
    apply tendsto_rpow_atTop
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn |> Nat.pos_of_ne_zero |> Nat.cast_pos.mpr
  -- EC50^n + c^n → ∞
  have h_denom_atTop : Filter.Tendsto (fun c : ℝ => EC50 ^ n + c ^ n) Filter.atTop Filter.atTop := by
    have h : Filter.Tendsto (fun c : ℝ => c ^ n + EC50 ^ n) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_add h_pow_atTop tendsto_const_nhds
    exact h.congr (fun c => by ring)
  -- EC50^n / (EC50^n + c^n) → 0
  have h_ratio_zero : Filter.Tendsto (fun c : ℝ => EC50 ^ n / (EC50 ^ n + c ^ n)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop h_denom_atTop _
  -- 1 - EC50^n/(EC50^n + c^n) → 1
  have h_sub_one : Filter.Tendsto (fun c : ℝ => 1 - EC50 ^ n / (EC50 ^ n + c ^ n)) Filter.atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop)).sub h_ratio_zero
    simpa using h
  -- Emax · (1 - EC50^n/(EC50^n + c^n)) → Emax · 1 = Emax
  have h_main : Filter.Tendsto (fun c : ℝ => Emax * (1 - EC50 ^ n / (EC50 ^ n + c ^ n)))
      Filter.atTop (nhds Emax) := by
    have h := h_sub_one.const_mul Emax
    simpa using h
  -- The functions agree for all large c (c > 0)
  apply h_main.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with c hc
  have hcn_pos : 0 < c ^ n := pow_pos hc n
  have hECn_pos : 0 < EC50 ^ n := pow_pos hEC n
  field_simp
  ring

end Pythia.Bio.HillEmax
