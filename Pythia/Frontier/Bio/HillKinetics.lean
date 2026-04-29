/-
Pythia.Frontier.Bio.HillKinetics -- Hill equation cooperativity.

Reference: Hill, A.V. (1910). "The possible effects of the
aggregation of the molecules of haemoglobin on its dissociation
curves." J. Physiol. 40 (Suppl): iv-vii.

The Hill equation describes the fractional saturation of a
ligand-binding receptor as a function of ligand concentration:

    θ(c) = c^n / (K^n + c^n)

where n is the Hill coefficient (cooperativity) and K is the
half-saturation concentration. The function is bounded in [0, 1],
zero at c = 0, approaches 1 as c → ∞, and is strictly monotone
increasing in c for n ≥ 1, K > 0.
-/
import Mathlib

namespace Pythia.Frontier.Bio

/-- Hill saturation function. -/
noncomputable def hillSaturation (n : ℕ) (K c : ℝ) : ℝ :=
  c ^ n / (K ^ n + c ^ n)

/-
Hill saturation is bounded above by 1 for K > 0, c ≥ 0, n ≥ 1.
-/
theorem hillSaturation_le_one
    {n : ℕ} {K c : ℝ} (hn : 1 ≤ n) (hK : 0 < K) (hc : 0 ≤ c) :
    hillSaturation n K c ≤ 1 := by
  exact div_le_one_of_le₀ ( by linarith [ pow_nonneg hK.le n, pow_nonneg hc n ] ) ( by positivity )

/-
Hill saturation is monotone increasing in concentration for K > 0,
    n ≥ 1, c1 ≤ c2 with both nonneg.
-/
theorem hillSaturation_monotone_in_c
    {n : ℕ} {K c1 c2 : ℝ} (hn : 1 ≤ n) (hK : 0 < K)
    (hc1 : 0 ≤ c1) (hle : c1 ≤ c2) :
    hillSaturation n K c1 ≤ hillSaturation n K c2 := by
  unfold hillSaturation;
  rw [ div_le_div_iff₀ ] <;> try positivity;
  · nlinarith [ pow_le_pow_left₀ hc1 hle n, pow_nonneg hK.le n ];
  · exact add_pos_of_pos_of_nonneg ( pow_pos hK _ ) ( pow_nonneg ( by linarith ) _ )

/-
Hill saturation vanishes at zero concentration.
-/
theorem hillSaturation_zero
    {n : ℕ} {K : ℝ} (hn : 1 ≤ n) (hK : 0 < K) :
    hillSaturation n K 0 = 0 := by
  unfold hillSaturation; aesop;

end Pythia.Frontier.Bio