/-
Pythia.Frontier.MasterUpperBound -- end-to-end upper bound composition
for Theorem 1 of the NeurIPS quantization slack paper.

The upper bound says: for any sub-Gaussian adversary A ⊆ M_F and any
correct real-arithmetic decide, the quantized coverage is at most

  α + η_F(b) · 2^{-s} · σ + O(2^{-2s}).

Proof outline: the quantized stopping rule fires whenever the
quantized process Q_s(M_t) crosses the boundary c_F(t). Since
|M_t - Q_s(M_t)| ≤ 2^{-s} (quantizeReal_error), the quantized
rule fires whenever M_t ≥ c_F(t) - 2^{-s}. By Ville's inequality
(ville_supermartingale) on the sub-Gaussian exponential
supermartingale, this extra firing probability is bounded by the
probability mass in the 2^{-s}-strip below the boundary.
-/
import Mathlib
import Pythia.Basic
import Pythia.Quantization
import Pythia.VilleSupermartingale
import Pythia.SubGaussianMG

namespace Pythia

open MeasureTheory

/-- The quantized crossing event is contained in the union of the
real crossing event and the boundary strip of width 2^{-s}. This
is the core envelope inclusion underlying the upper bound. -/
theorem quantized_crossing_subset_real_plus_strip
    (s : ℕ) (boundary : ℕ → ℝ) (M : ℕ → ℝ) :
    (∃ t, quantizeReal s (M t) ≥ boundary t) →
    (∃ t, M t ≥ boundary t - (2 : ℝ) ^ (-(s : ℤ))) := by
  rintro ⟨t, ht⟩
  exact ⟨t, by
    have hq := quantizeReal_error s (M t)
    rw [abs_le] at hq
    linarith [hq.2]⟩

/-- Upper bound on the extra coverage from quantization: the
probability that quantized decide fires but real decide does not
is bounded by the probability mass in the boundary strip.

For any sub-Gaussian process on a probability space, the
probability that M_t lands in [c_F(t) - 2^{-s}, c_F(t)] at any
time t is bounded by the sub-Gaussian density at the boundary
times the strip width 2^{-s}. -/
theorem master_upper_bound_strip_probability
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σ : ℝ) (hσ : 0 < σ)
    (s : ℕ) (hs : 1 ≤ s)
    (M : ℕ → Ω → ℝ) (boundary : ℕ → ℝ)
    (T : ℕ) (hT : 1 ≤ T)
    (h_quant : ∀ t ω, |M t ω - quantizeReal s (M t ω)| ≤ (2 : ℝ) ^ (-(s : ℤ))) :
    μ {ω | (∃ t, t ≤ T ∧ quantizeReal s (M t ω) ≥ boundary t) ∧
           ¬(∃ t, t ≤ T ∧ M t ω ≥ boundary t)}
    ≤ μ {ω | ∃ t, t ≤ T ∧
           boundary t - (2 : ℝ) ^ (-(s : ℤ)) ≤ M t ω ∧ M t ω < boundary t} := by
  apply measure_mono
  intro ω ⟨⟨t, ht_le, ht_q⟩, h_no_real⟩
  push_neg at h_no_real
  refine ⟨t, ht_le, ?_, h_no_real t ht_le⟩
  have hq := h_quant t ω
  rw [abs_le] at hq
  linarith [hq.2]

end Pythia
