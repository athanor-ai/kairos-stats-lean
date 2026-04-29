/-
Pythia.Neuroscience.ShannonHartley -- channel capacity for a noisy
spike-rate readout, applied to neural information transmission.

Reference: Shannon, C.E. (1948). "A mathematical theory of
communication." Bell System Technical Journal 27(3):379-423.
Applied to neural coding: Rieke, F. et al. (1997). "Spikes:
Exploring the neural code." MIT Press.

The Shannon-Hartley capacity of a continuous channel with bandwidth B
and signal-to-noise ratio S/N is

  C = B * log2(1 + S/N).

In neural coding, this gives an upper bound on the information rate
achievable by a noisy spike-rate code.
-/
import Mathlib

namespace Pythia.Neuroscience

/-- Shannon-Hartley channel capacity. -/
noncomputable def shannonHartleyCapacity (B SNR : ℝ) : ℝ :=
  B * Real.logb 2 (1 + SNR)

/-- Capacity is monotone nondecreasing in SNR for B ≥ 0 and SNR ≥ 0. -/
theorem shannonHartleyCapacity_monotone_in_snr
    {B SNR1 SNR2 : ℝ} (hB : 0 ≤ B) (hSNR1 : 0 ≤ SNR1) (hSNR : SNR1 ≤ SNR2) :
    shannonHartleyCapacity B SNR1 ≤ shannonHartleyCapacity B SNR2 := by
  unfold shannonHartleyCapacity
  apply mul_le_mul_of_nonneg_left _ hB
  have h_pos : 0 < 1 + SNR1 := by linarith
  have h_log2_pos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h_log_le : Real.log (1 + SNR1) ≤ Real.log (1 + SNR2) :=
    Real.log_le_log h_pos (by linarith)
  unfold Real.logb
  exact (div_le_div_iff_of_pos_right h_log2_pos).mpr h_log_le

/-- Capacity is nonneg when B ≥ 0 and SNR ≥ 0. -/
theorem shannonHartleyCapacity_nonneg
    {B SNR : ℝ} (hB : 0 ≤ B) (hSNR : 0 ≤ SNR) :
    0 ≤ shannonHartleyCapacity B SNR := by
  unfold shannonHartleyCapacity
  apply mul_nonneg hB
  apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
  linarith

/-- Capacity vanishes at zero SNR. -/
theorem shannonHartleyCapacity_zero_at_zero_snr (B : ℝ) :
    shannonHartleyCapacity B 0 = 0 := by
  unfold shannonHartleyCapacity
  rw [add_zero, Real.logb_one, mul_zero]

end Pythia.Neuroscience
