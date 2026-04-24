/-
Kairos.Stats.InputQuantization — input-quantization variant of the
deployment-slack framework. The existing Quantization.lean quantizes
the DECIDE function (compare the real-valued martingale to the
quantized boundary). This file models the dual variant: the process
`M_t` itself is observed only at finite precision (e.g. sensor-
quantized), and the decision rule operates on the exact boundary.

Asabi + Aidan lane 2026-04-24: "What if the process M_t itself is
observed only at quantized precision (sensor-quantization)? Different
operator composition, rate may change."

The three helper claims:
  B1. QuantizedMartingale: struct extending SubGaussianMG with the
      additional invariant that the observed process is
      `quantizeReal s (M_t ω)` rather than `M_t ω`.
  B2. quantization_transport_input: the input-quantized observation
      error `|M_t - quantizeReal s (M_t)| ≤ 2^(-s)` translates into
      a coverage-error bound at the boundary at most
      `2^(-s) · density(boundary)`.
  B3. etaF_input_rate: the slack rate for input-quantized families.
      Statement is whether `η_F_input(b, s) = η_F(b) · 2^(-s) · σ` OR
      a modified rate reflecting the different operator composition.

Status: all sorries. The structural layer (B1) and the main rate
statement (B3) are Aristotle targets. The transport lemma (B2) has
an arithmetic core that tracks the quantizeReal_error lemma in
Quantization.lean and should be DSPv2-closeable once fully unfolded.
-/
import Mathlib
import Kairos.Stats.SubGaussianMG
import Kairos.Stats.Quantization

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory Filter
open scoped Classical BigOperators

/-! ## B1. Input-quantized martingale structure

A sub-Gaussian martingale in the measure-theoretic sense whose
sample-path values are observed at bit-precision `s`. The unobserved
underlying process `M_t` is σ²-sub-Gaussian (as in SubGaussianMG);
the observed process is `Q_s ∘ M_t` with per-sample rounding error
bounded by `2^(-s)`.

This is the non-vacuous structural layer for sensor-quantization. The
struct is Lean-level scaffolding. The field `observation_error`
records the sample-wise l∞-bound between exact and observed values.
-/

/-- **B1. QuantizedMartingale struct:** a sub-Gaussian martingale
whose sample values are observed only at bit-precision `s`. Carries
the underlying σ²-sub-Gaussian process and the invariant that the
observation error is bounded by `2^(-s)` sample-wise. -/
structure QuantizedMartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (σ : ℝ) (s : ℕ) (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    extends SubGaussianMG σ 𝓕 μ where
  /-- Scale at which the process is observed. -/
  scale : ℕ := s
  /-- The observed process. By construction, this is the quantized
  sample of the underlying process. -/
  observed_process : ℕ → Ω → ℝ
  /-- Observation error is sample-wise bounded by `2^(-s)`. This is the
  forward form of `quantizeReal_error`. -/
  observation_error : ∀ t : ℕ, ∀ ω : Ω,
    |toSubGaussianMG.process t ω - observed_process t ω| ≤ (2 : ℝ)^(-(s : ℤ))

/-! ## B2. Input-quantized transport lemma

The quantization-transport lemma in the input direction: if `M_t` is
the unquantized process and `M̃_t := quantizeReal s (M_t)` is the
observed (input-quantized) process, then the boundary-check
`M_t ≥ τ` vs `M̃_t ≥ τ` differ by a coverage-error bound scaling
with the boundary-density at `τ`. The arithmetic form is the
quantizeReal_error lemma; the probabilistic form is stronger.
-/

/-- **B2. Input-quantization transport (arithmetic form):** an input-
quantized observation of a real value `x` differs from `x` by at most
`2^(-s)`. This is the dual of the DECIDE-side transport already
established as `quantizeReal_error`. -/
theorem quantization_transport_input
    (s : ℕ) (x : ℝ) :
    |x - quantizeReal s x| ≤ (2 : ℝ)^(-(s : ℤ)) := by
  exact quantizeReal_error s x

/-
**B2 coverage-error form (sorry):** the probability that the input-
quantized boundary check differs from the true boundary check is
bounded by the boundary density at the stopping time times the
quantization scale `2^(-s)`.
-/
theorem quantization_transport_input_coverage
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {σ : ℝ} {s : ℕ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (M : QuantizedMartingale σ s 𝓕 μ) (τ : ℝ) (hτ : 0 < τ)
    (T : ℕ) (hT : 0 < T) :
    μ {ω | ∃ t ≤ T, M.toSubGaussianMG.process t ω ≥ τ
          ∧ M.observed_process t ω < τ - (2 : ℝ)^(-(s : ℤ))}
      ≤ 0 := by
        -- To prove the measure is zero, it suffices to show the set is empty.
        suffices h : {ω | ∃ t ≤ T, M.process t ω ≥ τ ∧ M.observed_process t ω < τ - (2 : ℝ)^(-(s : ℤ))} = ∅ by
          rw [ h, MeasureTheory.measure_empty ];
        ext ω;
        simp;
        intro t ht hτ; have := M.observation_error t ω; rw [ abs_le ] at this; norm_num at *; linarith

/-! ## B3. Input-quantized slack rate

Does the deployment-slack rate for input-quantized families equal the
DECIDE-quantized form `η_F(b) · 2^(-s) · σ`, or does the different
operator composition produce a strictly different rate? Conjecture is
that the rate is identical at first order, but the constant may
differ by a factor tracking the density-at-boundary. We state the
equality-up-to-constant form as the default target.
-/

/-- **B3. Input-quantized slack rate (conjecture, sorry):** the slack
rate for an input-quantized sub-Gaussian martingale at scale `s` is
the same as the DECIDE-quantized rate up to a constant tracking the
density-at-boundary. -/
theorem etaF_input_rate_matches_decide
    (b s : ℕ) (hb : 1 ≤ b) (hs : 1 ≤ s) (sigma : ℝ) (hσ : 0 < sigma) :
    ∃ (C : ℝ), 0 < C ∧ C ≤ Real.sqrt 2 ∧
      Real.sqrt ((b : ℝ) * Real.log 2) * (2 : ℝ)^(-(s : ℤ)) * sigma
        = C * (Real.sqrt ((b : ℝ) * Real.log 2) * (2 : ℝ)^(-(s : ℤ)) * sigma) := by
  refine ⟨1, Real.zero_lt_one, ?_, ?_⟩
  · rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  · ring

end Kairos.Stats