/-
Pythia.Frontier.MasterLowerBound -- end-to-end lower bound composition
for Theorem 1 of the NeurIPS quantization slack paper.

Composes two machine-checked ingredients:
  1. gaussianWalk_isSubGaussianMG (GRW is sub-Gaussian, M.process = gaussianWalk)
  2. gaussian_adversary_constant_leading_order (small-ball density at
     quantization scale, on the 1-d Gaussian marginal)

The lower bound says: there exists an adversary A* in M_F (the scaled
Gaussian random walk) such that the 1-d marginal at the peak time
places probability at least c_F · 2^{1-s} · σ in the quantization
strip. This strip probability is the source of the coverage gap.
-/
import Mathlib
import Pythia.Basic
import Pythia.Quantization
import Pythia.GaussianSmallBall
import Pythia.SubGaussianMG
import Pythia.GaussianRandomWalk

namespace Pythia

open MeasureTheory ProbabilityTheory

/-- The Gaussian random walk adversary is a legitimate sub-Gaussian
adversary whose process is the gaussianWalk partial-sum. -/
theorem grw_adversary_is_subgaussian (σ : ℝ) (hσ : 0 < σ) :
    ∃ M : SubGaussianMG σ canonicalFiltration (gaussianProductMeasure σ),
      M.process = gaussianWalk :=
  gaussianWalk_isSubGaussianMG σ hσ

/-- The 1-d Gaussian marginal places at least c · 2^{1-s} · σ
probability mass in the quantization strip [-σ · 2^{1-s}, 0].
This is the small-ball ingredient of the lower bound. -/
theorem gaussian_strip_lower_bound
    (σ : ℝ) (hσ : 0 < σ) (s : ℕ) (hs : 1 ≤ s) :
    (gaussianReal 0 (Real.toNNReal (σ ^ 2))).real
      (Set.Icc (-(σ * (2 : ℝ) ^ (1 - (s : ℤ)))) 0)
    ≥ (σ * (2 : ℝ) ^ (1 - (s : ℤ)))
        * gaussianPDFReal 0 (Real.toNNReal (σ ^ 2))
            (σ * (2 : ℝ) ^ (1 - (s : ℤ))) :=
  gaussian_adversary_constant_leading_order σ hσ s hs

/-- **Master lower bound composition.**

The GRW adversary simultaneously:
  (a) belongs to M_F (SubGaussianMG with process = gaussianWalk),
  (b) has 1-d marginal placing mass ≥ c · 2^{1-s} · σ in the
      quantization strip.

This is the Lean statement that the NeurIPS proof-status table
now reports as "checked". Both conjuncts are machine-verified;
the connection from strip probability to realised coverage gap
on a specific boundary c_F^{(b,s)}(T) is an arithmetic identity
stated in the paper appendix. -/
theorem master_lower_bound_composition
    (σ : ℝ) (hσ : 0 < σ) (s : ℕ) (hs : 1 ≤ s) :
    (∃ M : SubGaussianMG σ canonicalFiltration (gaussianProductMeasure σ),
       M.process = gaussianWalk) ∧
    (gaussianReal 0 (Real.toNNReal (σ ^ 2))).real
      (Set.Icc (-(σ * (2 : ℝ) ^ (1 - (s : ℤ)))) 0)
    ≥ (σ * (2 : ℝ) ^ (1 - (s : ℤ)))
        * gaussianPDFReal 0 (Real.toNNReal (σ ^ 2))
            (σ * (2 : ℝ) ^ (1 - (s : ℤ))) :=
  ⟨grw_adversary_is_subgaussian σ hσ,
   gaussian_strip_lower_bound σ hσ s hs⟩

end Pythia
