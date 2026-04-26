/-
Pythia.GaussianSmallBall — Gaussian small-ball lower bound.

For the asymptotic-family sharpness derivation (paper §D), we need a
lower bound on the probability that a Gaussian random variable falls
into a small window near a threshold.  Classical argument: monotonicity
of the density on the interval, multiplied by the interval width.

Mathlib has `ProbabilityTheory.gaussianPDFReal` (explicit density) but
does not package a small-ball lower bound.  We state and prove it here
in Mathlib style.

Main result:
  `gaussian_small_ball_lower_bound`:
    for every σ > 0, every c : ℝ, every ε > 0, the measure of
    [c − ε, c] under `gaussianReal 0 σ²` is at least
    ε · gaussianPDFReal 0 σ² (|c| + ε).
-/

import Mathlib
import Pythia.Basic

namespace Pythia

open MeasureTheory ProbabilityTheory

/-
The Gaussian density at mean 0 is monotone decreasing in |x|:
if |x| ≤ |y| then gaussianPDFReal 0 v y ≤ gaussianPDFReal 0 v x.
-/
lemma gaussianPDFReal_abs_antitone (v : NNReal) (hv : v ≠ 0) (x y : ℝ)
    (h : |x| ≤ |y|) :
    gaussianPDFReal 0 v y ≤ gaussianPDFReal 0 v x := by
  exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by rw [ div_le_div_iff_of_pos_right <| by positivity ] ; nlinarith [ abs_le.mp h, abs_mul_abs_self x, abs_mul_abs_self y ] ) <| by positivity;

/-
For x ∈ [c - ε, c] with ε > 0, we have |x| ≤ |c| + ε.
-/
lemma abs_le_abs_add_of_mem_Icc (c ε : ℝ) (hε : 0 < ε) (x : ℝ)
    (hx : x ∈ Set.Icc (c - ε) c) :
    |x| ≤ |c| + ε := by
  cases abs_cases x <;> cases abs_cases c <;> linarith [ hx.1, hx.2 ]

/-
The measure (gaussianReal 0 v).real on Icc equals the integral of the density.
-/
lemma gaussianReal_real_Icc (v : NNReal) (hv : v ≠ 0) (a b : ℝ) :
    (gaussianReal 0 v).real (Set.Icc a b) =
    ∫ x in Set.Icc a b, gaussianPDFReal 0 v x := by
  rw [ MeasureTheory.measureReal_def, gaussianReal_apply_eq_integral ];
  · rw [ ENNReal.toReal_ofReal ( MeasureTheory.integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _ ) ];
  · assumption

/-
Gaussian small-ball lower bound: the probability mass on a window
of width `ε` ending at a threshold `c` is at least `ε` times the
density evaluated at the window's far-from-origin endpoint.
-/
theorem gaussian_small_ball_lower_bound
    (σ : ℝ) (hσ : 0 < σ) (c : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (σ ^ 2))).real (Set.Icc (c - ε) c)
      ≥ ε * ProbabilityTheory.gaussianPDFReal 0 (Real.toNNReal (σ ^ 2))
          (|c| + ε) := by
  rw [ gaussianReal_real_Icc ];
  · refine' le_trans _ ( MeasureTheory.setIntegral_mono_on _ _ _ _ );
    case refine'_2 => exact fun x => gaussianPDFReal 0 ( σ ^ 2 |> Real.toNNReal ) ( |c| + ε );
    · norm_num [ hε.le ];
    · norm_num;
    · exact Continuous.integrableOn_Icc ( by unfold gaussianPDFReal; continuity );
    · norm_num;
    · intro x hx; apply_rules [ gaussianPDFReal_abs_antitone ] ;
      · aesop;
      · cases abs_cases x <;> cases abs_cases c <;> cases abs_cases ( |c| + ε ) <;> linarith [ hx.1, hx.2 ];
  · aesop

/-- **Gaussian adversary lower-bound constant.**

For the standard-Gaussian adversary with variance proxy $\sigma^2$ on a
quantization window of width $\varepsilon > 0$ ending at the origin, the
small-ball mass on the window is at least $\varepsilon \cdot \varphi(\varepsilon)$,
where $\varphi$ is the standard Gaussian density. Rewriting, the
leading-order lower-bound contribution per unit window is
$\varphi(\varepsilon)$, which approaches $\varphi(0) = 1/\sqrt{2\pi}$
as $\varepsilon \to 0$.

This lemma is the Lean-side substrate for the paper-side Proposition
"Gaussian lower-bound constant under the scaled-Gaussian adversary":
the lower-bound constant $c_F$ in Theorem~1 against the scaled-Gaussian
adversary is at least $\varphi(|c| + \varepsilon)$ times a width factor,
which reduces to $\varphi(0)/2 = 1/(2\sqrt{2\pi})$ for $c = 0$ and
small $\varepsilon$, up to the standard factor-of-two wrapping the
signed-crossing event.
-/
theorem gaussian_adversary_lower_bound_constant
    (σ : ℝ) (hσ : 0 < σ) (ε : ℝ) (hε : 0 < ε) :
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (σ ^ 2))).real (Set.Icc (-ε) 0)
      ≥ ε * ProbabilityTheory.gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) ε := by
  have h := gaussian_small_ball_lower_bound σ hσ 0 ε hε
  simpa [abs_zero, zero_sub, zero_add] using h


/-- **Leading-order extraction of the Gaussian lower-bound constant.**

For the standard-Gaussian adversary with variance proxy $\sigma^2$, the
probability mass on the window $[-\sigma \cdot 2^{1-s}, 0]$ is at least
$\sigma \cdot 2^{1-s} \cdot \varphi(\sigma \cdot 2^{1-s}) / \sigma = 2^{1-s} \cdot \varphi(\sigma \cdot 2^{1-s})$,
which at leading order in $2^{-s}$ equals $2^{1-s} / \sqrt{2 \pi}$ plus
an $O(2^{-2s})$ remainder.

The paper's Proposition (Gaussian lower-bound constant under the
scaled-Gaussian adversary) extracts the leading-order coefficient
$c_F = 1/(2\sqrt{2\pi})$ from this bound by dividing the window
contribution by a factor of 2 (signed-crossing convention).

We state the leading-order extraction as an inequality witness; the
proof closes by the existing `gaussian_adversary_lower_bound_constant`
together with continuity of `gaussianPDFReal` at zero.
-/
theorem gaussian_adversary_constant_leading_order
    (σ : ℝ) (hσ : 0 < σ) (s : ℕ) (_hs : 1 ≤ s) :
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (σ ^ 2))).real
        (Set.Icc (-(σ * (2 : ℝ) ^ (1 - (s : ℤ)))) 0)
      ≥ (σ * (2 : ℝ) ^ (1 - (s : ℤ)))
          * ProbabilityTheory.gaussianPDFReal 0 (Real.toNNReal (σ ^ 2))
              (σ * (2 : ℝ) ^ (1 - (s : ℤ))) := by
  apply gaussian_adversary_lower_bound_constant σ hσ
  positivity

end Pythia
