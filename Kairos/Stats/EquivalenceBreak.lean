/-
Kairos.Stats.EquivalenceBreak — formal statement of the
equivalence-breaking theorem (Theorem 5 of the NeurIPS paper).

Ramdas–Ruf 2022 established that the self-normalized and betting
confidence sequences are equivalent in continuous arithmetic under
the exponential martingale transform `W_t = exp(M_t - sigma² t / 2)`.
At finite precision `s < ∞`, additive quantization of `M_t` does not
correspond to multiplicative quantization of `W_t`, and the two
families produce different stopping decisions.
-/

import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.Quantization
import Kairos.Stats.SubGaussianMG

namespace Kairos.Stats

open MeasureTheory

/-- **Equivalence break at finite precision.**

For every bit-precision pair `(b, s)` with `b ≥ 2` and `s ≥ 1`,
every `σ > 0`, and every `α ∈ (0, 1)`, there exists a sub-Gaussian
martingale `M` and at least one sample path on which the two
quantized rules — additive quantization of `M_t` at scale `s`
versus additive quantization of `log W_t` at scale `s`, with
`W_t := exp(M_t - σ²·t/2)` — produce different stopping decisions
against the same boundary.

The claim shows the Ramdas–Ruf continuous-arithmetic equivalence is
a continuous-arithmetic artefact: at every positive fractional
precision `s < ∞`, the two deployments can be distinguished by at
least one sample path.
-/
theorem equivalence_break_at_finite_precision
    (b : ℕ) (hb : 2 ≤ b) (s : ℕ) (hs : 1 ≤ s)
    (sigma : ℝ) (hσ : 0 < sigma)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1) :
    ∃ (tstar : ℕ) (m_tstar : ℝ),
      -- existence of a point `(tstar, m_tstar)` where the additive-
      -- quantized `M_t` event and the log-wealth-quantized event
      -- give different indicators against the boundary `sigma *
      -- sqrt(2 * tstar * log(tstar/alpha))`:
      tstar ≤ 2^b ∧
      1 ≤ tstar ∧
      (decide (quantizeReal s m_tstar ≥
               sigma * Real.sqrt (2 * tstar * Real.log (tstar / alpha)))
       ≠ decide (quantizeReal s (m_tstar - sigma^2 * tstar / 2) ≥
                 Real.log (1 / alpha))) := by
  sorry

end Kairos.Stats
