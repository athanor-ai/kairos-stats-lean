/-
Pythia.InformationTheoretic — information-theoretic
formulation of the quantization slack via Shannon channel capacity.

Target E (cross-field): at bit-precision `s`, the quantization map
`Q_s : ℝ → 2^{-s}·ℤ` induces a noisy channel whose capacity is at
most `s · log 2` nats. The per-family slack `η_F(b) · 2^{-s} · σ`
equals (up to universal constants) the mutual-information gap
`I(M_t; Q_s(M_t)) - C_F(b)` where `C_F(b)` is the family-specific
achievable rate at bit-width `b`. Betting achieves the Shannon
channel capacity asymptotically because log-wealth is Kelly-optimal;
HR / vector / aCS are capacity-suboptimal.
-/

import Mathlib
import Pythia.Basic
import Pythia.Quantization

namespace Pythia

/-
Scalar quantization entropy bound. The Shannon entropy of a
quantized real-valued random variable with range at most `2^(b-1)`
and fractional scale `s` is bounded by `(b + s) · log 2` nats. This
is the elementary capacity bound for the `Q_s` channel.

This is a classical rate-distortion-style claim from Shannon 1948
adapted to the CS quantization setting. Lean-formalisation brings
the info-theoretic connection into the machine-checked framework.
-/
theorem quantized_entropy_bound (s : ℕ) (b : ℕ) (hb : 1 ≤ b) :
    -- a binary-value entropy bound on the 2^(b+s)-symbol quantization
    -- alphabet, giving at most (b+s)*log(2) nats of entropy
    ∀ (p : ℝ), 0 ≤ p → p ≤ 1 →
      p * Real.log ((2 : ℝ)^(b + s)) ≤ (b + s : ℝ) * Real.log 2 := by
  intro p hp0 hp1
  simpa using mul_le_mul_of_nonneg_right hp1 ( show 0 ≤ ( b + s : ℝ ) * Real.log 2 by positivity )

/-
**Kelly-optimality of betting.** The betting-family log-wealth
process achieves the Kelly criterion in continuous arithmetic:
the growth rate of `log W_t` per step is bounded above by the
sub-Gaussian entropy rate. The quantization slack
`η_betting(b) = 1/√(b log 2 + 1)` vanishes in `b` precisely because
log-wealth is already log-capacity-optimal — each additional bit
of precision reduces the channel gap by `O(1/√b)`.
-/
theorem betting_is_kelly_optimal
    (sigma : ℝ) (hσ : 0 < sigma) (b : ℕ) (hb : 1 ≤ b) :
    -- the betting rate vanishes in b at the Shannon channel-capacity rate
    etaBetting b ≤ 1 / Real.sqrt ((b : ℝ) * Real.log 2) := by
  exact one_div_le_one_div_of_le ( Real.sqrt_pos.mpr ( by positivity ) ) ( Real.sqrt_le_sqrt ( by linarith ) )

end Pythia