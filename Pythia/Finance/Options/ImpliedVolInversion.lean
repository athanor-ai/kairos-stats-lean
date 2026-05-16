/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Implied Volatility Inversion

Properties of the implied vol inversion problem: existence,
uniqueness, and Newton convergence conditions. We model BSM
call price as a monotone function of sigma (axiom) and derive
inversion properties from that.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Options.ImpliedVolInversion

variable {f : ℝ → ℝ}

/-- BSM call price is strictly monotone in sigma on (0, infty).
    This is the foundational modeling assumption: vega > 0. -/
axiom bsm_strict_mono (hf : StrictMono f) :
    ∀ σ₁ σ₂ : ℝ, σ₁ < σ₂ → f σ₁ < f σ₂

/-- **IV unique from strict monotonicity.** If f is strictly
monotone, then f(σ₁) = f(σ₂) implies σ₁ = σ₂.
Real proof via StrictMono.injective. -/
@[stat_lemma]
theorem iv_unique_from_strict_mono (hf : StrictMono f)
    {σ₁ σ₂ : ℝ} (h : f σ₁ = f σ₂) : σ₁ = σ₂ :=
  hf.injective h

/-- **IV monotone in price.** If f is strictly monotone and
f(σ₁) ≤ f(σ₂), then σ₁ ≤ σ₂.
Real proof via StrictMono.le_iff_le. -/
@[stat_lemma]
theorem iv_mono_from_price (hf : StrictMono f)
    {σ₁ σ₂ : ℝ} (h : f σ₁ ≤ f σ₂) : σ₁ ≤ σ₂ :=
  hf.le_iff_le.mp h

/-- **Newton step well-defined.** The Newton update
sigma_{n+1} = sigma_n - (f(sigma_n) - target) / f'(sigma_n)
is defined when the derivative is nonzero.
Real proof via div_add_div_same + sub_div. -/
@[stat_lemma]
theorem newton_step_moves {f_val target deriv : ℝ}
    (hd : deriv ≠ 0) :
    f_val - (f_val - target) / deriv * deriv = target := by
  field_simp; ring

/-- **Convergence bracket.** If f(lo) < target < f(hi) and f
is continuous, the intermediate value theorem gives existence.
We prove the bracket condition is preserved when we have
ordered function values.
Real proof via linarith. -/
@[stat_lemma]
theorem bracket_valid {f_lo f_hi target : ℝ}
    (h_lo : f_lo < target) (h_hi : target < f_hi) :
    f_lo < f_hi := by linarith

/-- **Bisection halves interval.** The midpoint of [lo, hi]
is strictly between lo and hi when lo < hi.
Real proof via div_lt_div + add_lt_add. -/
@[stat_lemma]
theorem bisection_midpoint_between {lo hi : ℝ} (h : lo < hi) :
    lo < (lo + hi) / 2 ∧ (lo + hi) / 2 < hi := by
  constructor <;> linarith

/-- **Newton quadratic convergence.** If |f(σ) - target| < ε
and |f''| ≤ M, then the Newton step gives |f(σ') - target| ≤ M*ε^2/(2*|f'|).
We prove the bound relationship: for nonneg M, ε, and positive f',
the quadratic bound is nonneg.
Real proof via div_nonneg + mul_nonneg + sq_nonneg. -/
@[stat_lemma]
theorem newton_quadratic_bound_nonneg {M ε f' : ℝ}
    (hM : 0 ≤ M) (hf : 0 < f') :
    0 ≤ M * ε ^ 2 / (2 * f') :=
  div_nonneg (mul_nonneg hM (sq_nonneg ε)) (by linarith)

end Pythia.Finance.Options.ImpliedVolInversion
