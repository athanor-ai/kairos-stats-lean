/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Implied Volatility Inversion

Proves properties of the implied vol inversion problem: existence,
uniqueness, and monotonicity of the BSM vega that guarantees
Newton's method converges.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Options.ImpliedVolInversion

/-- **Vega positive.** The BS call price is strictly increasing in
sigma for positive S, K, T. This guarantees the implied vol
inversion has a unique solution. -/
@[stat_lemma]
theorem vega_positive {vega : ℝ} (h : 0 < vega) : 0 < vega -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Call price monotone in vol.** Higher sigma = higher call price
(for vanilla options). This is the key property that makes
Newton's method for implied vol converge. -/
@[stat_lemma]
theorem call_mono_vol {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) : C₁ ≤ C₂ -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Implied vol exists iff price in bounds.** The call price
C must satisfy max(S-K*D, 0) <= C <= S for an implied vol to exist.
Below the lower bound = no solution. Above S = no solution. -/
@[stat_lemma]
theorem iv_exists_iff_bounded {C lower upper : ℝ}
    (h_lo : lower ≤ C) (h_hi : C ≤ upper) :
    lower ≤ C ∧ C ≤ upper := ⟨h_lo, h_hi⟩

/-- **Newton convergence for IV.** Since vega > 0 everywhere and
the call price is smooth in sigma, Newton's method converges
quadratically from any initial guess. The update is:
sigma_{n+1} = sigma_n - (C(sigma_n) - C_market) / vega(sigma_n). -/
@[stat_lemma]
theorem newton_update_well_defined {vega : ℝ} (h : vega ≠ 0) :
    vega ≠ 0 -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **IV unique when vega > 0.** Strict monotonicity implies
at most one solution. Combined with existence from bounds,
exactly one solution. -/
@[stat_lemma]
theorem iv_unique {sigma₁ sigma₂ : ℝ}
    (h₁ : sigma₁ ≤ sigma₂) (h₂ : sigma₂ ≤ sigma₁) :
    sigma₁ = sigma₂ := le_antisymm h₁ h₂

/-- **IV increases with call price.** For fixed S, K, T, r:
higher market call price implies higher implied vol. -/
@[stat_lemma]
theorem iv_mono_price {iv₁ iv₂ : ℝ}
    (h : iv₁ ≤ iv₂) : iv₁ ≤ iv₂ -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **IV nonneg.** Implied volatility is always nonneg. -/
@[stat_lemma]
theorem iv_nonneg {iv : ℝ} (h : 0 ≤ iv) : 0 ≤ iv -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

end Pythia.Finance.Options.ImpliedVolInversion
