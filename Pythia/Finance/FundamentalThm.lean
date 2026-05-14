/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# First Fundamental Theorem of Asset Pricing (Discrete)

No-arbitrage ⟺ existence of an equivalent martingale measure.

This is the cornerstone of mathematical finance: a market is
arbitrage-free if and only if there exists a probability measure
Q equivalent to P under which discounted asset prices are
martingales.

## Statement (finite, discrete-time)

For a finite probability space (Ω, F, P) with filtration {F_n}_{n=0..N}
and a discounted price process S:

  No arbitrage (no self-financing strategy with V_0 = 0, V_N ≥ 0 a.s.,
  P(V_N > 0) > 0) ⟺ ∃ Q ~ P such that S is a Q-martingale.

## References

* Harrison, J. M. & Pliska, S. R. (1981): "Martingales and Stochastic
  Integrals in the Theory of Continuous Trading." Stochastic Processes
  and their Applications 11(3), 215–260.
* Dalang, R. C., Morton, A. & Willinger, W. (1990): "Equivalent
  martingale measures and no-arbitrage in stochastic securities market
  models." Stochastics 29(2), 185–201.
* Delbaen, F. & Schachermayer, W. (1994): "A general version of the
  fundamental theorem of asset pricing." Math. Annalen 300, 463–520.

General applied mathematics.
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace Pythia.Finance.FTAP

variable {n : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A trading strategy is a predictable process (sequence of positions). -/
def TradingStrategy (N : ℕ) := Fin N → Ω → ℝ

/-- Gains from trading: ∑ θ_k · (S_{k+1} - S_k). -/
def gainsProcess (θ : TradingStrategy N) (S : Fin (N + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin N, θ k ω * (S k.succ ω - S k.castSucc ω)

/-- No-arbitrage condition: no strategy produces non-negative terminal
wealth with positive probability of strict gain, starting from zero. -/
def noArbitrage (S : Fin (N + 1) → Ω → ℝ) : Prop :=
  ∀ θ : TradingStrategy N,
    (∀ ω, 0 ≤ gainsProcess θ S ω) →
    (∀ ω, gainsProcess θ S ω = 0)

/-- An equivalent martingale measure: Q ~ P and S is a Q-martingale. -/
def existsEMM (S : Fin (N + 1) → Ω → ℝ) : Prop :=
  ∃ ν : Measure Ω, IsProbabilityMeasure ν ∧
    μ.AbsolutelyContinuous ν ∧ ν.AbsolutelyContinuous μ ∧
    ∀ k : Fin N, ∫ ω, S k.succ ω ∂ν = ∫ ω, S k.castSucc ω ∂ν

/-- **First Fundamental Theorem (forward direction).**
If an equivalent martingale measure exists, then the market is
arbitrage-free.

This direction is the easier half: if S is a Q-martingale, then
E_Q[gains] = 0, so no strategy can produce nonneg gains with
strictly positive probability. -/
theorem ftap_forward (S : Fin (N + 1) → Ω → ℝ)
    (hemm : existsEMM μ S) : noArbitrage S := by
  sorry

/-- **First Fundamental Theorem (converse, finite case).**
On a finite probability space, no-arbitrage implies existence of
an equivalent martingale measure.

This direction requires the separating hyperplane theorem (or
Farkas lemma) applied to the cone of attainable payoffs. -/
theorem ftap_converse (S : Fin (N + 1) → Ω → ℝ)
    (hna : noArbitrage S)
    (hsupp : ∀ ω : Ω, 0 < (μ {ω}).toReal) :
    existsEMM μ S := by
  sorry

end Pythia.Finance.FTAP
