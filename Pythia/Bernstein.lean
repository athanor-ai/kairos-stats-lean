/-
Pythia.Bernstein — Bernstein's inequality + Bennett-Bernstein
maximal inequality for martingales.

# Mathlib v4.28 status (verified 2026-04-25)

`grep -r "Bernstein" .lake/packages/mathlib/Mathlib/Probability/` returns
*nothing* probability-theoretic: the only `Bernstein`-named files are
the Bernstein polynomial (`RingTheory.Polynomial.Bernstein` /
`Analysis.SpecialFunctions.Bernstein`) and the Schroeder-Bernstein
cardinality theorem. Mathlib's probability layer ships only the
sub-Gaussian / Hoeffding family in
`Mathlib.Probability.Moments.SubGaussian`. The variance-aware
Bernstein form is not present.

This module therefore supplies Bernstein within `Pythia`. The
key wrapper lemma `bernstein_of_subGamma` is **closed without sorries**:
the proof is a one-liner reduction to `Pythia.subGamma_ville_ineq`
(which is itself fully closed in `Pythia.SubGamma`).

# Statement family

Given iid bounded random variables `X₁, …, X_n` with `|X_i| ≤ b`,
zero mean, and variance `σ²`, Bernstein's inequality bounds:

    P(S_n ≥ ε) ≤ exp(−ε² / (2 (n σ² + b ε / 3)))

Hoeffding gives `exp(−ε² / (2 n b²))`. When `σ² ≪ b²` (low-variance
bounded RVs), Bernstein wins by a factor of `b² / σ²` in the exponent.

This module supplies:

1. `bernstein_of_subGamma` — Bernstein's tail bound for sub-gamma
   martingales. **Fully closed**, registered with `@[stat_lemma]`. The
   universal black-box: every Bernstein-shaped concentration result
   in this library is supposed to factor through this lemma.
2. `bernstein_iid` — Bernstein for iid bounded RVs (unchanged
   scaffold; closure requires the bounded-implies-subGamma MGF
   embedding, which has no Mathlib support yet — see status note).
3. `bennett_iid` — Bennett's tighter Bernstein with explicit log
   factor (scaffold).
4. `bernstein_martingale` — Bennett-Bernstein maximal inequality for
   martingales with conditionally-bounded increments (scaffold).
5. `freedman` — Freedman's inequality (scaffold).

# Closure plan for the four remaining sorries

Each of `bernstein_iid`, `bennett_iid`, `bernstein_martingale`,
`freedman` reduces to constructing a `SubGammaMG` instance from
hypotheses about bounded random variables / martingales, then invoking
`bernstein_of_subGamma` (or the underlying `subGamma_ville_ineq`).

The blocking gap is the textbook MGF embedding for bounded centered
random variables: if `|X| ≤ b` a.s., `E[X|F] = 0`, `E[X²|F] ≤ ν`, then

    E[exp(λ X) | F]  ≤  exp(ν λ² / (2 (1 − b |λ| / 3)))   for `b|λ| < 3`.

The proof is a Taylor-series argument:
    exp(λ X) = 1 + λ X + (λ X)² · g(λ X)/2,
    g(x)    := 2 (exp(x) − 1 − x) / x²    (with g(0) = 1)
    g(x)    ≤ Σ_{k≥0} |x|^k / (k+2)!  ≤  Σ_{k≥0} (b|λ|/3)^k / 3^?  ≤  1 / (1 − b|λ|/3).
This requires:
  • `Real.exp_taylor_remainder` or equivalent (not yet in Mathlib v4.28).
  • `condExp_mul_le` for the cross term (in Mathlib).
  • `condExp_const_le` (in Mathlib).
The Taylor remainder is the only genuine gap. The path is either
(a) prove `g_bound : ∀ x, |x| ≤ r → g(x) ≤ 1 / (1 - r/3)` directly via
    the sum identity, or
(b) external-prover hammer once it's online for SubGamma.lean
    completion (Aidan 2026-04-25 directive: "local Mathlib closure first").

Tagging the wrapper `bernstein_of_subGamma` with `@[stat_lemma]`
means any downstream author who builds a `SubGammaMG` (e.g. via the
upcoming `bounded_to_subGamma : (...) → SubGammaMG (V) (b/3) 𝓕 μ`
helper) can close their Bernstein goal with `pythia`.
-/
import Mathlib
import Pythia.Basic
import Pythia.SubGamma
import Pythia.MGFBoundedSubGamma
import Pythia.Tactic.Pythia

namespace Pythia

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Section 1 — Bernstein for sub-gamma martingales (CLOSED)

This is the core lemma. It is a thin reparametrisation of
`subGamma_ville_ineq` that exposes the Bernstein-shape rate

    exp(-τ² / (2 (V + b τ / 3)))

instead of the sub-gamma-shape rate

    exp(-τ² / (2 ν N + 2 c τ)).

The two coincide under the substitution `(ν, c) := (V / N, b / 3)`,
i.e. the textbook embedding of bounded-increment martingales into
the sub-gamma class. -/

/-- **Bernstein's inequality, sub-gamma form.**

If `M : ℕ → Ω → ℝ` is a sub-gamma martingale with parameters
`(V / N, b / 3)` — that is, increments have conditional MGF bounded
by `exp((V/N) λ² / (2 (1 − (b/3) λ)))` for `b λ < 3` — and
starts at zero a.s., then for every `τ > 0` and `N ≥ 1`,

  ℙ{∃ t ≤ N, M_t ≥ τ} ≤ exp(− τ² / (2 (V + b τ / 3))).

The constants `V` and `b` correspond exactly to the textbook
parameters: `V` is the variance budget over `N` steps, `b` the
magnitude bound on the increments.

Proof: direct application of `subGamma_ville_ineq`, with the algebraic
identity `2 (V/N) N + 2 (b/3) τ = 2 V + (2/3) b τ = 2 (V + b τ/3)`.

Tagged `@[stat_lemma]` so `pythia` will dispatch to it for goals of
this exact shape (sub-gamma martingale + Bernstein-shape rate). -/
@[stat_lemma]
theorem bernstein_of_subGamma
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {V b : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    (M : SubGammaMG (V / N) (b / 3) 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ^2) / (2 * (V + b * τ / 3)))) := by
  -- Apply the sub-gamma Ville inequality as a black box.
  have h := subGamma_ville_ineq (M := M) hM0 τ hτ N hN
  -- Reshape the rate `exp(-τ²/(2(V/N)N + 2(b/3)τ))` into Bernstein form
  -- `exp(-τ²/(2(V + bτ/3)))`. The two denominators are equal as real
  -- numbers (algebra), hence the two exponentials are equal, hence the
  -- two ENNReal.ofReal images are equal.
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h_denom_eq :
      (2 * (V / N) * N + 2 * (b / 3) * τ) = 2 * (V + b * τ / 3) := by
    field_simp
  have h_rate_eq :
      Real.exp (-(τ^2) / (2 * (V / N) * N + 2 * (b / 3) * τ))
        = Real.exp (-(τ^2) / (2 * (V + b * τ / 3))) := by
    rw [h_denom_eq]
  rw [h_rate_eq] at h
  exact h

/-! ## Section 2 — Bernstein for iid bounded RVs (SCAFFOLD)

The classical textbook statement. Closure requires the bounded-→
sub-gamma MGF embedding (see file docstring). -/

/-- **Bernstein's inequality** for iid bounded random variables.
Given `X_i` iid with `|X_i| ≤ b` a.s., `E[X_i] = 0`, `Var(X_i) ≤ σ²`,
and `n` samples:
$$ P\left( \sum_{i=1}^n X_i \geq \varepsilon \right)
   \leq \exp\left( -\frac{\varepsilon^2}{2 (n \sigma^2 + b\varepsilon/3)} \right). $$

Closure path: needs the bounded-implies-subGamma MGF embedding (gap
flagged in file docstring). Once that ships, this reduces to
`bernstein_of_subGamma` with `V := n σ²`. -/
theorem bernstein_iid
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b : ℝ} {sigma_sq : ℝ}
    (hb_pos : 0 < b) (hsigma_sq_nonneg : 0 ≤ sigma_sq)
    (h_iid : ∀ t, ProbabilityTheory.IndepFun (X 0) (X t) μ)
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    (h_zero_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (h_var_bound : ∀ t, ∫ ω, (X t ω)^2 ∂μ ≤ sigma_sq)
    (n : ℕ) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | (Finset.range n).sum (fun i => X i ω) ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps^2) / (2 * (n * sigma_sq + b * eps / 3)))) := by
  -- Closure plan (blocking on Pythia.MGFBoundedSubGamma):
  --   1. Build SubGammaMG (n * sigma_sq / n) (b / 3) 𝓕 μ from the iid hypotheses,
  --      using mgf_le_subGamma_of_bounded (in Pythia.MGFBoundedSubGamma) for the
  --      increment MGF bound. Requires StandardBorelSpace Ω (add to hypotheses).
  --   2. The partial-sum process S_t = Σ_{i<t} X_i is adapted to 𝓕_t = σ(X_0,...,X_{t-1}).
  --   3. Apply bernstein_of_subGamma with V := n * sigma_sq, hN := hn, τ := eps.
  --   4. The rate exponent matches: exp(-eps²/(2*(n*sigma_sq + b*eps/3)))
  --      = exp(-eps²/(2*(V + b*eps/3))) with V = n*sigma_sq.
  --   5. Structural detail: need iIndepFun hypothesis (stronger than h_iid) to construct
  --      the filtration and independence correctly. Current h_iid uses pairwise IndepFun.
  -- Unblocked once exp_le_bernstein_abs closes in MGFBoundedSubGamma.lean (§1).
  sorry

-- `bennett_iid` was a `True := by sorry` placeholder here. The real
-- inequality with the closed-form Bennett ψ-function landed in
-- `Pythia.Bennett` (Aristotle import 2026-04-26, project 7e11d4c4).
-- See `Pythia/Bennett.lean`.

/-- **Bernstein's inequality for martingales** (Freedman): a
martingale with conditionally-bounded increments and predictable
variance process satisfies a Bernstein-type bound. Supersedes
Azuma-Hoeffding when conditional variance is small.

Reduces to `bernstein_of_subGamma` once the conditional-MGF embedding
is available. -/
theorem bernstein_martingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : MeasureTheory.Martingale M 𝓕 μ)
    (b : ℝ) (hb_pos : 0 < b)
    (h_bounded_increments : ∀ t, ∀ᵐ ω ∂μ,
      |M (t + 1) ω - M t ω| ≤ b)
    (V_n : ℝ) (hV_pos : 0 < V_n)
    (h_predictable_var : ∀ t,
      μ[fun ω => (M (t + 1) ω - M t ω)^2 | 𝓕 t] =ᵐ[μ] (fun _ => V_n / (t + 1 : ℝ)))
    (n : ℕ) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | M n ω ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps^2) / (2 * (V_n + b * eps / 3)))) := by
  -- Closure plan (structural work beyond MGFBoundedSubGamma):
  --   1. Derive conditional MGF bound from h_bounded_increments and h_predictable_var:
  --      E[exp(lam * (M_{t+1} - M_t)) | 𝓕_t] ≤ exp(V_n/(t+1) * lam² / (2*(1-b*lam/3))) a.s.
  --      This uses mgf_le_subGamma_of_bounded applied conditionally (conditional Jensen).
  --   2. Construct SubGammaMG (V_n/n) (b/3) 𝓕 μ from M.
  --   3. Apply bernstein_of_subGamma to get the MAXIMAL inequality form,
  --      then extract the fixed-time bound P(M_n ≥ eps) by set monotonicity
  --      ({M_n ≥ eps} ⊆ {∃ t ≤ n, M_t ≥ eps}).
  -- Blocking: (a) conditional MGF application requires conditional Jensen in Mathlib,
  -- (b) non-iid martingale increments need a different independence argument.
  sorry

/-- **Freedman's inequality**: the maximal-inequality form of
`bernstein_martingale`. Bounds `P(sup_{t ≤ n} M_t ≥ ε)` rather than
the fixed-time `P(M_n ≥ ε)`. Useful for sequential stopping
problems.

Closes via `bernstein_of_subGamma`. -/
theorem freedman
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_mart : MeasureTheory.Martingale M 𝓕 μ)
    (b : ℝ) (hb_pos : 0 < b)
    (h_bounded_increments : ∀ t, ∀ᵐ ω ∂μ,
      |M (t + 1) ω - M t ω| ≤ b)
    (V_n : ℝ) (hV_pos : 0 < V_n)
    (n : ℕ) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | ∃ t : ℕ, t ≤ n ∧ M t ω ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps^2) / (2 * (V_n + b * eps / 3)))) := by
  -- Closure plan (requires SubGammaMG instance from bounded martingale increments):
  --   1. From h_bounded_increments, apply mgf_le_subGamma_of_bounded conditionally
  --      to each increment (M_{t+1} - M_t) given 𝓕_t, using the a.s. bound on
  --      E[(M_{t+1}-M_t)²|𝓕_t] ≤ V_n (from h_mart + h_bounded_increments via
  --      conditional Jensen on the bounded increment: E[ΔM²|𝓕_t] ≤ b²).
  --      The predictable variance h_predictable_var gives exact control of
  --      the conditional second moment, enabling the tighter Bernstein rate.
  --   2. Construct M' : SubGammaMG (V_n / n) (b / 3) 𝓕 μ from M and h_mart.
  --   3. Apply bernstein_of_subGamma hN M' hM0 heps directly to conclude.
  --   Note: M.process 0 = 0 a.s. is a standard assumption; needs to be added
  --   to the hypotheses or derived from h_mart + martingale initialization.
  -- Blocking: conditional MGF bound step (same as bernstein_martingale above).
  sorry

end Pythia
