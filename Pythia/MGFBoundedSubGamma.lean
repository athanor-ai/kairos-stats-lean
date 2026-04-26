/-
Pythia.MGFBoundedSubGamma — MGF bound for bounded centred random variables.

## Main result

`mgf_le_subGamma_of_bounded`: for `X : Ω → ℝ` with `|X| ≤ b` a.s.,
`μ[X] = 0`, `μ[X²] ≤ σ²`, and `0 ≤ lam` with `b * lam < 3`,

    mgf X μ lam  ≤  exp(σ² * lam² / (2 * (1 - b * lam / 3))).

This is the sub-gamma envelope with parameters `(ν, c) = (σ², b/3)`:

    mgf X μ lam  ≤  exp(ν * lam² / (2 * (1 - c * lam)))

with `c * lam = (b/3) * lam < 1`.

This bridge lemma connects `Pythia.bernstein_iid` to the sub-gamma
machinery in `Pythia.SubGamma` by constructing a `SubGammaMG σ² (b/3) 𝓕 μ`
from iid bounded centred random variables.

## Proof structure

The key analytical step is pointwise: for `u ∈ ℝ` with `|u| < 3`,

    exp u  ≤  1 + u + u² / (2 * (1 - |u|/3)).                 (*)

Proof of (*): expand `exp u = Σ u^k/k!` and bound term-by-term.
For k ≥ 2: `u^k/k! ≤ (u²/2) * (|u|/3)^(k-2)` since `2 * 3^(k-2) ≤ k!`.
Summing the geometric series gives the right-hand side.

The integral step:
    μ[exp(lam * X)] ≤ μ[1 + lam*X + (lam*X)²/(2(1-b*lam/3))]
                    = 1 + lam·μ[X] + lam²·μ[X²]/(2(1-b*lam/3))
                    ≤ 1 + lam²·σ²/(2(1-b*lam/3))   (using μ[X]=0, μ[X²]≤σ²)
                    ≤ exp(lam²·σ²/(2(1-b*lam/3)))   (using 1+t ≤ exp(t))

## Mathlib v4.28 gaps

The term-by-term geometric bound `2 * 3^(k-2) ≤ k!` (k ≥ 2) and its
summation to a geometric series requires `Nat.factorial` reasoning and
`tsum` convergence. Until a self-contained Lean proof is verified, the
key analytical helper `exp_le_bernstein_pointwise` is marked `sorry`
with this explicit closure plan:

Closure plan for `exp_le_bernstein_pointwise`:
  1. `h_factorial : ∀ k : ℕ, 2 ≤ k → 2 * 3^(k-2) ≤ k.factorial`
       Proof: induction on k; base k=2: 2*1=2=2!; k=3: 2*3=6=3!;
       step k+1: 2*3^(k-1) ≤ (k+1)! follows since 2*3*3^(k-2) ≤ (k+1)*k!
       holds for k ≥ 3 because k+1 ≥ 4 > 3 and 2*3^(k-2) ≤ k!.
  2. Pointwise: `u^k / k! ≤ u^2 / 2 * (u/3)^(k-2)` follows from h_factorial.
  3. `hasSum (fun k => u^k/k!) (exp u)` — from `Real.exp_hasSum`.
  4. Split sum at k=2; bound tail by geometric series via `tsum_geometric_of_lt_one`.
  5. Conclude (*) from `hasSum` + tsum inequality.

The rest of the file (`mgf_le_subGamma_of_bounded`, `mgf_iid_increment_subGamma`)
is scaffolded as honest sorries, each reducing to `exp_le_bernstein_pointwise`
once that is available.
-/
import Mathlib
import Pythia.Basic
import Pythia.SubGamma

namespace Pythia

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

/-! ## §1  Pointwise analytic bound -/

/-- **Key analytical helper (scaffold).**

For any `u : ℝ` with `0 ≤ u` and `u < 3`,
`exp u  ≤  1 + u + u^2 / (2 * (1 - u / 3))`.

Equivalently: `exp u - 1 - u ≤ u^2 / (2 * (1 - u/3))`.

This is the Bernstein MGF pointwise bound. The proof is a
term-by-term comparison of Taylor series:
  `Σ_{k≥2} u^k/k! ≤ (u²/2) · Σ_{k≥0} (u/3)^k`
using `2 * 3^(k-2) ≤ k!` for every `k ≥ 2`.

**Closure plan**: see module docstring §"Mathlib v4.28 gaps". The proof
uses `Real.exp_hasSum`, `Nat.factorial` induction, and `tsum_geometric_of_lt_one`.
No new Mathlib upstream is needed; all ingredients are in Mathlib v4.28.
-/
lemma exp_le_bernstein_pointwise (u : ℝ) (hu0 : 0 ≤ u) (hu3 : u < 3) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 * (1 - u / 3)) := by
  -- Closure plan: Taylor series term comparison. See module docstring.
  sorry

/-- Combined: for `|u| < 3`,
`exp u ≤ 1 + u + u^2 / (2 * (1 - |u| / 3))`.

For `u ≥ 0`: direct from `exp_le_bernstein_pointwise`.
For `u < 0` with `-3 < u`: use `exp u ≤ 1 + u + u²/(2(1-|u|/3))`.
The term `u²/(2(1-|u|/3))` dominates the negative `1+u` for most `u ≤ 0`.
Full case analysis in the closure plan.

**Closure plan**: case split on `0 ≤ u` vs `u < 0`. For `u ≥ 0`, apply
`exp_le_bernstein_pointwise` (with `|u| = u`). For `u < 0`, show separately
that `exp u ≤ 1 + u + u²/(2*(1+u/3))` using the `u < 0` Taylor analysis:
`exp u = 1 + u + u²/2 · g(u)` where `g(u) = 2(exp u - 1 - u)/u² ≤ 1/(1-|u|/3)`.
Since `g` is an even function of the series `Σ u^(k-2)·2/k!` and each term
satisfies `2/k! ≤ (1/3)^(k-2)` for `k ≥ 2`, the bound holds uniformly in sign.
-/
lemma exp_le_bernstein_abs (u : ℝ) (hu : |u| < 3) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 * (1 - |u| / 3)) := by
  -- Closure plan: case split on sign of u, use exp_le_bernstein_pointwise for u ≥ 0.
  sorry

/-! ## §2  MGF bound from bounded support -/

/-- **MGF bound for bounded centred random variables.**

If `X : Ω → ℝ` satisfies
- `h_bdd : ∀ᵐ ω ∂μ, |X ω| ≤ b`  (where `0 < b`)
- `h_mean : ∫ ω, X ω ∂μ = 0`
- `h_var : ∫ ω, (X ω)^2 ∂μ ≤ σ_sq`
- `hlam0 : 0 ≤ lam`  and  `hblam : b * lam < 3`

then `mgf X μ lam ≤ exp(σ_sq * lam^2 / (2 * (1 - b * lam / 3)))`.

## Proof sketch (three steps)

**Step 1 (pointwise)**:  since `|X ω| ≤ b` a.s. and `b * lam < 3`, we have
`|lam * X ω| ≤ b * lam < 3` a.s., so by `exp_le_bernstein_abs`:
  `exp(lam * X ω) ≤ 1 + lam * X ω + (lam * X ω)^2 / (2*(1-|lam*X ω|/3))`
  `              ≤ 1 + lam * X ω + lam^2 * (X ω)^2 / (2*(1-b*lam/3))`
(the denominator: `1 - |lam * X ω|/3 ≥ 1 - b*lam/3 > 0` since `|X ω| ≤ b`).

**Step 2 (integrate)**:
  `mgf X μ lam = ∫ exp(lam * X ω) ∂μ`
  `           ≤ 1 + lam * ∫ X ω ∂μ + lam^2/(2*(1-b*lam/3)) * ∫ (X ω)^2 ∂μ`
  `           = 1 + 0 + lam^2/(2*(1-b*lam/3)) * ∫ (X ω)^2 ∂μ`    (h_mean)
  `           ≤ 1 + σ_sq * lam^2 / (2*(1-b*lam/3))`.              (h_var)

**Step 3 (close with `1 + t ≤ exp t`)**:
  `mgf X μ lam ≤ 1 + σ_sq * lam^2 / (2*(1-b*lam/3)) ≤ exp(σ_sq * lam^2 / (2*(1-b*lam/3)))`.
  Uses `Real.add_one_le_exp`.

**Blocking**: Step 1 requires `exp_le_bernstein_abs` (§1, currently sorry).
Steps 2-3 use `MeasureTheory.integral_mono`, `Integrable.const_mul`, and
`Real.add_one_le_exp` — all in Mathlib v4.28.
-/
theorem mgf_le_subGamma_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b σ_sq lam : ℝ}
    (hb : 0 < b) (hσ_sq : 0 ≤ σ_sq)
    (hlam0 : 0 ≤ lam) (hblam : b * lam < 3)
    (h_meas : AEMeasurable X μ)
    (h_int : Integrable (fun ω => Real.exp (lam * X ω)) μ)
    (h_sq_int : Integrable (fun ω => (X ω) ^ 2) μ)
    (h_bdd : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (h_mean : ∫ ω, X ω ∂μ = 0)
    (h_var : ∫ ω, (X ω) ^ 2 ∂μ ≤ σ_sq) :
    mgf X μ lam ≤ Real.exp (σ_sq * lam ^ 2 / (2 * (1 - b * lam / 3))) := by
  -- The denominator is positive since b * lam < 3.
  have hd_pos : 0 < 1 - b * lam / 3 := by linarith
  -- The exponent t := σ_sq * lam^2 / (2*(1-b*lam/3)) is non-negative.
  have ht_nonneg : 0 ≤ σ_sq * lam ^ 2 / (2 * (1 - b * lam / 3)) :=
    div_nonneg (mul_nonneg hσ_sq (sq_nonneg lam))
      (mul_nonneg two_pos.le hd_pos.le)
  -- Blocking: steps 1–3 above. Unblocked once exp_le_bernstein_abs closes.
  sorry

/-! ## §3  Sub-gamma increment bound for iid bounded centred RVs -/

/-- **Sub-gamma MGF increment bound for iid bounded centred RVs (scaffold).**

Given `X : ℕ → Ω → ℝ` iid with `|X i| ≤ b` a.s., `E[X i] = 0`,
`E[(X i)²] ≤ σ_sq`, and `(b/3) * |lam| < 1`, the conditional MGF of
the increment `X (t+1)` (independent of `𝓕 t`) satisfies:

  `E[exp(lam * X (t+1)) | 𝓕 t]`
  `= E[exp(lam * X (t+1))]`        (by independence of X(t+1) from 𝓕_t)
  `= mgf (X (t+1)) μ lam`
  `≤ exp(σ_sq * lam^2 / (2*(1-(b/3)*lam)))`    (by mgf_le_subGamma_of_bounded)

This is the `SubGammaMG σ_sq (b/3)` increment condition with `ν = σ_sq`, `c = b/3`.

**Closure plan** (once `mgf_le_subGamma_of_bounded` is available):
  1. The partial-sum increment `S_{t+1} - S_t = X (t+1)` is independent
     of `𝓕 t = σ(X 0, …, X t)` by the iid hypothesis.
  2. Conditional expectation of a `𝓕_t`-independent integrand equals the
     unconditional expectation: apply `ProbabilityTheory.condExp_of_indepFun`
     or an analogous Mathlib lemma for measurable functions.
  3. Apply `mgf_le_subGamma_of_bounded` to get `mgf (X (t+1)) μ lam ≤ exp(...)`.
  4. Conclude the a.s. bound via `ae_of_all` + step 2.

**Status**: honest-sorry. Blocking on `mgf_le_subGamma_of_bounded` (§2).
-/
theorem mgf_iid_increment_subGamma
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b σ_sq : ℝ}
    (hb : 0 < b) (hσ_sq : 0 ≤ σ_sq)
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_var : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤ σ_sq)
    (h_meas : ∀ i, Measurable (X i))
    (h_int_exp : ∀ (i : ℕ) (lam : ℝ), (b / 3) * |lam| < 1 →
      Integrable (fun ω => Real.exp (lam * X i ω)) μ)
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (h_adapt : ∀ i, Measurable[𝓕 i] (X i))
    -- X (t+1) is independent of X 0, used as a proxy for filtration independence
    (h_indep : ∀ t, ProbabilityTheory.IndepFun
      (fun ω => X (t + 1) ω) (fun ω => X 0 ω) μ)
    (t : ℕ) (lam : ℝ) (hlam : (b / 3) * |lam| < 1) :
    ∀ᵐ ω ∂μ,
      (μ[fun ω' => Real.exp (lam * X (t + 1) ω') | 𝓕 t]) ω ≤
        Real.exp (σ_sq * lam ^ 2 / (2 * (1 - (b / 3) * lam))) := by
  -- Blocking on mgf_le_subGamma_of_bounded (§2) and conditional-expectation
  -- independence. See closure plan in docstring.
  sorry

end Pythia
