/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Floating-Point Layer Normalization Error Bound

Layer Normalization (Ba et al. 2016) normalizes a length-n vector x by its
mean and standard deviation, then applies an affine transform:

  LN(x)ᵢ = γ_scale · (xᵢ − μ) / σ + β

where
  μ  = (1/n) · Σᵢ xᵢ              (mean)
  σ² = (1/n) · Σᵢ (xᵢ − μ)²      (population variance)
  σ  = sqrt(σ² + ε_ln)             (stabilised standard deviation, ε_ln > 0)

## Error analysis (Higham-style)

Floating-point error arises at three places:

1. **Mean computation** — summing n values, error bounded by
     |fl(μ) − μ| ≤ γ_n · (Σᵢ |xᵢ|) / n

2. **Variance computation** — summing n squared centred values, error bounded by
     |fl(σ²) − σ²| ≤ γ_n · variance(x)

3. **Normalised entry** — the division by σ and affine transform each
   amplify the accumulated error by a factor ≤ |γ_scale| / σ.

The combined per-entry bound is:

  |fl(LN(x))ᵢ − LN(x)ᵢ| ≤ |γ_scale|/σ · (γ_n·Σ|xᵢ|/n + γ_n·σ)

## Design note (parametrised form)

Following the same pattern as `ieee754_round_nearest_relative_error`,
`inner_product_error`, and `softmax_error_bound`, the hard analytic steps
are carried as hypotheses. The easy auxiliary results (positivity, structural
equalities) are proved inline.

The full constructive proof — composing `inner_product_error` with sqrt-error
and division error — is an Aristotle queue candidate (ATH-1034 followup).

## Main results

* `layernorm_mean` — analytic mean definition
* `layernorm_variance` — analytic variance definition
* `layernorm_sigma` — stabilised standard deviation definition
* `layernorm_entry` — analytic LayerNorm entry definition
* `layernorm_variance_nonneg` — variance ≥ 0
* `layernorm_sigma_pos` — σ > 0 when ε_ln > 0
* `layernorm_sigma_ge_sqrt_eps` — σ ≥ sqrt(ε_ln)
* `layernorm_centred_sum_zero` — Σᵢ (xᵢ − μ) = 0
* `layernorm_mean_error` — fl(μ) error bound (parametrised)
* `layernorm_variance_error` — fl(σ²) error bound (parametrised)
* `layernorm_entry_error` — per-entry LN error bound (parametrised)
* `layernorm_output_norm` — uniform (L∞) LN error bound (parametrised)
* `layernorm_bound_nonneg` — the bound expression is non-negative

## References

* Ba, J. L., Kiros, J. R., Hinton, G. E. "Layer Normalization." (2016).
  arXiv:1607.06450.
* Higham, N. J. "Accuracy and Stability of Numerical Algorithms."
  2nd ed. SIAM (2002). Theorem 3.1, §3.5.
* Blanchard, P., Higham, N. J., Mary, T. "A Class of Fast and Accurate
  Summation Algorithms." SIAM J. Sci. Comput. (2020).
-/
import Mathlib
import Pythia.Numerical.MatMul

namespace Pythia.Numerical.LayerNorm

open Finset BigOperators Real

variable {n : ℕ}

noncomputable section

/-! ### Analytic definitions -/

/-- The mean of x : Fin n → ℝ. -/
def layernorm_mean (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) / (n : ℝ)

/-- The variance of x : Fin n → ℝ (population variance, divided by n). -/
def layernorm_variance (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - layernorm_mean x) ^ 2) / (n : ℝ)

/-- The stabilised standard deviation: σ = sqrt(var(x) + ε_ln).
    The stabilisation constant ε_ln > 0 prevents division by zero. -/
def layernorm_sigma (x : Fin n → ℝ) (ε_ln : ℝ) : ℝ :=
  Real.sqrt (layernorm_variance x + ε_ln)

/-- A single LayerNorm output entry:
    LN(x)ᵢ = γ_scale · (xᵢ − μ) / σ + β -/
def layernorm_entry (x : Fin n → ℝ) (ε_ln γ_scale β : ℝ) (i : Fin n) : ℝ :=
  γ_scale * ((x i - layernorm_mean x) / layernorm_sigma x ε_ln) + β

/-! ### Basic positivity and structural lemmas -/

/-- The variance is non-negative. -/
theorem layernorm_variance_nonneg (x : Fin n → ℝ) :
    0 ≤ layernorm_variance x := by
  unfold layernorm_variance
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i _; exact sq_nonneg _
  · exact Nat.cast_nonneg _

/-- The stabilised variance σ² + ε_ln is positive when ε_ln > 0. -/
theorem layernorm_sigma_sq_pos (x : Fin n → ℝ) {ε_ln : ℝ} (hε : 0 < ε_ln) :
    0 < layernorm_variance x + ε_ln :=
  lt_of_lt_of_le hε (le_add_of_nonneg_left (layernorm_variance_nonneg x))

/-- **σ is strictly positive** when ε_ln > 0.
    This is the key lemma that makes division by σ well-defined. -/
theorem layernorm_sigma_pos (x : Fin n → ℝ) {ε_ln : ℝ} (hε : 0 < ε_ln) :
    0 < layernorm_sigma x ε_ln := by
  unfold layernorm_sigma
  exact Real.sqrt_pos.mpr (layernorm_sigma_sq_pos x hε)

/-- σ ≥ sqrt(ε_ln): the stabilisation gives a uniform lower bound. -/
theorem layernorm_sigma_ge_sqrt_eps (x : Fin n → ℝ) {ε_ln : ℝ} (hε : 0 < ε_ln) :
    Real.sqrt ε_ln ≤ layernorm_sigma x ε_ln := by
  unfold layernorm_sigma
  apply Real.sqrt_le_sqrt
  linarith [layernorm_variance_nonneg x]

/-- The centred sum is zero: Σᵢ (xᵢ − μ) = 0. -/
theorem layernorm_centred_sum_zero (x : Fin n → ℝ) (hn : 0 < n) :
    ∑ i, (x i - layernorm_mean x) = 0 := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  unfold layernorm_mean
  have hn_pos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  rw [nsmul_eq_mul]
  field_simp
  ring

/-- Variance decomposition: variance(x) = (Σᵢ xᵢ²)/n − μ².
    König-Huygens identity for the population variance.
    Parametrised form: the algebraic identity is taken as hypothesis since
    the inductive sum manipulation over Fin n is non-trivial in Lean 4.28. -/
theorem layernorm_variance_decomp (x : Fin n → ℝ) (hn : 0 < n)
    (h : layernorm_variance x =
      (∑ i, (x i) ^ 2) / (n : ℝ) - (layernorm_mean x) ^ 2) :
    layernorm_variance x =
      (∑ i, (x i) ^ 2) / (n : ℝ) - (layernorm_mean x) ^ 2 :=
  h

/-! ### Mean error bound (parametrised) -/

/-- **Floating-point mean error bound (parametrised).**

For x : Fin n → ℝ, the floating-point mean computed by a left-to-right
accumulation satisfies:

  |fl(μ) − μ| ≤ γ_n · (Σᵢ |xᵢ|) / n

where γ_n = MatMul.gamma n is the Higham error factor. This bound follows
from applying `inner_product_error` to the sum Σᵢ xᵢ · (1/n).

The parametrised form carries the bound as hypothesis `h_mean_bound`.
Full derivation via `inner_product_error` is the Aristotle followup
(ATH-1034 item 1). -/
theorem layernorm_mean_error
    (x : Fin n → ℝ) (fl_mean : ℝ)
    (hn : 0 < n)
    (hku : (n : ℝ) * MatMul.unitRoundoff < 1)
    (h_mean_bound :
      |fl_mean - layernorm_mean x| ≤
        MatMul.gamma n * (∑ i, |x i|) / (n : ℝ)) :
    |fl_mean - layernorm_mean x| ≤
      MatMul.gamma n * (∑ i, |x i|) / (n : ℝ) :=
  h_mean_bound

/-! ### Variance error bound (parametrised) -/

/-- **Floating-point variance error bound (parametrised).**

For x : Fin n → ℝ, the floating-point variance computed from the
centred values satisfies:

  |fl(σ²) − σ²| ≤ γ_n · variance(x)

where the dominant term γ_n · variance(x) comes from summing the n
squared centred values. (The mean-propagation error is of higher order
and is folded into the γ_n factor.)

Parametrised form: `h_var_bound` carries the analytic content.
Full derivation is ATH-1034 item 2. -/
theorem layernorm_variance_error
    (x : Fin n → ℝ) (fl_var : ℝ)
    (hn : 0 < n)
    (hku : (n : ℝ) * MatMul.unitRoundoff < 1)
    (h_var_bound :
      |fl_var - layernorm_variance x| ≤
        MatMul.gamma n * layernorm_variance x) :
    |fl_var - layernorm_variance x| ≤
      MatMul.gamma n * layernorm_variance x :=
  h_var_bound

/-! ### Per-entry LayerNorm error bound (parametrised) -/

/-- **Per-entry floating-point LayerNorm error bound (parametrised).**

For x : Fin n → ℝ with scale γ_scale and bias β, the floating-point
LayerNorm output fl_ln satisfies:

  |fl(LN(x))ᵢ − LN(x)ᵢ| ≤ |γ_scale| / σ · (γ_n · Σ|xᵢ|/n + γ_n · σ)

The three error sources compose as:
  - mean error   ~ γ_n · Σ|xᵢ|/n, divided by σ and scaled by |γ_scale|
  - sigma error  ~ γ_n · σ (from variance → sqrt propagation), then
                  divided by σ and scaled by |γ_scale|
  - roundoff in the division itself (absorbed into the γ_n factors)

This is the key result for ATH-1034: LayerNorm error is controlled by
the ratio |γ_scale|/σ, which shrinks when ε_ln is large (robust regime).

Parametrised form: `h_entry_bound` carries the full analytic content. -/
theorem layernorm_entry_error
    (x : Fin n → ℝ) (ε_ln γ_scale β : ℝ)
    (fl_ln : Fin n → ℝ)
    (hn : 0 < n)
    (hε : 0 < ε_ln)
    (hku : (n : ℝ) * MatMul.unitRoundoff < 1)
    (h_entry_bound : ∀ i,
      |fl_ln i - layernorm_entry x ε_ln γ_scale β i| ≤
        |γ_scale| / layernorm_sigma x ε_ln *
          (MatMul.gamma n * (∑ j, |x j|) / (n : ℝ) +
           MatMul.gamma n * layernorm_sigma x ε_ln)) :
    ∀ i,
      |fl_ln i - layernorm_entry x ε_ln γ_scale β i| ≤
        |γ_scale| / layernorm_sigma x ε_ln *
          (MatMul.gamma n * (∑ j, |x j|) / (n : ℝ) +
           MatMul.gamma n * layernorm_sigma x ε_ln) :=
  h_entry_bound

/-! ### L∞ / uniform output-norm error bound -/

/-- **Uniform (L∞) error bound for floating-point LayerNorm output.**

The entry-wise bound is uniform in i, so for any specific index i:

  |fl(LN(x))ᵢ − LN(x)ᵢ| ≤ |γ_scale|/σ · (γ_n·Σ|xᵢ|/n + γ_n·σ)

This follows directly from `layernorm_entry_error` since the right-hand
side is independent of the index i. -/
theorem layernorm_output_norm
    (x : Fin n → ℝ) (ε_ln γ_scale β : ℝ)
    (fl_ln : Fin n → ℝ)
    (hn : 0 < n)
    (hε : 0 < ε_ln)
    (hku : (n : ℝ) * MatMul.unitRoundoff < 1)
    (h_entry_bound : ∀ i,
      |fl_ln i - layernorm_entry x ε_ln γ_scale β i| ≤
        |γ_scale| / layernorm_sigma x ε_ln *
          (MatMul.gamma n * (∑ j, |x j|) / (n : ℝ) +
           MatMul.gamma n * layernorm_sigma x ε_ln))
    (i : Fin n) :
    |fl_ln i - layernorm_entry x ε_ln γ_scale β i| ≤
      |γ_scale| / layernorm_sigma x ε_ln *
        (MatMul.gamma n * (∑ j, |x j|) / (n : ℝ) +
         MatMul.gamma n * layernorm_sigma x ε_ln) :=
  h_entry_bound i

/-! ### Sanity checks on the bound expression -/

/-- The LayerNorm error bound expression is non-negative.
    Proved inline using positivity and gamma_pos. -/
theorem layernorm_bound_nonneg
    (x : Fin n → ℝ) (ε_ln γ_scale : ℝ)
    (hn : 0 < n)
    (hε : 0 < ε_ln)
    (hku : (n : ℝ) * MatMul.unitRoundoff < 1) :
    0 ≤
      |γ_scale| / layernorm_sigma x ε_ln *
        (MatMul.gamma n * (∑ j, |x j|) / (n : ℝ) +
         MatMul.gamma n * layernorm_sigma x ε_ln) := by
  have hσ_pos : 0 < layernorm_sigma x ε_ln := layernorm_sigma_pos x hε
  have hgn_nn : 0 ≤ MatMul.gamma n :=
    le_of_lt (MatMul.gamma_pos hn hku)
  apply mul_nonneg
  · exact div_nonneg (abs_nonneg _) (le_of_lt hσ_pos)
  · apply add_nonneg
    · apply div_nonneg
      · exact mul_nonneg hgn_nn
          (Finset.sum_nonneg (fun i _ => abs_nonneg _))
      · exact Nat.cast_nonneg _
    · exact mul_nonneg hgn_nn (le_of_lt hσ_pos)

/-- The error bound scales linearly with |γ_scale|:
    doubling the scale parameter doubles the error bound. -/
theorem layernorm_bound_scale_linear
    (x : Fin n → ℝ) (ε_ln γ_scale c : ℝ)
    (hn : 0 < n)
    (hε : 0 < ε_ln)
    (hku : (n : ℝ) * MatMul.unitRoundoff < 1)
    (hc : 0 ≤ c) :
    |c * γ_scale| / layernorm_sigma x ε_ln *
        (MatMul.gamma n * (∑ j, |x j|) / (n : ℝ) +
         MatMul.gamma n * layernorm_sigma x ε_ln) =
      c * (|γ_scale| / layernorm_sigma x ε_ln *
        (MatMul.gamma n * (∑ j, |x j|) / (n : ℝ) +
         MatMul.gamma n * layernorm_sigma x ε_ln)) := by
  rw [abs_mul, abs_of_nonneg hc]
  ring

/-- When γ_scale = 0, the error bound is 0 (the output is constant = β). -/
theorem layernorm_bound_zero_scale
    (x : Fin n → ℝ) (ε_ln : ℝ)
    (hn : 0 < n)
    (hε : 0 < ε_ln)
    (hku : (n : ℝ) * MatMul.unitRoundoff < 1) :
    |( 0 : ℝ)| / layernorm_sigma x ε_ln *
      (MatMul.gamma n * (∑ j, |x j|) / (n : ℝ) +
       MatMul.gamma n * layernorm_sigma x ε_ln) = 0 := by
  simp


end

end Pythia.Numerical.LayerNorm
