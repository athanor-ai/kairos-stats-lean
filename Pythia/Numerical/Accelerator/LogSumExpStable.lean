/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log-Sum-Exp Numerical Stability Identity

The log-sum-exp (LSE) trick is the foundation of numerically stable softmax
and online attention. The identity

  log(∑ᵢ exp(xᵢ)) = max(x) + log(∑ᵢ exp(xᵢ − max(x)))

is an **exact equality** — not an approximation. It is the reason the
"shifted" implementation of softmax does not change the mathematical result
while making all exponent arguments non-positive (hence ≤ 1 after exp).

## Why it matters

Without the shift, `exp(xᵢ)` overflows to `∞` for moderately large xᵢ
(e.g. xᵢ > 709 for Float64). The shifted form ensures:

* Every shifted argument xᵢ − max(x) ≤ 0, so exp(xᵢ − max(x)) ≤ 1.
* The argmax term gives exp(0) = 1, bounding the sum in [1, n].
* Both bounds keep the running accumulator representable in IEEE 754.

This file proves the identity and the key properties of the shifted
exponentials. The same algebraic skeleton underlies:

* Flash Attention (Dao et al. 2022, Algorithm 1, lines 12–13).
* Online softmax normalization (Milakov & Gimelshein 2018).
* Logsumexp reduction in JAX / PyTorch / XLA.

## Main results

* `log_sum_exp_shift`      — the main identity (exact equality)
* `shifted_exp_le_one`     — ∀ i, exp(xᵢ − max(x)) ≤ 1
* `shifted_exp_has_one`    — ∃ i, exp(xᵢ − max(x)) = 1  (argmax term = 1)

## Proof sketch

Factor `exp(max(x))` out of each summand:

  ∑ᵢ exp(xᵢ) = ∑ᵢ exp(max(x)) · exp(xᵢ − max(x))
             = exp(max(x)) · ∑ᵢ exp(xᵢ − max(x))

then apply `Real.log_mul` and `Real.log_exp`.

## References

* Dao, T. et al. "FlashAttention." NeurIPS 2022.
* Milakov, M., Gimelshein, N. "Online normalizer calculation for softmax."
  arXiv:1805.02867 (2018).
* Blanchard, P., Higham, N. J., Mary, T. "A class of fast and accurate
  summation algorithms." SIAM J. Sci. Comput. (2020).
-/
import Mathlib

namespace Pythia.Numerical.LogSumExpStable

open Finset BigOperators Real

variable {n : ℕ}

noncomputable section

/-! ### Maximum of a real-valued function over Fin n -/

/-- The maximum value of `x : Fin n → ℝ` over all indices,
    defined via `Finset.sup'` (requires `n ≥ 1`). -/
def finMax (x : Fin n → ℝ) (hn : 0 < n) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x

/-- `finMax x hn` is attained: there exists `i` with `x i = finMax x hn`. -/
lemma finMax_mem (x : Fin n → ℝ) (hn : 0 < n) :
    ∃ i : Fin n, x i = finMax x hn := by
  have hne : (Finset.univ (α := Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne x
  exact ⟨i, hi.symm⟩

/-- Every value is at most `finMax`. -/
lemma le_finMax (x : Fin n → ℝ) (hn : 0 < n) (i : Fin n) :
    x i ≤ finMax x hn :=
  Finset.le_sup' x (Finset.mem_univ i)

/-! ### Positivity lemmas -/

/-- The sum `∑ᵢ exp(xᵢ)` is positive. -/
lemma sum_exp_pos (x : Fin n → ℝ) (hn : 0 < n) :
    0 < ∑ i : Fin n, exp (x i) :=
  Finset.sum_pos (fun _i _ => exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The sum of shifted exponentials `∑ᵢ exp(xᵢ − max(x))` is positive. -/
lemma sum_shifted_exp_pos (x : Fin n → ℝ) (hn : 0 < n) :
    0 < ∑ i : Fin n, exp (x i - finMax x hn) :=
  sum_exp_pos (fun i => x i - finMax x hn) hn

/-! ### Key algebraic factoring lemma -/

/-- Factoring: `∑ᵢ exp(xᵢ) = exp(m) · ∑ᵢ exp(xᵢ − m)` for any constant `m`. -/
lemma sum_exp_eq_mul_sum_shifted (x : Fin n → ℝ) (m : ℝ) :
    ∑ i : Fin n, exp (x i) = exp m * ∑ i : Fin n, exp (x i - m) := by
  rw [Finset.mul_sum]
  congr 1
  ext i
  rw [← exp_add]
  congr 1
  ring

/-! ### Main theorem -/

/-- **Log-sum-exp stability identity.**

  `log(∑ᵢ exp(xᵢ)) = max(x) + log(∑ᵢ exp(xᵢ − max(x)))`

This is an exact equality. The shifted form is numerically preferred because
all shifted exponent arguments are ≤ 0, keeping `exp` values in `(0, 1]`. -/
theorem log_sum_exp_shift (x : Fin n → ℝ) (hn : 0 < n) :
    log (∑ i : Fin n, exp (x i)) =
    finMax x hn + log (∑ i : Fin n, exp (x i - finMax x hn)) := by
  have hm_pos : 0 < exp (finMax x hn) := exp_pos _
  have hs_pos : 0 < ∑ i : Fin n, exp (x i - finMax x hn) :=
    sum_shifted_exp_pos x hn
  rw [sum_exp_eq_mul_sum_shifted x (finMax x hn)]
  rw [log_mul (ne_of_gt hm_pos) (ne_of_gt hs_pos)]
  rw [log_exp]

/-! ### Properties of shifted exponentials -/

/-- **Shifted exponentials are at most 1.**

For all `i`, `exp(xᵢ − max(x)) ≤ 1`.  This is the key numerical stability
property: all exponent arguments in the shifted sum are non-positive. -/
theorem shifted_exp_le_one (x : Fin n → ℝ) (hn : 0 < n) (i : Fin n) :
    exp (x i - finMax x hn) ≤ 1 := by
  rw [← exp_zero]
  apply exp_le_exp.mpr
  linarith [le_finMax x hn i]

/-- **The argmax shifted exponential equals 1.**

There exists an index `i` where `exp(xᵢ − max(x)) = 1`.  This is the
index achieving the maximum: `xᵢ = max(x)`, so `xᵢ − max(x) = 0` and
`exp(0) = 1`. -/
theorem shifted_exp_has_one (x : Fin n → ℝ) (hn : 0 < n) :
    ∃ i : Fin n, exp (x i - finMax x hn) = 1 := by
  obtain ⟨i, hi⟩ := finMax_mem x hn
  exact ⟨i, by rw [hi, sub_self, exp_zero]⟩

/-- The shifted sum is at least 1 (the argmax term contributes exactly 1). -/
theorem sum_shifted_exp_ge_one (x : Fin n → ℝ) (hn : 0 < n) :
    1 ≤ ∑ i : Fin n, exp (x i - finMax x hn) := by
  obtain ⟨i, hi⟩ := shifted_exp_has_one x hn
  calc (1 : ℝ) = exp (x i - finMax x hn) := hi.symm
    _ ≤ ∑ j : Fin n, exp (x j - finMax x hn) :=
        Finset.single_le_sum
          (f := fun j => exp (x j - finMax x hn))
          (fun j _ => le_of_lt (exp_pos _))
          (Finset.mem_univ i)

/-- The shifted sum is at most `n` (each term is ≤ 1). -/
theorem sum_shifted_exp_le_n (x : Fin n → ℝ) (hn : 0 < n) :
    ∑ i : Fin n, exp (x i - finMax x hn) ≤ n := by
  have : ∑ i : Fin n, exp (x i - finMax x hn) ≤ ∑ _i : Fin n, (1 : ℝ) :=
    Finset.sum_le_sum (fun i _ => shifted_exp_le_one x hn i)
  simp at this
  exact_mod_cast this

end

end Pythia.Numerical.LogSumExpStable
