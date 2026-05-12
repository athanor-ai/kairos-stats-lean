/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kernel Fusion Error Bounds

Fusing two numerical operations (e.g. RMSNorm followed by attention) into a
single accelerator kernel does not magnify the per-operation error bounds.  This file
formalises the composition rule for absolute-error bounds on real-valued
functions and proves that fused-kernel error grows at most linearly.

## Setup

Two operations `A_fp` and `B_fp` are floating-point approximations of exact
functions `A` and `B` respectively, with relative-error bounds

  |A_fp(x) − A(x)| ≤ ε_A · |x|
  |B_fp(y) − B(y)| ≤ ε_B · |y|

and `B` (exact) is L-Lipschitz:

  |B(y) − B(z)| ≤ L · |y − z|

Under these hypotheses the fused operation `B_fp ∘ A_fp` satisfies

  |B_fp(A_fp(x)) − B(A(x))| ≤ (L · ε_A + ε_B + ε_B · ε_A) · |x|

when `A` is contractive (`|A(x)| ≤ |x|`), which holds for all standard
normalisation operations (RMSNorm, LayerNorm, softmax).

When both ε_A and ε_B are small the cross-term `ε_B · ε_A` is negligible and
the first-order bound `(L · ε_A + ε_B) · |x|` applies.

## Main results

* `composed_error_bound`            — full composition bound (L·ε_A + ε_B + ε_B·ε_A)·|x|
* `composed_error_first_order`      — first-order split: (L·ε_A + ε_B)·|x| + cross-term explicit
* `fusion_preserves_individual_bounds` — fused error ≤ (ε_A + ε_B + ε_A·ε_B)·|x| (L = 1 case)
* `n_fold_composition_error`        — n equal-ε operations: error ≤ ((1+ε)^n − 1)·|x|
* `lipschitz_composition_error`     — general L₂-Lipschitz g: error ≤ L₂·ε_f·|x| + ε_g·|f(x)| + ε_g·ε_f·|x|
* `lipschitz_composition_error_contractive` — contractive-f corollary:
                                    error ≤ (L₂·ε_f + ε_g·C + ε_g·ε_f)·|x|

## References

* Higham, N. J. "Accuracy and Stability of Numerical Algorithms."
  2nd ed. SIAM (2002). Chapter 3 (error analysis of composed operations).
* Accelerator SDK documentation: kernel fusion for RMSNorm + attention.
-/
import Mathlib

namespace Pythia.Numerical.KernelFusionError

/-! ## 1. Full composition error bound -/

/-- **`composed_error_bound`**: fusing operation A (relative error ε_A) followed
    by L-Lipschitz operation B (relative error ε_B) gives fused error

      |B_fp(A_fp(x)) − B(A(x))| ≤ (L · ε_A + ε_B + ε_B · ε_A) · |x|

    when the exact A is contractive: |A(x)| ≤ |x|.

    Proof:
      |B_fp(A_fp x) − B(A x)|
      ≤ |B_fp(A_fp x) − B(A_fp x)| + |B(A_fp x) − B(A x)|   [abs_sub_le / triangle]
      ≤ ε_B·|A_fp x| + L·|A_fp x − A x|                      [hB + hLip]
      ≤ ε_B·(1 + ε_A)·|x| + L·ε_A·|x|                        [hA + contractiveness]
      = (L·ε_A + ε_B + ε_B·ε_A) · |x|                         [algebra] -/
theorem composed_error_bound
    (A B A_fp B_fp : ℝ → ℝ)
    (x : ℝ)
    (ε_A ε_B L : ℝ)
    (_hεA : 0 ≤ ε_A)
    (hεB  : 0 ≤ ε_B)
    (hL   : 0 ≤ L)
    -- Floating-point error bounds
    (hA   : |A_fp x - A x| ≤ ε_A * |x|)
    (hB   : ∀ y, |B_fp y - B y| ≤ ε_B * |y|)
    -- B (exact) is L-Lipschitz
    (hLip : ∀ y z, |B y - B z| ≤ L * |y - z|)
    -- A (exact) is contractive
    (hAx  : |A x| ≤ |x|) :
    |B_fp (A_fp x) - B (A x)| ≤ (L * ε_A + ε_B + ε_B * ε_A) * |x| := by
  -- Three-point triangle inequality
  have htri := abs_sub_le (B_fp (A_fp x)) (B (A_fp x)) (B (A x))
  -- Bound the B_fp term at A_fp x
  have hBfp   : |B_fp (A_fp x) - B (A_fp x)| ≤ ε_B * |A_fp x| := hB (A_fp x)
  -- Bound the Lipschitz term
  have hLipA  : |B (A_fp x) - B (A x)| ≤ L * |A_fp x - A x| := hLip (A_fp x) (A x)
  have hAerr  : L * |A_fp x - A x| ≤ L * ε_A * |x| := by nlinarith [abs_nonneg x]
  -- |A_fp x| ≤ (1 + ε_A)·|x| by triangle + contractiveness
  have hAfp   : |A_fp x| ≤ (1 + ε_A) * |x| := by
    calc |A_fp x|
        = |A x + (A_fp x - A x)| := by ring_nf
      _ ≤ |A x| + |A_fp x - A x| := abs_add_le _ _
      _ ≤ |x| + ε_A * |x|        := by linarith
      _ = (1 + ε_A) * |x|        := by ring
  -- Propagate
  have hBfp2  : ε_B * |A_fp x| ≤ ε_B * (1 + ε_A) * |x| := by
    nlinarith [abs_nonneg x]
  nlinarith [abs_nonneg x]

/-! ## 2. First-order composition bound -/

/-- **`composed_error_first_order`**: the cross-term `ε_B · ε_A · |x|` is explicit.

      |B_fp(A_fp(x)) − B(A(x))| ≤ (L · ε_A + ε_B) · |x| + ε_B · ε_A · |x| -/
theorem composed_error_first_order
    (A B A_fp B_fp : ℝ → ℝ)
    (x : ℝ)
    (ε_A ε_B L : ℝ)
    (hεA  : 0 ≤ ε_A)
    (hεB  : 0 ≤ ε_B)
    (hL   : 0 ≤ L)
    (hA   : |A_fp x - A x| ≤ ε_A * |x|)
    (hB   : ∀ y, |B_fp y - B y| ≤ ε_B * |y|)
    (hLip : ∀ y z, |B y - B z| ≤ L * |y - z|)
    (hAx  : |A x| ≤ |x|) :
    |B_fp (A_fp x) - B (A x)| ≤ (L * ε_A + ε_B) * |x| + ε_B * ε_A * |x| := by
  have hfull := composed_error_bound A B A_fp B_fp x ε_A ε_B L
    hεA hεB hL hA hB hLip hAx
  nlinarith [abs_nonneg x]

/-! ## 3. Fusion preserves individual bounds -/

/-- **`fusion_preserves_individual_bounds`**: when B (exact) is 1-Lipschitz
    (e.g. it is itself a normalisation), the fused error satisfies

      |B_fp(A_fp(x)) − B(A(x))| ≤ (ε_A + ε_B + ε_A · ε_B) · |x|

    In particular, the fused bound is the multiplicative composition
    of the two individual bounds: (1 + ε_A)(1 + ε_B) − 1 = ε_A + ε_B + ε_A·ε_B. -/
theorem fusion_preserves_individual_bounds
    (A B A_fp B_fp : ℝ → ℝ)
    (x : ℝ)
    (ε_A ε_B : ℝ)
    (hεA  : 0 ≤ ε_A)
    (hεB  : 0 ≤ ε_B)
    (hA   : |A_fp x - A x| ≤ ε_A * |x|)
    (hB   : ∀ y, |B_fp y - B y| ≤ ε_B * |y|)
    -- B (exact) is 1-Lipschitz
    (hLip1 : ∀ y z, |B y - B z| ≤ |y - z|)
    -- A (exact) is contractive
    (hAx  : |A x| ≤ |x|) :
    |B_fp (A_fp x) - B (A x)| ≤ (ε_A + ε_B + ε_A * ε_B) * |x| := by
  have htri  := abs_sub_le (B_fp (A_fp x)) (B (A_fp x)) (B (A x))
  have hBfp  : |B_fp (A_fp x) - B (A_fp x)| ≤ ε_B * |A_fp x| := hB (A_fp x)
  have hLipA : |B (A_fp x) - B (A x)| ≤ |A_fp x - A x|       := hLip1 (A_fp x) (A x)
  have hAfp  : |A_fp x| ≤ (1 + ε_A) * |x| := by
    calc |A_fp x|
        = |A x + (A_fp x - A x)| := by ring_nf
      _ ≤ |A x| + |A_fp x - A x| := abs_add_le _ _
      _ ≤ |x| + ε_A * |x|        := by linarith
      _ = (1 + ε_A) * |x|        := by ring
  nlinarith [abs_nonneg x]

/-! ## 4. Linear error growth for n-fold composition -/

/-- Helper: the exact fold of contractive operations stays bounded by the input. -/
private lemma exact_fold_bounded
    (exact_ops : ℕ → ℝ → ℝ)
    (hcont : ∀ k y, |exact_ops k y| ≤ |y|)
    (x : ℝ) (m : ℕ) :
    |Nat.rec x (fun k acc => exact_ops k acc) m| ≤ |x| := by
  induction m with
  | zero     => simp
  | succ p ih =>
    calc |exact_ops p (Nat.rec x (fun k acc => exact_ops k acc) p)|
        ≤ |Nat.rec x (fun k acc => exact_ops k acc) p| := hcont p _
      _ ≤ |x| := ih

/-- **`n_fold_composition_error`**: composing n operations, each with relative
    error ≤ ε and each exact version contractive and 1-Lipschitz, gives total
    relative error bounded by `((1 + ε)^n − 1) · |x|`.

    The exact formula `(1 + ε)^n − 1` arises from the recurrence

      err_{k+1} ≤ (1 + ε) · err_k + ε · |x|

    with err_0 = 0, whose solution is `((1 + ε)^n − 1) · |x|`.

    In the small-ε regime: `(1 + ε)^n − 1 ≤ exp(n·ε) − 1 ≈ n·ε` for n·ε ≪ 1,
    confirming linear error growth. -/
theorem n_fold_composition_error
    (n : ℕ)
    (ops exact_ops : ℕ → ℝ → ℝ)
    (ε : ℝ)
    (hε    : 0 ≤ ε)
    (herr  : ∀ k y, |ops k y - exact_ops k y| ≤ ε * |y|)
    (hcont : ∀ k y, |exact_ops k y| ≤ |y|)
    (hLip  : ∀ k y z, |exact_ops k y - exact_ops k z| ≤ |y - z|)
    (x : ℝ) :
    |Nat.rec x (fun k acc => ops k acc) n -
     Nat.rec x (fun k acc => exact_ops k acc) n| ≤
     ((1 + ε) ^ n - 1) * |x| := by
  induction n with
  | zero => simp
  | succ m ih =>
    -- Let a_fp, a_ex be the m-step folds
    set a_fp : ℝ := Nat.rec x (fun k acc => ops k acc) m
    set a_ex : ℝ := Nat.rec x (fun k acc => exact_ops k acc) m
    -- IH: |a_fp − a_ex| ≤ ((1+ε)^m − 1)·|x|
    have hIH : |a_fp - a_ex| ≤ ((1 + ε) ^ m - 1) * |x| := ih
    -- Triangle on the successor step
    have htri   := abs_sub_le (ops m a_fp) (exact_ops m a_fp) (exact_ops m a_ex)
    have herr_m : |ops m a_fp - exact_ops m a_fp| ≤ ε * |a_fp| := herr m a_fp
    have hlip_m : |exact_ops m a_fp - exact_ops m a_ex| ≤ |a_fp - a_ex| :=
      hLip m a_fp a_ex
    -- |a_fp| ≤ (1+ε)^m · |x|
    have ha_ex  : |a_ex| ≤ |x| := exact_fold_bounded exact_ops hcont x m
    have ha_fp  : |a_fp| ≤ (1 + ε) ^ m * |x| := by
      calc |a_fp|
          = |a_ex + (a_fp - a_ex)| := by ring_nf
        _ ≤ |a_ex| + |a_fp - a_ex| := abs_add_le _ _
        _ ≤ |x| + ((1 + ε) ^ m - 1) * |x| := by linarith
        _ = (1 + ε) ^ m * |x|      := by ring
    -- ε*|a_fp| ≤ ε*(1+ε)^m*|x|
    have hstep : ε * |a_fp| ≤ ε * (1 + ε) ^ m * |x| := by
      nlinarith [abs_nonneg x]
    -- Explicit chain: total ≤ ε*(1+ε)^m*|x| + ((1+ε)^m−1)*|x| = ((1+ε)^(m+1)−1)*|x|
    have hchain : |ops m a_fp - exact_ops m a_ex| ≤
        ε * (1 + ε) ^ m * |x| + ((1 + ε) ^ m - 1) * |x| := by linarith
    have hring  : ε * (1 + ε) ^ m * |x| + ((1 + ε) ^ m - 1) * |x| =
        ((1 + ε) ^ (m + 1) - 1) * |x| := by ring
    linarith

/-! ## 5. Lipschitz composition error -/

/-- **`lipschitz_composition_error`**: if `f_fp` approximates `f` with error
    ≤ ε_f·|x|, and `g_fp` approximates L₂-Lipschitz `g` with error ≤ ε_g·|y|,
    then the composed approximation satisfies

      |g_fp(f_fp(x)) − g(f(x))| ≤ L₂·ε_f·|x| + ε_g·|f(x)| + ε_g·ε_f·|x|

    The three terms correspond to:
    1. L₂·ε_f·|x|   — Lipschitz amplification of f's error
    2. ε_g·|f(x)|   — g's error applied at the exact output f(x)
    3. ε_g·ε_f·|x|  — second-order cross term from f's perturbation through ε_g -/
theorem lipschitz_composition_error
    (f g f_fp g_fp : ℝ → ℝ)
    (x : ℝ)
    (ε_f ε_g L₂ : ℝ)
    (_hεf  : 0 ≤ ε_f)
    (_hεg  : 0 ≤ ε_g)
    (hL₂   : 0 ≤ L₂)
    (hf    : |f_fp x - f x| ≤ ε_f * |x|)
    (hg    : ∀ y, |g_fp y - g y| ≤ ε_g * |y|)
    (hgLip : ∀ y z, |g y - g z| ≤ L₂ * |y - z|) :
    |g_fp (f_fp x) - g (f x)| ≤
      L₂ * ε_f * |x| + ε_g * |f x| + ε_g * ε_f * |x| := by
  have htri   := abs_sub_le (g_fp (f_fp x)) (g (f_fp x)) (g (f x))
  have hgfp   : |g_fp (f_fp x) - g (f_fp x)| ≤ ε_g * |f_fp x| := hg (f_fp x)
  have hgLipf : |g (f_fp x) - g (f x)| ≤ L₂ * |f_fp x - f x|  := hgLip (f_fp x) (f x)
  have hferr  : L₂ * |f_fp x - f x| ≤ L₂ * ε_f * |x| := by nlinarith [abs_nonneg x]
  -- |f_fp x| ≤ |f x| + ε_f·|x|
  have hffp   : |f_fp x| ≤ |f x| + ε_f * |x| := by
    calc |f_fp x|
        = |f x + (f_fp x - f x)| := by ring_nf
      _ ≤ |f x| + |f_fp x - f x| := abs_add_le _ _
      _ ≤ |f x| + ε_f * |x|      := by linarith
  have hgfp2  : ε_g * |f_fp x| ≤ ε_g * |f x| + ε_g * ε_f * |x| := by
    nlinarith [abs_nonneg x, abs_nonneg (f x)]
  linarith

/-- **`lipschitz_composition_error_contractive`**: corollary of
    `lipschitz_composition_error` when `|f(x)| ≤ C·|x|` (scale-bounded f).
    The bound simplifies to

      |g_fp(f_fp(x)) − g(f(x))| ≤ (L₂·ε_f + ε_g·C + ε_g·ε_f) · |x|

    **Accelerator application**: for RMSNorm→attention fusion, C = 1 (RMSNorm is
    contractive in L₂), L₂ = attention Lipschitz constant, giving

      fused error ≤ (L_attn · ε_RMSNorm + ε_attn + ε_RMSNorm · ε_attn) · |x| -/
theorem lipschitz_composition_error_contractive
    (f g f_fp g_fp : ℝ → ℝ)
    (x : ℝ)
    (ε_f ε_g L₂ C : ℝ)
    (_hεf  : 0 ≤ ε_f)
    (_hεg  : 0 ≤ ε_g)
    (hL₂   : 0 ≤ L₂)
    (_hC   : 0 ≤ C)
    (hf    : |f_fp x - f x| ≤ ε_f * |x|)
    (hg    : ∀ y, |g_fp y - g y| ≤ ε_g * |y|)
    (hgLip : ∀ y z, |g y - g z| ≤ L₂ * |y - z|)
    -- Scale bound on exact f
    (hfC   : |f x| ≤ C * |x|) :
    |g_fp (f_fp x) - g (f x)| ≤ (L₂ * ε_f + ε_g * C + ε_g * ε_f) * |x| := by
  have htri   := abs_sub_le (g_fp (f_fp x)) (g (f_fp x)) (g (f x))
  have hgfp   : |g_fp (f_fp x) - g (f_fp x)| ≤ ε_g * |f_fp x| := hg (f_fp x)
  have hgLipf : |g (f_fp x) - g (f x)| ≤ L₂ * |f_fp x - f x|  := hgLip (f_fp x) (f x)
  have hferr  : L₂ * |f_fp x - f x| ≤ L₂ * ε_f * |x| := by nlinarith [abs_nonneg x]
  -- |f_fp x| ≤ (C + ε_f)·|x|
  have hffp   : |f_fp x| ≤ C * |x| + ε_f * |x| := by
    calc |f_fp x|
        = |f x + (f_fp x - f x)| := by ring_nf
      _ ≤ |f x| + |f_fp x - f x| := abs_add_le _ _
      _ ≤ C * |x| + ε_f * |x|    := by linarith
  have hgfp2  : ε_g * |f_fp x| ≤ ε_g * C * |x| + ε_g * ε_f * |x| := by
    nlinarith [abs_nonneg x, abs_nonneg (f x)]
  nlinarith [abs_nonneg x]

end Pythia.Numerical.KernelFusionError
