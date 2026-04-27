/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Shannon Binary Entropy Non-negativity

The binary entropy function is defined as
`H(p) = -p * log p - (1-p) * log(1-p)` for `p` in `[0, 1]`,
with the convention `0 * log 0 = 0` (handled by `Real.negMulLog`).

## Main results

* `binaryEntropy`           : the function `H(p) = negMulLog p + negMulLog (1 - p)`
* `binary_entropy_nonneg`   : `H(p) >= 0` for all `p` in `[0, 1]`

## Why this lemma

Mathlib has `Real.negMulLog` and `Real.negMulLog_nonneg` as primitives but
no named `binary_entropy_nonneg` declaration. Pythia exposes the binary
entropy function and its non-negativity so the `pythia` tactic cascade can
close information-theoretic goals without the user unpacking the two-term sum.

The companion empirical layer (`tools/sim/info_theory_binary_entropy.py`)
runs a 10 000-trial PBT, a deterministic sweep over `[0, 1]`, and a mutation
harness so the bound can be verified numerically across the entire domain
including the boundary conventions at `p = 0` and `p = 1`.

## References

* Shannon, C.E. "A Mathematical Theory of Communication."
  Bell System Technical Journal 27(3): 379-423 (1948).
* Cover, T.M. and Thomas, J.A. "Elements of Information Theory,"
  2nd ed. Wiley (2006), Section 2.1.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.InfoTheory

/-- The Shannon binary entropy function `H(p) = -p * log p - (1-p) * log(1-p)`.
The argument is an unconstrained real; the meaningful domain is `[0, 1]`.
The boundary convention `0 * log 0 = 0` is inherited from `Real.negMulLog`. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ := Real.negMulLog p + Real.negMulLog (1 - p)

/-- **Shannon binary entropy non-negativity.** For any `p` in `[0, 1]`,
the binary entropy `H(p) = -p * log p - (1-p) * log(1-p)` is non-negative.
Each term is non-negative by `Real.negMulLog_nonneg`, and the sum inherits
the bound by `linarith`. -/
@[stat_lemma]
theorem binary_entropy_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ binaryEntropy p := by
  unfold binaryEntropy
  have hpos1 : 0 ≤ Real.negMulLog p := Real.negMulLog_nonneg h0 h1
  have h1p : (0 : ℝ) ≤ 1 - p := by linarith
  have h1p_le : (1 - p : ℝ) ≤ 1 := by linarith
  have hpos2 : 0 ≤ Real.negMulLog (1 - p) := Real.negMulLog_nonneg h1p h1p_le
  linarith

end Pythia.InfoTheory
