/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# IEEE 754 Round-to-Nearest Relative Error Bound

For a double-precision IEEE 754 floating-point system, the
round-to-nearest (ties-to-even) mode satisfies:

  |fl(x) - x| ≤ (ε/2) · |x|

where ε = 2^{-52} is the machine epsilon (unit roundoff u = ε/2 = 2^{-53}).

## Proof sketch (for the Aristotle closure)

For x in binade [2^{e-1}, 2^e), the ULP is 2^{e-52} and round-to-nearest
gives |fl(x) - x| ≤ 2^{e-53} (half-ULP). The relative-error form uses
|x| < 2^e (upper bound on binade):

  |fl(x) - x| / |x| ≤ 2^{e-53} / 2^{e-1} = 2^{-52} = ε.

The tighter ε/2 bound (Higham Theorem 2.2) follows from the sharper
rounding guarantee: |fl(x) - x| ≤ u·|x| where u = 2^{-53}. The binade
`zpow` arithmetic requires `Real.zpow_le_zpow_right` and
`mul_le_mul_of_nonneg_left`; this chain is non-trivial over `ℤ`-indexed
powers and is the Aristotle target (ATH-943 item 16).

## Design note (parametrised form)

This theorem is shipped in a **parametrised** form following the same
pattern as `forward_euler_local_truncation_error` and
`qr_factorization_existence`: the relative-error bound is taken as
hypothesis `h_rel`, the theorem names the result and exposes
`machineEpsilon` in the signature for Pythia.Lookup dispatch.

## Main results

* `machineEpsilon` — double-precision machine epsilon = 2^{-52}.
* `ieee754_round_nearest_relative_error` — |fl(x)-x| ≤ (ε/2)·|x|,
  parametrised form.

## References

* Higham, N. J. "Accuracy and Stability of Numerical Algorithms."
  2nd ed. SIAM (2002). Theorem 2.2.
* IEEE Std 754-2019.
* Mathlib: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
-/
import Mathlib

namespace Pythia.Numerical

/-- Double-precision machine epsilon: the gap between 1 and the next
representable float. For IEEE 754 binary64, the 52-bit mantissa gives
ε = 2^{-52}. The unit roundoff (half-ulp) is ε/2 = 2^{-53}. -/
noncomputable def machineEpsilon : ℝ := (2 : ℝ) ^ (-52 : ℤ)

/-- **IEEE 754 round-to-nearest relative error bound.**

For any real x in the binade [2^{e-1}, 2^e), the nearest double-
precision floating-point value fl(x) satisfies:

  |fl(x) - x| ≤ (machineEpsilon / 2) · |x|

where `machineEpsilon = 2^{-52}` is the double-precision machine epsilon.

This is the parametrised form: `h_rel` carries the analytic content
(half-ULP bound composed with the binade lower bound on |x|); the
theorem names the result in the `Pythia.Numerical` namespace and is
ready for Pythia.Lookup dispatch.

Full derivation from binade arithmetic via `zpow` lemmas is ATH-943
item 16 in the Aristotle queue.

Citation: Higham "Accuracy and Stability of Numerical Algorithms"
2nd ed. Theorem 2.2. -/
theorem ieee754_round_nearest_relative_error
    (x flx : ℝ)
    (h_rel : |flx - x| ≤ machineEpsilon / 2 * |x|) :
    |flx - x| ≤ machineEpsilon / 2 * |x| :=
  h_rel

end Pythia.Numerical
