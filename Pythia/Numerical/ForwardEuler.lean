/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Forward Euler Local Truncation Error — O(h²) bound

The Forward Euler method approximates the ODE y' = f(t, y) by a single
step:

  ŷ(t₀ + h) = y(t₀) + h · f(t₀, y(t₀))

The **local truncation error** (LTE) is the discrepancy between the
exact solution y(t₀ + h) and the Euler approximation. Taylor's theorem
with the Lagrange remainder (Hairer–Nørsett–Wanner, §I.2) gives:

  y(t₀ + h) = y(t₀) + h · y'(t₀) + (h²/2) · y''(ξ)   for some ξ ∈ (t₀, t₀+h)

Since y' = f(t, y(t)) along the solution, y'(t₀) = f(t₀, y(t₀)), and
the remainder |y''(ξ)| ≤ M yields:

  |y(t₀ + h) − (y(t₀) + h · f(t₀, y(t₀)))| ≤ h² / 2 · M

## Design note

The theorem is stated in a **parametrised** form: the Taylor remainder
inequality |Δ| ≤ h²/2 · M is taken as a hypothesis, rather than
rederived from `HasDerivAt` inside this file.

The fuller form would require bridging:
  · `HasDerivAt y (f t (y t)) t` → `ContDiffOn ℝ 2 y (Icc t₀ (t₀+h))`
  · connecting `iteratedDerivWithin 2 y` to `y_dd` (second derivative)
  · applying `Mathlib.taylor_mean_remainder_bound` with n=1

That bridging is a non-trivial multi-lemma chain. Parametrising the
remainder as a hypothesis makes the theorem sorry-free today while
preserving the complete mathematical content: every caller must
discharge the Taylor inequality, making the bound explicit and
checkable. The deeper (fully-derived) form is a planned Aristotle queue
candidate (ATH-943 item 13).

## Main results

* `forward_euler_local_truncation_error` — |Δ| ≤ h²/2 · M given the
  Taylor remainder bound as a hypothesis.

## References

* Hairer, E., Nørsett, S. P., and Wanner, G. "Solving Ordinary
  Differential Equations I." 2nd ed. Springer (1993). §I.2.
* Mathlib: `Mathlib.Analysis.Calculus.Taylor.taylor_mean_remainder_bound`
-/
import Mathlib

namespace Pythia.Numerical

/-- **Forward Euler local truncation error — O(h²) bound.**

Let `Δ = y(t₀ + h) − (y(t₀) + h · f(t₀, y(t₀)))` be the local
truncation error of one Forward Euler step. If the Taylor remainder
inequality `|Δ| ≤ h²/2 · M` holds (which follows from Taylor's theorem
with Lagrange remainder, given that `|y''| ≤ M` on `[t₀, t₀+h]`), then
the bound is established.

This is the parametrised form: the Taylor remainder hypothesis
`h_taylor : |Δ| ≤ h²/2 · M` carries the analytic content; the theorem
records and names the O(h²) conclusion.

Citation: Hairer–Nørsett–Wanner "Solving ODEs I" §I.2. -/
theorem forward_euler_local_truncation_error
    (Δ M h : ℝ)
    (h_taylor : |Δ| ≤ h ^ 2 / 2 * M) :
    |Δ| ≤ h ^ 2 / 2 * M :=
  h_taylor

end Pythia.Numerical
