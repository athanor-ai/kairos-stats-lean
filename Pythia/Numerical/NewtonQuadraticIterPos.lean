/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Newton iteration on f(x)=x^2-c keeps positive iterates: (x + c/x)/2 > 0 when x > 0 and c > 0.

Newton iteration on f(x)=x^2-c keeps positive iterates: (x + c/x)/2 > 0 when x > 0 and c > 0.

## Main results

* `newton_quadratic_iter_pos` — Newton iteration on f(x)=x^2-c keeps positive iterates: (x + c/x)/2 > 0 when x > 0 and c > 0.

## References

    * Newton, I. De analysi per aequationes numero terminorum infinitas (1669)
-/
import Mathlib
import Pythia.Tactic.Pythia


namespace Pythia.Numerical


/-- **Newton iteration positivity for `f(x) = x² - c`.** The Newton
iterate `x_{n+1} = (x_n + c / x_n) / 2` for `f(x) = x² - c` (the
classical "Babylonian" / Heron square-root iteration) remains
positive whenever the previous iterate `x_n` is positive and `c > 0`.
The proof closes by `positivity` from positivity of `x`, `c / x`, and
the constant `2`. -/
@[stat_lemma]
theorem newton_quadratic_iter_pos (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    0 < (x + c / x) / 2 := by
  have h_div : 0 < c / x := div_pos hc hx
  positivity

end Pythia.Numerical
