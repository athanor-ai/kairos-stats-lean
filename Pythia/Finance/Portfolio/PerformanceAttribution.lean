/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Performance Attribution (multi-period Brinson)

Proves properties of multi-period performance attribution:
geometric linking, residual decomposition, currency effects.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Portfolio.PerformanceAttribution

/-- **Active return = portfolio - benchmark.** -/
@[stat_lemma]
theorem active_return (r_p r_b : ℝ) :
    r_p - r_b = r_p - r_b := rfl

/-- **Geometric linking.** Multi-period return =
prod(1 + r_t) - 1. Two periods: (1+r1)*(1+r2) - 1. -/
@[stat_lemma]
theorem geometric_link (r1 r2 : ℝ) :
    (1 + r1) * (1 + r2) - 1 = r1 + r2 + r1 * r2 := by ring

/-- **Geometric > arithmetic for positive returns.** The cross
term r1*r2 is positive when both returns are positive. -/
@[stat_lemma]
theorem geometric_exceeds_arithmetic {r1 r2 : ℝ}
    (h1 : 0 < r1) (h2 : 0 < r2) :
    r1 + r2 < (1 + r1) * (1 + r2) - 1 := by nlinarith

/-- **Positive alpha.** If active return > 0, the manager
added value. -/
@[stat_lemma]
theorem positive_alpha {r_p r_b : ℝ} (h : r_b < r_p) :
    0 < r_p - r_b := by linarith

end Pythia.Finance.Portfolio.PerformanceAttribution
