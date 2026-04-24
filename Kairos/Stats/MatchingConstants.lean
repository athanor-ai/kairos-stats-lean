/-
Kairos.Stats.MatchingConstants — explicit sharp constants c_F in the
matching-lower-bound for the universal quantization slack theorem.

For HR and betting we already have c_HR = c_betting = 1/(2√(2π)) via
the Gaussian-random-walk adversary + small-ball. For vector and aCS,
the sharp constants differ by family-specific scaling factors that
match the per-family rate ranking.

Target: prove explicit closed-form c_vector and c_aCS. These are
what a method-of-mixtures argument would produce as the asymptotic
Laplace-approximation constants; we state them here as
arithmetic-level claims.
-/

import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.Quantization

namespace Kairos.Stats

/-- The sharp matching-lower-bound constant for the vector family:
`c_vector = √2 / (2√(2π)) = 1/(2√π)`.  Differs from `c_HR` by the
factor `√2` that matches the ranking `η_vector = √2 · η_HR`. -/
noncomputable def c_vector_sharp : ℝ := 1 / (2 * Real.sqrt Real.pi)

/-- The sharp matching-lower-bound constant for the asymptotic family:
`c_aCS = 1/(2√(2π))`, same form as `c_HR` because the aCS boundary's
`t`-invariant log term makes the Laplace-approximation constant
coincide with the HR one. -/
noncomputable def c_aCS_sharp : ℝ := 1 / (2 * Real.sqrt (2 * Real.pi))

/-- Positivity of `c_vector_sharp`. -/
theorem c_vector_sharp_pos : 0 < c_vector_sharp := by
  unfold c_vector_sharp
  positivity

/-- Positivity of `c_aCS_sharp`. -/
theorem c_aCS_sharp_pos : 0 < c_aCS_sharp := by
  unfold c_aCS_sharp
  positivity

/-- The sharp constants respect the family ranking: `c_aCS ≤ c_vector`
(equivalent to `1/(2√(2π)) ≤ 1/(2√π)`, i.e. `√π ≤ √(2π)`). -/
theorem c_sharp_ranking : c_aCS_sharp ≤ c_vector_sharp := by
  unfold c_aCS_sharp c_vector_sharp
  sorry

/-- Explicit arithmetic identity: `c_vector = √2 · c_HR` where
`c_HR = 1/(2·√(2π))`. Matches the `η_vector = √2 · η_HR` ranking
at the sharp-constant level. -/
theorem c_vector_eq_sqrt_two_mul_c_HR :
    c_vector_sharp = Real.sqrt 2 * (1 / (2 * Real.sqrt (2 * Real.pi))) := by
  sorry

end Kairos.Stats
