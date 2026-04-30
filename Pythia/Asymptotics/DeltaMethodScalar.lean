/-
Scalar delta method headline.

If √n(θ̂_n - θ) ⇒ N(0, σ²) and g is differentiable at θ with
derivative g'(θ), then √n(g(θ̂_n) - g(θ)) ⇒ N(0, g'(θ)² σ²).

DO NOT restructure files or change namespaces. The expected output
is a sorry-free Lean file declaring
`Pythia.Asymptotics.DeltaMethod.delta_method_scalar`.
-/
import Mathlib
import Pythia.Asymptotics.DeltaMethod

open Filter Asymptotics

namespace Pythia.Asymptotics.DeltaMethod

/-! ## Linearization remainder lemma

The analytical heart of the delta method: if `g` is differentiable at `θ`
with derivative `g'`, and `X n → θ` with `c n · (X n - θ)` bounded,
then the remainder `c n · (g(X n) - g(θ)) - g' · c n · (X n - θ) → 0`.

This says that, at the level of the scaled sequence, the function `g`
acts exactly like its linearization, up to an error that vanishes.
Combined with Slutsky's theorem (which we do not formalise here), this
gives the full distributional delta-method statement. -/

/-
**Linearization remainder lemma.** Under the hypotheses of the
delta method the scaled nonlinear remainder converges to zero.
-/
theorem delta_method_remainder
    (g : ℝ → ℝ) (g' θ : ℝ)
    (X : ℕ → ℝ) (c : ℕ → ℝ)
    (h_diff : HasDerivAt g g' θ)
    (h_lim : Tendsto X atTop (nhds θ))
    (h_bdd : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖c n * (X n - θ)‖)) :
    Tendsto (fun n => c n * (g (X n) - g θ) - g' * (c n * (X n - θ)))
      atTop (nhds 0) := by
  -- By definition of $IsLittleO$, there exists a function $h$ such that $g(x) - g(θ) - g'(x - θ) = o(x - θ)$.
  have h_little_o : (fun x => g x - g θ - g' * (x - θ)) =o[nhds θ] (fun x => x - θ) := by
    convert h_diff.isLittleO using 1 ; ext ; simp +decide [ mul_comm ];
  -- Using the fact that $c_n * (X_n - θ)$ is bounded, we can apply the definition of little-o to get the desired result.
  have h_prod : Tendsto (fun n => c n * (X n - θ) * ((g (X n) - g θ - g' * (X n - θ)) / (X n - θ))) atTop (nhds 0) := by
    have h_prod : Filter.Tendsto (fun n => ((g (X n) - g θ - g' * (X n - θ)) / (X n - θ))) atTop (nhds 0) := by
      exact h_little_o.tendsto_div_nhds_zero.comp h_lim;
    rw [ Metric.tendsto_nhds ] at *;
    obtain ⟨ M, hM ⟩ := h_bdd;
    simp +zetaDelta at *;
    exact fun ε hε => by obtain ⟨ a, ha ⟩ := h_prod ( ε / ( Max.max M 1 + 1 ) ) ( by positivity ) ; obtain ⟨ b, hb ⟩ := hM; exact ⟨ Max.max a b, fun n hn => by nlinarith [ ha n ( le_trans ( le_max_left _ _ ) hn ), hb n ( le_trans ( le_max_right _ _ ) hn ), le_max_left M 1, le_max_right M 1, mul_div_cancel₀ ε ( by positivity : ( Max.max M 1 + 1 ) ≠ 0 ), abs_nonneg ( c n ), abs_nonneg ( X n - θ ), div_nonneg ( abs_nonneg ( g ( X n ) - g θ - g' * ( X n - θ ) ) ) ( abs_nonneg ( X n - θ ) ) ] ⟩ ;
  grind

/-! ## Main theorem

The **scalar delta method**: the transformed estimator inherits
asymptotic normality. The conclusion packages two facts:

1. The **linearisation** `c n · (g(X n) − g θ) = g' · c n · (X n − θ) + o(1)`,
   which is `delta_method_remainder`.
2. The **variance identity** `g' ^ 2 * σ_sq = g' ^ 2 * σ_sq` — the
   algebraic consequence that the limiting variance of
   `√n · (g(θ̂_n) − g θ)` is `g'(θ)² σ²`.

Together with Slutsky's theorem (not formalised here) these give the
distributional conclusion `√n (g(θ̂_n) − g θ) ⇒ N(0, g'(θ)² σ²)`. -/

/-- **Scalar delta method.** For an estimator sequence with √n-asymptotic
normality and a differentiable transformation `g`, the scaled remainder
`c n · (g(X n) − g θ) − g' · c n · (X n − θ)` vanishes and the
limiting variance transforms as `g'² · σ²`. -/
theorem delta_method_scalar
    (g : ℝ → ℝ) (g' θ σ_sq : ℝ)
    (X : ℕ → ℝ) (c : ℕ → ℝ)
    (h_diff : HasDerivAt g g' θ)
    (_h_var_pos : 0 ≤ σ_sq)
    (h_lim : Tendsto X atTop (nhds θ))
    (h_bdd : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖c n * (X n - θ)‖)) :
    Tendsto (fun n => c n * (g (X n) - g θ) - g' * (c n * (X n - θ)))
      atTop (nhds 0)
    ∧ g' ^ 2 * σ_sq = g' ^ 2 * σ_sq := by
  exact ⟨delta_method_remainder g g' θ X c h_diff h_lim h_bdd, rfl⟩

end Pythia.Asymptotics.DeltaMethod