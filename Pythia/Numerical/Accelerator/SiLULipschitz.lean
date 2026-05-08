import Mathlib

noncomputable def silu (x : ℝ) : ℝ := x * (1 / (1 + Real.exp (-x)))

-- SiLU(x) = x · σ(x) where σ is the sigmoid function.
-- The derivative is σ(x) + x·σ(x)·(1-σ(x)) = 1/(1+exp(-x)) + x·exp(-x)/(1+exp(-x))²
-- |silu'(x)| ≤ 1 + 1 = 2, so SiLU is 2-Lipschitz.

private lemma one_add_exp_neg_pos (x : ℝ) : (0 : ℝ) < 1 + Real.exp (-x) := by
  linarith [Real.exp_pos (-x)]

private lemma mul_exp_neg_self_le_one (t : ℝ) (ht : 0 ≤ t) : t * Real.exp (-t) ≤ 1 := by
  nlinarith [ Real.exp_pos ( -t ), Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ]

private lemma silu_hasDerivAt (x : ℝ) :
    HasDerivAt silu (1 / (1 + Real.exp (-x)) + x * Real.exp (-x) / (1 + Real.exp (-x)) ^ 2) x := by
  unfold silu; convert HasDerivAt.mul ( hasDerivAt_id x ) ( HasDerivAt.div ( hasDerivAt_const _ _ ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.exp ( hasDerivAt_neg x ) ) ) _ ) using 1 <;> norm_num <;> ring;
  positivity

private lemma silu_differentiable : Differentiable ℝ silu := by
  intro x
  exact (silu_hasDerivAt x).differentiableAt

private lemma deriv_silu (x : ℝ) :
    deriv silu x = 1 / (1 + Real.exp (-x)) + x * Real.exp (-x) / (1 + Real.exp (-x)) ^ 2 :=
  (silu_hasDerivAt x).deriv

private lemma abs_silu_deriv_le_two (x : ℝ) :
    |deriv silu x| ≤ 2 := by
  rw [ deriv_silu, abs_le ];
  constructor <;> norm_num [ Real.exp_neg ];
  · field_simp;
    nlinarith [ Real.exp_pos x, Real.exp_neg x, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos x ) ), Real.add_one_le_exp x, Real.add_one_le_exp ( -x ) ];
  · field_simp;
    nlinarith [ Real.exp_pos x, Real.exp_neg x, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos x ) ), Real.add_one_le_exp x, Real.add_one_le_exp ( -x ) ]

theorem silu_lipschitz : LipschitzWith 2 silu := by
  exact lipschitzWith_of_nnnorm_deriv_le ( show Differentiable ℝ silu from silu_differentiable ) fun x => by simpa [ ← NNReal.coe_le_coe ] using abs_silu_deriv_le_two x;