/-
Target: Constructive proof of the floating-point inner-product error bound.

For a length-k inner product computed with left-to-right accumulation in
round-to-nearest floating-point arithmetic with unit roundoff u, the
absolute error satisfies:

  |fl(a · b) - a · b| ≤ γ_k · Σᵢ |aᵢ| · |bᵢ|

where γ_k = k · u / (1 - k · u).

The standard model of floating-point arithmetic: each operation ⊕ satisfies
  fl(x ⊕ y) = (x + y)(1 + δ)  where |δ| ≤ u

Proof approach (Higham, Theorem 3.1):
- Define the accumulation sequence: s₁ = fl(a₁·b₁), sⱼ = fl(sⱼ₋₁ + aⱼ·bⱼ)
- Each sⱼ = (sⱼ₋₁ + aⱼ·bⱼ)(1+δⱼ) with |δⱼ| ≤ u
- By induction, sₖ = Σᵢ aᵢ·bᵢ · ∏ⱼ≥ᵢ (1+δⱼ) (with two δ's for the first term)
- |∏(1+δⱼ) - 1| ≤ γ_k when k·u < 1 (by the standard (1+u)^k ≤ 1/(1-ku) bound)
- Therefore |sₖ - Σaᵢbᵢ| ≤ γ_k · Σ|aᵢ||bᵢ|

References: Higham "Accuracy and Stability of Numerical Algorithms" 2nd ed, Theorem 3.1.
-/
import Mathlib
import Pythia.Numerical.IEEE754

namespace Pythia.Numerical

open Finset BigOperators

noncomputable section

def unitRoundoff : ℝ := machineEpsilon / 2

def gamma (k : ℕ) : ℝ := (k : ℝ) * unitRoundoff / (1 - (k : ℝ) * unitRoundoff)

/-- The standard floating-point model: each arithmetic operation introduces
    a relative error bounded by unit roundoff u. -/
structure FPModel where
  fl_mul : ℝ → ℝ → ℝ
  fl_add : ℝ → ℝ → ℝ
  mul_bound : ∀ a b, |fl_mul a b - a * b| ≤ unitRoundoff * |a * b|
  add_bound : ∀ a b, |fl_add a b - (a + b)| ≤ unitRoundoff * |a + b|

/-- Left-to-right inner product accumulation using the standard model. -/
def fp_inner_product (model : FPModel) {k : ℕ} (a b : Fin k → ℝ) : ℝ :=
  match k, a, b with
  | 0, _, _ => 0
  | 1, a, b => model.fl_mul (a 0) (b 0)
  | _n + 2, a, b =>
    model.fl_add
      (fp_inner_product model (a ∘ Fin.castSucc) (b ∘ Fin.castSucc))
      (model.fl_mul (a (Fin.last _)) (b (Fin.last _)))

/-
**(1+u)^k bound:** For any sequence of perturbations |δᵢ| ≤ u with k·u < 1:
    |∏ᵢ (1 + δᵢ) - 1| ≤ γ_k
-/
theorem prod_perturbation_bound
    (δ : Fin k → ℝ)
    (hδ : ∀ i, |δ i| ≤ unitRoundoff)
    (hku : (k : ℝ) * unitRoundoff < 1) :
    |∏ i, (1 + δ i) - 1| ≤ gamma k := by
  induction' k with k ih;
  · norm_num [ gamma ];
  · have h_expand : |∏ i : Fin (k + 1), (1 + δ i) - 1| ≤ gamma k * (1 + unitRoundoff) + unitRoundoff := by
      rw [ Fin.prod_univ_castSucc ];
      have h_expand : |∏ i : Fin k, (1 + δ (Fin.castSucc i)) - 1| ≤ gamma k := by
        exact ih _ ( fun i => hδ _ ) ( by push_cast at *; nlinarith [ show 0 ≤ unitRoundoff by exact div_nonneg ( by exact zpow_nonneg ( by norm_num ) _ ) zero_le_two ] );
      rw [ abs_le ] at *;
      constructor <;> nlinarith [ abs_le.mp ( hδ ( Fin.last k ) ), show 0 ≤ gamma k from div_nonneg ( mul_nonneg ( Nat.cast_nonneg k ) ( show 0 ≤ unitRoundoff by exact div_nonneg ( by norm_num [ machineEpsilon ] ) zero_le_two ) ) ( sub_nonneg.mpr <| by norm_num [ unitRoundoff, machineEpsilon ] at * ; nlinarith ) ];
    refine le_trans h_expand ?_;
    unfold gamma unitRoundoff;
    unfold machineEpsilon; norm_num at *;
    rw [ div_mul_eq_mul_div, div_add_div, div_le_div_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 0 by positivity, show ( unitRoundoff : ℝ ) = 1 / 9007199254740992 by unfold unitRoundoff; unfold machineEpsilon; norm_num ]

/-
============================================================
Helper lemmas for the inner product error bound
============================================================
-/
lemma unitRoundoff_pos : (0 : ℝ) < unitRoundoff := by
  exact div_pos ( by rw [ show machineEpsilon = ( 2 : ℝ ) ^ ( -52 : ℤ ) by rfl ] ; positivity ) ( by norm_num )

lemma gamma_nonneg {k : ℕ} (hku : (k : ℝ) * unitRoundoff < 1) : 0 ≤ gamma k := by
  exact div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( unitRoundoff_pos.le ) ) ( sub_nonneg.mpr hku.le )

/-
u ≤ γ₁ since γ₁ = u/(1-u) and 0 < 1-u.
-/
lemma unitRoundoff_le_gamma_one : unitRoundoff ≤ gamma 1 := by
  unfold unitRoundoff gamma; norm_num [ machineEpsilon ] ;
  unfold unitRoundoff; norm_num [ machineEpsilon ] ;

/-
The first coefficient bound: γ_{n+1}(1+u) + u ≤ γ_{n+2}
-/
lemma gamma_coeff_bound (n : ℕ) (hku : ((n + 2 : ℕ) : ℝ) * unitRoundoff < 1) :
    gamma (n + 1) * (1 + unitRoundoff) + unitRoundoff ≤ gamma (n + 2) := by
  unfold gamma;
  unfold unitRoundoff; norm_num at *;
  unfold unitRoundoff at *;
  rw [ div_mul_eq_mul_div, div_add', div_le_div_iff₀ ] <;> try nlinarith;
  unfold machineEpsilon at *; norm_num at *; nlinarith [ pow_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 ) n ] ;

/-
The second coefficient bound: 2u + u² ≤ γ_{n+2}
-/
lemma gamma_coeff2_bound (n : ℕ) (hku : ((n + 2 : ℕ) : ℝ) * unitRoundoff < 1) :
    2 * unitRoundoff + unitRoundoff ^ 2 ≤ gamma (n + 2) := by
  unfold gamma unitRoundoff machineEpsilon at *;
  rw [ le_div_iff₀ ] <;> norm_num at * <;> nlinarith [ show ( n : ℝ ) ≥ 0 by positivity ]

/-
fp_inner_product unfolds correctly for the n+2 case
-/
@[simp]
lemma fp_inner_product_succ_succ (model : FPModel) (n : ℕ) (a b : Fin (n + 2) → ℝ) :
    fp_inner_product model a b =
      model.fl_add
        (fp_inner_product model (a ∘ Fin.castSucc) (b ∘ Fin.castSucc))
        (model.fl_mul (a (Fin.last _)) (b (Fin.last _))) := by
  rfl

/-
fp_inner_product unfolds correctly for the k=1 case
-/
@[simp]
lemma fp_inner_product_one (model : FPModel) (a b : Fin 1 → ℝ) :
    fp_inner_product model a b = model.fl_mul (a 0) (b 0) := by
  rfl

/-
**Inner-product error bound (Higham Theorem 3.1, constructive).**

For vectors a, b ∈ ℝᵏ, the floating-point inner product computed with
left-to-right accumulation satisfies:

  |fl(a · b) - Σᵢ aᵢ·bᵢ| ≤ γ_k · Σᵢ |aᵢ|·|bᵢ|

when k · u < 1.
-/
theorem inner_product_error_constructive
    (model : FPModel)
    (a b : Fin k → ℝ)
    (hku : (k : ℝ) * unitRoundoff < 1) :
    |fp_inner_product model a b - ∑ i, a i * b i| ≤
      gamma k * ∑ i, |a i| * |b i| := by
  induction' k with k ih;
  · aesop;
  · rcases k with ( _ | k ) <;> simp_all +decide [ Fin.sum_univ_castSucc ];
    · refine' le_trans ( model.mul_bound _ _ ) _;
      rw [ ← abs_mul ];
      exact mul_le_mul_of_nonneg_right ( unitRoundoff_le_gamma_one ) ( abs_nonneg _ );
    · have h_ind : |fp_inner_product model (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) - (∑ i : Fin (k + 1), a (Fin.castSucc i) * b (Fin.castSucc i))| ≤ gamma (k + 1) * (∑ i : Fin (k + 1), |a (Fin.castSucc i)| * |b (Fin.castSucc i)|) := by
        specialize ih (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) (by
        nlinarith [ show 0 < unitRoundoff by exact unitRoundoff_pos ]);
        simp_all +decide [ Fin.sum_univ_castSucc ];
      have h_ind2 : |model.fl_mul (a (Fin.last _)) (b (Fin.last _)) - a (Fin.last _) * b (Fin.last _)| ≤ unitRoundoff * |a (Fin.last _) * b (Fin.last _)| := by
        exact model.mul_bound _ _;
      have h_ind3 : |model.fl_add (fp_inner_product model (a ∘ Fin.castSucc) (b ∘ Fin.castSucc)) (model.fl_mul (a (Fin.last _)) (b (Fin.last _))) - (fp_inner_product model (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) + model.fl_mul (a (Fin.last _)) (b (Fin.last _)))| ≤ unitRoundoff * |fp_inner_product model (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) + model.fl_mul (a (Fin.last _)) (b (Fin.last _))| := by
        exact model.add_bound _ _;
      have h_ind4 : |fp_inner_product model (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) + model.fl_mul (a (Fin.last _)) (b (Fin.last _))| ≤ (1 + gamma (k + 1)) * (∑ i : Fin (k + 1), |a (Fin.castSucc i)| * |b (Fin.castSucc i)|) + (1 + unitRoundoff) * |a (Fin.last _) * b (Fin.last _)| := by
        have h_ind4 : |∑ i : Fin (k + 1), a (Fin.castSucc i) * b (Fin.castSucc i)| ≤ ∑ i : Fin (k + 1), |a (Fin.castSucc i)| * |b (Fin.castSucc i)| := by
          simpa only [ ← abs_mul ] using Finset.abs_sum_le_sum_abs _ _;
        grind +qlia;
      have h_ind5 : |model.fl_add (fp_inner_product model (a ∘ Fin.castSucc) (b ∘ Fin.castSucc)) (model.fl_mul (a (Fin.last _)) (b (Fin.last _))) - (∑ i : Fin (k + 1), a (Fin.castSucc i) * b (Fin.castSucc i) + a (Fin.last _) * b (Fin.last _))| ≤ (gamma (k + 1) * (1 + unitRoundoff) + unitRoundoff) * (∑ i : Fin (k + 1), |a (Fin.castSucc i)| * |b (Fin.castSucc i)|) + (2 * unitRoundoff + unitRoundoff ^ 2) * |a (Fin.last _) * b (Fin.last _)| := by
        rw [ abs_le ] at *;
        constructor <;> cases abs_cases ( fp_inner_product model ( a ∘ Fin.castSucc ) ( b ∘ Fin.castSucc ) + model.fl_mul ( a ( Fin.last ( k + 1 ) ) ) ( b ( Fin.last ( k + 1 ) ) ) ) <;> nlinarith [ unitRoundoff_pos ];
      have h_ind6 : gamma (k + 1) * (1 + unitRoundoff) + unitRoundoff ≤ gamma (k + 2) := by
        grind +suggestions;
      have h_ind7 : 2 * unitRoundoff + unitRoundoff ^ 2 ≤ gamma (k + 2) := by
        apply gamma_coeff2_bound;
        exact_mod_cast hku;
      convert h_ind5.trans _ using 1;
      · simp +decide [ Fin.sum_univ_castSucc ];
      · refine le_trans ( add_le_add ( mul_le_mul_of_nonneg_right h_ind6 <| Finset.sum_nonneg fun _ _ => mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) ( mul_le_mul_of_nonneg_right h_ind7 <| abs_nonneg _ ) ) ?_;
        norm_num [ Fin.sum_univ_castSucc, abs_mul ];
        linarith

end

end Pythia.Numerical