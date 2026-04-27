/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Artzner–Delbaen–Eber–Heath Coherent Risk Measures (Finite Ω)

Formalises the ADEH representation theorem for coherent risk measures on a
finite probability space Ω:

> A functional ρ : (Ω → ℝ) → ℝ is coherent (translation-invariant,
> sub-additive, positively-homogeneous, monotone) **if and only if**
> ρ(X) = sup_{q ∈ 𝒬} 𝔼_q[−X] for some non-empty set 𝒬 of probability
> weights on Ω.

**Reference:** Artzner, Delbaen, Eber, Heath, *Coherent measures of risk*,
Math. Finance 9(3):203–228, 1999.

## Closure path

Finite Ω with `[Fintype Ω]` ⇒ no measure theory; random variables are just
`Ω → ℝ` and probability measures are non-negative weight functions summing to
1.  The hard direction (coherent ⇒ sup-representation) uses the algebraic
Hahn–Banach theorem (`exists_extension_of_le_sublinear`) from Mathlib to
produce a dominated linear extension, then shows the extension corresponds to
a probability weight via the coherence axioms.
-/
import Mathlib

namespace Pythia.Risk.CoherentMeasures

open Finset BigOperators

/-! ## 1. Definitions -/

/-- A probability weight on a finite type: non-negative reals summing to 1. -/
structure ProbWeight (Ω : Type*) [Fintype Ω] where
  w : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ w ω
  sum_one : ∑ ω, w ω = 1

/-- Expected value of `X : Ω → ℝ` under probability weight `q`. -/
noncomputable def expect {Ω : Type*} [Fintype Ω] (q : ProbWeight Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, q.w ω * X ω

/-- Standard basis vector: 1 at `ω`, 0 elsewhere. -/
def stdBasis {Ω : Type*} [DecidableEq Ω] (ω : Ω) : Ω → ℝ :=
  fun ω' => if ω' = ω then 1 else 0

/-- The four ADEH coherence axioms for a risk measure on `Ω → ℝ`. -/
structure IsCoherent {Ω : Type*} [Fintype Ω] (ρ : (Ω → ℝ) → ℝ) : Prop where
  /-- Adding a sure amount `m` reduces risk by `m`. -/
  translation_inv : ∀ (X : Ω → ℝ) (m : ℝ), ρ (fun ω => X ω + m) = ρ X - m
  /-- Diversification does not increase risk. -/
  subadditive : ∀ X Y : Ω → ℝ, ρ (X + Y) ≤ ρ X + ρ Y
  /-- Scaling a position scales its risk. -/
  pos_homogeneous : ∀ (t : ℝ), 0 ≤ t → ∀ X : Ω → ℝ, ρ (t • X) = t * ρ X
  /-- Dominating payoffs have lower risk. -/
  monotone : ∀ X Y : Ω → ℝ, (∀ ω, X ω ≤ Y ω) → ρ Y ≤ ρ X

/-- The ADEH dual set: probability weights q with 𝔼_q[−X] ≤ ρ(X) for all X. -/
def adehSet {Ω : Type*} [Fintype Ω] (ρ : (Ω → ℝ) → ℝ) : Set (ProbWeight Ω) :=
  {q | ∀ X : Ω → ℝ, expect q (-X) ≤ ρ X}

/-! ## 2. Elementary consequences of coherence -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
variable {ρ : (Ω → ℝ) → ℝ}

lemma coherent_zero (hρ : IsCoherent ρ) : ρ 0 = 0 := by
  convert hρ.pos_homogeneous 0 ( by norm_num ) 0 using 1 ; norm_num;
  ring

lemma coherent_nonneg_imp_nonpos (hρ : IsCoherent ρ) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : ρ X ≤ 0 := by
      have h_nonneg_X : ρ X ≤ ρ 0 := by
        exact hρ.monotone _ _ hX;
      exact h_nonneg_X.trans ( by linarith [ coherent_zero hρ ] )

lemma coherent_const (hρ : IsCoherent ρ) (c : ℝ) :
    ρ (fun _ : Ω => c) = -c := by
      have := hρ.translation_inv 0 c;
      simpa [ coherent_zero hρ ] using this

/-! ## 3. Linear-map decomposition on `Ω → ℝ` -/

/-
Every `X : Ω → ℝ` decomposes as `∑ ω, X ω • stdBasis ω`.
-/
lemma fun_eq_sum_stdBasis (X : Ω → ℝ) :
    X = ∑ ω : Ω, X ω • stdBasis ω := by
      ext ω; simp +decide [ stdBasis ] ;

/-
A linear map `g : (Ω → ℝ) →ₗ[ℝ] ℝ` equals `∑ ω, g(eω) · X(ω)`.
-/
lemma linearMap_eq_sum_single (g : (Ω → ℝ) →ₗ[ℝ] ℝ) (X : Ω → ℝ) :
    g X = ∑ ω : Ω, g (stdBasis ω) * X ω := by
      rw [ fun_eq_sum_stdBasis X, map_sum ];
      simp +decide [ mul_comm, Finset.mul_sum _ _ _ ];
      simp +decide [ stdBasis ]

/-! ## 4. Hahn–Banach: dominated extension with equality at a point -/

/-
For a sublinear `N` and any `x₀`, there is a linear `g ≤ N` with `g x₀ = N x₀`.
    Follows from `exists_extension_of_le_sublinear` applied to the partial linear map
    on `span {x₀}` defined by `t • x₀ ↦ t * N(x₀)`.
-/
lemma exists_linear_le_eq (N : (Ω → ℝ) → ℝ)
    (hN_hom : ∀ (c : ℝ), 0 < c → ∀ x : Ω → ℝ, N (c • x) = c * N x)
    (hN_sub : ∀ x y : Ω → ℝ, N (x + y) ≤ N x + N y)
    (x₀ : Ω → ℝ) :
    ∃ g : (Ω → ℝ) →ₗ[ℝ] ℝ, (∀ x, g x ≤ N x) ∧ g x₀ = N x₀ := by
      -- Define a linear functional $f$ on the subspace spanned by $x₀$.
      obtain ⟨f, hf⟩ : ∃ f : (Submodule.span ℝ {x₀}) →ₗ[ℝ] ℝ, (∀ x : Submodule.span ℝ {x₀}, f x ≤ N (x : Ω → ℝ)) ∧ f ⟨x₀, by simp⟩ = N x₀ := by
        by_cases hx₀ : x₀ = 0;
        · refine' ⟨ 0, _, _ ⟩ <;> simp +decide [ hx₀ ];
          · have := hN_hom 2 zero_lt_two 0; norm_num at this; linarith;
          · have := hN_hom 2 zero_lt_two 0; norm_num at this; linarith;
        · -- Define a linear functional $f$ on the subspace spanned by $x₀$ such that $f(x₀) = N(x₀)$.
          obtain ⟨f, hf⟩ : ∃ f : (Submodule.span ℝ {x₀}) →ₗ[ℝ] ℝ, f ⟨x₀, by simp⟩ = N x₀ := by
            -- Since $x₀ \neq 0$, the submodule spanned by $x₀$ is one-dimensional.
            have h_one_dim : ∃ f : (Submodule.span ℝ {x₀}) →ₗ[ℝ] ℝ, f ⟨x₀, by simp⟩ = 1 := by
              have h_one_dim : ∃ f : (Submodule.span ℝ {x₀}) →ₗ[ℝ] ℝ, f ⟨x₀, by simp⟩ ≠ 0 := by
                have h_one_dim : ∃ f : (Ω → ℝ) →ₗ[ℝ] ℝ, f x₀ ≠ 0 := by
                  contrapose! hx₀;
                  exact funext fun i => by simpa using hx₀ ( LinearMap.proj i ) ;
                exact ⟨ h_one_dim.choose.comp ( Submodule.subtype _ ), h_one_dim.choose_spec ⟩;
              exact ⟨ h_one_dim.choose.smulRight ( h_one_dim.choose ⟨ x₀, by simp ⟩ ) ⁻¹, by simp +decide [ h_one_dim.choose_spec ] ⟩;
            exact ⟨ h_one_dim.choose.smulRight ( N x₀ ), by simp +decide [ h_one_dim.choose_spec ] ⟩;
          refine' ⟨ f, _, hf ⟩;
          intro x
          obtain ⟨c, hc⟩ : ∃ c : ℝ, x = c • ⟨x₀, by simp⟩ := by
            rcases x with ⟨ x, hx ⟩ ; rcases Submodule.mem_span_singleton.mp hx with ⟨ c, rfl ⟩ ; exact ⟨ c, rfl ⟩ ;
          by_cases hc_pos : 0 < c <;> simp_all +decide [ mul_comm ];
          · have := f.map_smul c ⟨ x₀, by simp +decide ⟩ ; aesop;
          · by_cases hc_neg : c < 0;
            · have := hN_hom ( -c ) ( neg_pos.mpr hc_neg ) x₀; simp_all +decide [ neg_smul ] ;
              have := f.map_smul c ⟨ x₀, by simp +decide ⟩ ; simp_all +decide [ mul_comm ] ;
              have := hN_sub ( c • x₀ ) ( - ( c • x₀ ) ) ; simp_all +decide [ add_comm ] ;
              have := hN_hom 2 zero_lt_two 0; norm_num at this; nlinarith;
            · norm_num [ show c = 0 by linarith ] at *;
              have := hN_hom 2 zero_lt_two 0; norm_num at this; linarith! [ f.map_zero ] ;
      have := @exists_extension_of_le_sublinear ( Ω → ℝ );
      specialize this ( LinearPMap.mk ( Submodule.span ℝ { x₀ } ) f ) N hN_hom hN_sub hf.1;
      obtain ⟨ g, hg₁, hg₂ ⟩ := this; use g; aesop;

/-! ## 5. Dominated linear functional → probability weight -/

/-
If `g ≤ ρ` for coherent `ρ`, then `−g(eω) ≥ 0`.

    Proof: `stdBasis ω ≥ 0`, so `ρ(stdBasis ω) ≤ 0` by monotonicity and `ρ(0) = 0`.
    Since `g(stdBasis ω) ≤ ρ(stdBasis ω) ≤ 0`, we get `−g(stdBasis ω) ≥ 0`.
-/
lemma dominated_nonneg_weight (hρ : IsCoherent ρ)
    (g : (Ω → ℝ) →ₗ[ℝ] ℝ) (hg : ∀ x, g x ≤ ρ x) (ω : Ω) :
    0 ≤ -g (stdBasis ω) := by
      have h_nonpos : ρ (stdBasis ω) ≤ 0 := by
        apply coherent_nonneg_imp_nonpos hρ;
        exact fun ω' => by unfold stdBasis; split_ifs <;> norm_num;
      linarith [ hg ( stdBasis ω ) ]

/-
If `g ≤ ρ` for coherent `ρ`, then `∑ ω, −g(eω) = 1`.

    Proof: `g(𝟙) ≤ ρ(𝟙) = −1` and `−g(𝟙) = g(−𝟙) ≤ ρ(−𝟙) = 1`,
    so `g(𝟙) = −1`. Then `g(𝟙) = ∑ g(eω)` by linearity, giving `∑ −g(eω) = 1`.
-/
lemma dominated_sum_one (hρ : IsCoherent ρ)
    (g : (Ω → ℝ) →ₗ[ℝ] ℝ) (hg : ∀ x, g x ≤ ρ x) :
    ∑ ω : Ω, (-g (stdBasis ω)) = 1 := by
      have h_sum : ∑ ω, g (stdBasis ω) = g (fun _ => 1) := by
        rw [ ← map_sum ];
        exact congr_arg _ ( funext fun x => by simp +decide [ stdBasis ] );
      have h_g1 : g (fun _ => 1) = -1 := by
        have h_le : g (fun _ => 1) ≤ -1 := by
          exact le_trans ( hg _ ) ( by simpa using coherent_const hρ 1 |> le_of_eq )
        have h_ge : g (fun _ => -1) ≤ 1 := by
          exact le_trans ( hg _ ) ( by simpa using coherent_const hρ ( -1 ) |> le_of_eq )
        have h_ge : g (fun _ => -1) = -g (fun _ => 1) := by
          convert g.map_neg ( fun _ => 1 ) using 1;
        linarith;
      rw [ Finset.sum_neg_distrib, h_sum, h_g1, neg_neg ]

/-- Build a `ProbWeight` from a dominated linear functional. -/
noncomputable def probWeightOfDominated (hρ : IsCoherent ρ)
    (g : (Ω → ℝ) →ₗ[ℝ] ℝ) (hg : ∀ x, g x ≤ ρ x) : ProbWeight Ω where
  w ω := -g (stdBasis ω)
  nonneg := dominated_nonneg_weight hρ g hg
  sum_one := dominated_sum_one hρ g hg

/-
The constructed weight satisfies `expect q (−X) = g(X)`.
-/
lemma expect_probWeightOfDominated (hρ : IsCoherent ρ)
    (g : (Ω → ℝ) →ₗ[ℝ] ℝ) (hg : ∀ x, g x ≤ ρ x) (X : Ω → ℝ) :
    expect (probWeightOfDominated hρ g hg) (-X) = g X := by
      simp +decide [ expect, probWeightOfDominated ];
      rw [ ← linearMap_eq_sum_single g X ]

/-! ## 6. The ADEH representation theorem -/

/-- **Hard direction (attainment):** for any `X`, there exists `q ∈ adehSet ρ`
    with `𝔼_q[−X] = ρ(X)`. -/
theorem adeh_attained (ρ : (Ω → ℝ) → ℝ) (hρ : IsCoherent ρ) (X : Ω → ℝ) :
    ∃ q ∈ adehSet ρ, expect q (-X) = ρ X := by
  obtain ⟨g, hg_le, hg_eq⟩ := exists_linear_le_eq ρ
    (fun c hc x => hρ.pos_homogeneous c (le_of_lt hc) x) hρ.subadditive X
  exact ⟨probWeightOfDominated hρ g hg_le,
    fun Y => (expect_probWeightOfDominated hρ g hg_le Y).le.trans (hg_le Y),
    (expect_probWeightOfDominated hρ g hg_le X).trans hg_eq⟩

/-- The `adehSet` of a coherent `ρ` is non-empty. -/
theorem adehSet_nonempty (ρ : (Ω → ℝ) → ℝ) (hρ : IsCoherent ρ) :
    (adehSet ρ).Nonempty :=
  let ⟨q, hq, _⟩ := adeh_attained ρ hρ 0; ⟨q, hq⟩

/-
**Full ADEH representation theorem (hard direction):**
    `ρ(X) = sup { 𝔼_q[−X] | q ∈ adehSet ρ }`.
-/
theorem adeh_representation (ρ : (Ω → ℝ) → ℝ) (hρ : IsCoherent ρ) (X : Ω → ℝ) :
    ρ X = sSup ((fun q => expect q (-X)) '' adehSet ρ) := by
      -- Apply the lemma adeh_attained to obtain the existence of q in adehSet ρ such that expect q (-X) = ρ(X).
      have hq : ∃ q ∈ adehSet ρ, expect q (-X) = ρ X := by
        exact adeh_attained ρ hρ X;
      rw [ eq_comm, csSup_eq_of_forall_le_of_forall_lt_exists_gt ];
      · exact ⟨ _, ⟨ hq.choose, hq.choose_spec.1, rfl ⟩ ⟩;
      · rintro _ ⟨ q, hq, rfl ⟩ ; exact hq X;
      · exact fun w hw => ⟨ _, ⟨ hq.choose, hq.choose_spec.1, rfl ⟩, hw.trans_le hq.choose_spec.2.ge ⟩

/-
**Easy direction:** any non-empty sup-expectation representation is coherent.
-/
theorem isCoherent_sup_expect (Q : Set (ProbWeight Ω)) (hQ : Q.Nonempty)
    (hbdd : ∀ X : Ω → ℝ, BddAbove ((fun q => expect q (-X)) '' Q)) :
    IsCoherent (fun X => sSup ((fun q => expect q (-X)) '' Q)) := by
      constructor;
      · intro X m; rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ];
        · exact hQ.image _;
        · rintro _ ⟨ q, hq, rfl ⟩ ; simp +decide [ expect ] ; ring_nf;
          simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_eq_add_neg ];
          simp +decide [ ← Finset.sum_mul _ _ _, q.sum_one ];
          exact le_csSup ( by rcases hbdd X with ⟨ M, hM ⟩ ; exact ⟨ M, Set.forall_mem_image.2 fun q hq => by simpa [ expect ] using hM ⟨ q, hq, rfl ⟩ ⟩ ) ( Set.mem_image_of_mem _ hq );
        · intro w hw
          obtain ⟨q, hqQ, hq⟩ : ∃ q ∈ Q, w + m < expect q (-X) := by
            simpa using exists_lt_of_lt_csSup ( Set.Nonempty.image _ hQ ) ( by linarith );
          refine' ⟨ _, ⟨ q, hqQ, rfl ⟩, _ ⟩;
          simp_all +decide [ expect, Finset.sum_add_distrib, mul_add ];
          simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, q.sum_one ];
          linarith;
      · intro X Y; refine' csSup_le _ _ <;> simp_all +decide [ expect ] ;
        intro q hq; have := le_csSup ( hbdd X ) ( Set.mem_image_of_mem _ hq ) ; have := le_csSup ( hbdd Y ) ( Set.mem_image_of_mem _ hq ) ; simp_all +decide [ mul_add, Finset.sum_add_distrib ] ; linarith;
      · intro t ht X;
        by_cases ht' : t = 0 <;> simp_all +decide [ expect, mul_left_comm, Finset.mul_sum _ _ _ ];
        rw [ ← smul_eq_mul, ← Real.sSup_smul_of_nonneg ht ];
        congr with x ; simp +decide [ Set.mem_smul_set, Finset.mul_sum _ _ _ ];
      · intro X Y hXY
        have h_le : ∀ q ∈ Q, expect q (-Y) ≤ expect q (-X) := by
          exact fun q hq => Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ( neg_le_neg ( hXY ω ) ) ( q.nonneg ω );
        exact csSup_le ( Set.Nonempty.image _ hQ ) ( Set.forall_mem_image.2 fun q hq => le_trans ( h_le q hq ) ( le_csSup ( hbdd _ ) ( Set.mem_image_of_mem _ hq ) ) )

end Pythia.Risk.CoherentMeasures