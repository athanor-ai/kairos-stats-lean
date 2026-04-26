/-
Copyright (c) 2024 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Wold Decomposition Theorem

The Wold decomposition theorem (Wold 1938) states that every zero-mean covariance-stationary
process in L²(Ω, μ) decomposes uniquely as `X_t = V_t + D_t` where:
- `V_t = ∑_{j ≥ 0} cⱼ ε_{t-j}` is a **MA(∞)** process with `∑ cⱼ² < ∞` and
  white-noise innovations `{ε_t}`;
- `D_t` is **deterministic**, lying in the remote-past σ-field.

We formalize this at the abstract Hilbert-space level: given a linear isometry `U` on a
real Hilbert space `H`, we decompose `H` into the *unitary subspace* (remote past) and
its orthogonal complement (purely nondeterministic / shift part), then extract the
MA(∞) representation using the wandering subspace.

## Main definitions

* `Wold.unitarySubspace U` — the remote past: `⨅ n, closure(range Uⁿ)`.
* `Wold.shiftSubspace U` — orthogonal complement of the unitary subspace.
* `Wold.wanderingSubspace U` — `(range U)ᗮ`; one-step innovation space.
* `Wold.innovation U x n` — projection of `x` onto the `n`-th level subspace
  `closure(range Uⁿ) ⊖ closure(range Uⁿ⁺¹)`.
* `Wold.deterministicComponent U x` — projection onto the unitary (remote-past) subspace.
* `Wold.maComponent U x` — the purely nondeterministic (MA) part: `x - deterministicComponent`.

## Main results

* `Wold.unitarySubspace_isClosed` — the unitary subspace is closed.
* `Wold.unitarySubspace_invariant` — the unitary subspace is `U`-invariant.
* `Wold.wold_decomposition` — every `x ∈ H` decomposes as
  `x = maComponent U x + deterministicComponent U x`.
* `Wold.decomposition_orthogonal` — the two components are orthogonal.
* `Wold.innovation_orthogonal` — innovations at different lags are orthogonal.
* `Wold.decomposition_unique` — uniqueness of the decomposition.
* `Wold.maCoeff_sq_summable` — square-summability of MA coefficients `∑ cⱼ² < ∞`.

## References

* H. Wold, *A Study in the Analysis of Stationary Time Series*, 1938.
* J. D. Hamilton, *Time Series Analysis*, Princeton University Press, 1994, §3.4.

## Implementation notes

We work in a real inner product space `H` with `CompleteSpace H`. The linear isometry
`U : H →ₗᵢ[ℝ] H` models the time-shift operator. This abstract setting covers
the L²(Ω, μ) case: elements of `H` are square-integrable random variables, `U` is
the shift `X_t ↦ X_{t+1}`, inner product is covariance, and stationarity is encoded
by `U` being an isometry.
-/

open scoped InnerProductSpace
open Submodule LinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace Wold

/-! ### Core subspace definitions -/

/-- The **unitary subspace** (remote past): the intersection of all closures of ranges of
iterates of `U`. This is the largest closed subspace on which `U` restricts to a
surjective isometry (a unitary operator). In the time-series interpretation, this is
the space of deterministic components. -/
def unitarySubspace (U : H →ₗᵢ[ℝ] H) : Submodule ℝ H :=
  ⨅ n : ℕ, (U.toLinearMap ^ n).range.topologicalClosure

/-- The **shift subspace** (purely nondeterministic part): the orthogonal complement
of the unitary subspace. Elements admit an MA(∞) representation. -/
def shiftSubspace (U : H →ₗᵢ[ℝ] H) : Submodule ℝ H :=
  (unitarySubspace U)ᗮ

/-- The **wandering subspace**: vectors orthogonal to the range of `U`. These are the
one-step innovations; vectors in this space are unpredictable from the past. -/
def wanderingSubspace (U : H →ₗᵢ[ℝ] H) : Submodule ℝ H :=
  U.toLinearMap.range.topologicalClosureᗮ

/-! ### Basic properties of the unitary subspace -/

/-- The unitary subspace is closed. -/
theorem unitarySubspace_isClosed (U : H →ₗᵢ[ℝ] H) :
    IsClosed (unitarySubspace U : Set H) := by
  rw [unitarySubspace, Submodule.coe_iInf]
  exact isClosed_iInter fun n => (U.toLinearMap ^ n).range.isClosed_topologicalClosure

/-- The unitary subspace equals its own topological closure. -/
theorem unitarySubspace_eq_closure (U : H →ₗᵢ[ℝ] H) :
    (unitarySubspace U).topologicalClosure = unitarySubspace U :=
  IsClosed.submodule_topologicalClosure_eq (unitarySubspace_isClosed U)

/-- The ranges of iterates form a decreasing (antitone) sequence of closed subspaces. -/
theorem range_pow_antitone (U : H →ₗᵢ[ℝ] H) :
    Antitone (fun n => (U.toLinearMap ^ n).range.topologicalClosure) := by
  intro m n hmn
  apply Submodule.topologicalClosure_mono
  rw [show n = m + (n - m) from (Nat.add_sub_cancel' hmn).symm, pow_add]
  exact LinearMap.range_comp_le_range _ _

/-- The unitary subspace is contained in the closure of the range of every iterate. -/
theorem unitarySubspace_le_range_pow (U : H →ₗᵢ[ℝ] H) (n : ℕ) :
    unitarySubspace U ≤ (U.toLinearMap ^ n).range.topologicalClosure :=
  iInf_le _ n

/-
`U` maps the unitary subspace into itself: the unitary subspace is `U`-invariant.
-/
theorem unitarySubspace_invariant (U : H →ₗᵢ[ℝ] H) (x : H)
    (hx : x ∈ unitarySubspace U) : U x ∈ unitarySubspace U := by
  simp_all +decide [ unitarySubspace, Submodule.mem_iInf ];
  intro i;
  rcases i with ( _ | i );
  · exact subset_closure ⟨ U x, rfl ⟩;
  · obtain ⟨ y, hy ⟩ := mem_closure_iff_seq_limit.mp ( hx i );
    refine' mem_closure_of_tendsto ( U.continuous.continuousAt.tendsto.comp hy.2 ) _;
    simp_all +decide [ pow_succ', mul_assoc ]

/-! ### Orthogonal projection and decomposition -/

/-- The unitary subspace has an orthogonal projection (it is a closed subspace of a
complete space). -/
instance unitarySubspace_hasOrthogonalProjection (U : H →ₗᵢ[ℝ] H) :
    (unitarySubspace U).HasOrthogonalProjection := by
  haveI : IsClosed (unitarySubspace U : Set H) := unitarySubspace_isClosed U
  infer_instance

/-- The **deterministic component** of `x`: its orthogonal projection onto the
unitary (remote-past) subspace. -/
def deterministicComponent (U : H →ₗᵢ[ℝ] H) (x : H) : H :=
  (unitarySubspace U).orthogonalProjection x

/-- The **MA component** (purely nondeterministic part) of `x`: its projection onto
the shift subspace. -/
def maComponent (U : H →ₗᵢ[ℝ] H) (x : H) : H :=
  x - deterministicComponent U x

/-- **Wold decomposition**: every vector decomposes as the sum of its MA component
and its deterministic component. -/
theorem wold_decomposition (U : H →ₗᵢ[ℝ] H) (x : H) :
    x = maComponent U x + deterministicComponent U x := by
  simp [maComponent, sub_add_cancel]

/-- The deterministic component lies in the unitary subspace. -/
theorem deterministicComponent_mem (U : H →ₗᵢ[ℝ] H) (x : H) :
    deterministicComponent U x ∈ unitarySubspace U :=
  ((unitarySubspace U).orthogonalProjection x).2

/-
The MA component lies in the shift subspace (orthogonal to the unitary subspace).
-/
theorem maComponent_mem (U : H →ₗᵢ[ℝ] H) (x : H) :
    maComponent U x ∈ shiftSubspace U := by
  unfold maComponent;
  unfold shiftSubspace deterministicComponent;
  simp +decide [ Submodule.mem_orthogonal' ];
  exact Submodule.orthogonalProjectionFn_inner_eq_zero x

/-
The two components are orthogonal.
-/
theorem decomposition_orthogonal (U : H →ₗᵢ[ℝ] H) (x : H) :
    ⟪maComponent U x, deterministicComponent U x⟫_ℝ = 0 := by
  -- By definition of orthogonal projection, we know that the projection of x onto the unitary subspace is orthogonal to the orthogonal complement of the unitary subspace. Use this fact.
  apply Submodule.inner_right_of_mem_orthogonal;
  convert maComponent_mem U x;
  simp +decide [ shiftSubspace ];
  exact deterministicComponent_mem U x

/-
**Pythagoras**: the norm squares of the components sum to the norm square of `x`.
-/
theorem decomposition_norm_sq (U : H →ₗᵢ[ℝ] H) (x : H) :
    ‖x‖ ^ 2 = ‖maComponent U x‖ ^ 2 + ‖deterministicComponent U x‖ ^ 2 := by
  -- By definition of maComponent and deterministicComponent, we have x = maComponent U x + deterministicComponent U x.
  have h_decomp : x = maComponent U x + deterministicComponent U x :=
    wold_decomposition U x;
  conv_lhs => rw [ h_decomp, @norm_add_sq ℝ ];
  rw [ decomposition_orthogonal ] ; norm_num

/-! ### Innovation sequence and orthogonality -/

/-- Abbreviation for the `n`-th past subspace `closure(range Uⁿ)`. -/
private def M (U : H →ₗᵢ[ℝ] H) (n : ℕ) : Submodule ℝ H :=
  (U.toLinearMap ^ n).range.topologicalClosure

private theorem M_isClosed (U : H →ₗᵢ[ℝ] H) (n : ℕ) :
    IsClosed (M U n : Set H) :=
  (U.toLinearMap ^ n).range.isClosed_topologicalClosure

private instance M_hasOrthogonalProjection (U : H →ₗᵢ[ℝ] H) (n : ℕ) :
    (M U n).HasOrthogonalProjection := by
  haveI : IsClosed (M U n : Set H) := M_isClosed U n
  infer_instance

/-- The **innovation** of `x` at lag `n`: the projection of `x` onto the `n`-th level
subspace `M_n ⊖ M_{n+1} = closure(range Uⁿ) ⊖ closure(range Uⁿ⁺¹)`.

This is defined as `P_{M_n}(x) - P_{M_{n+1}}(x)` where `P_{M_k}` denotes orthogonal
projection onto the `k`-th past subspace. In the time-series interpretation, this gives
the component of `x` attributable to the `n`-th lagged shock `ε_{t-n}`. -/
def innovation (U : H →ₗᵢ[ℝ] H) (x : H) (n : ℕ) : H :=
  (M U n).orthogonalProjection x - (M U (n + 1)).orthogonalProjection x

/-
Innovations at different lags are orthogonal: `⟪ε_m, ε_n⟫ = 0` for `m ≠ n`.
This is the **white-noise property** of the innovation sequence.
-/
theorem innovation_orthogonal (U : H →ₗᵢ[ℝ] H) (x : H) {m n : ℕ} (hmn : m ≠ n) :
    ⟪innovation U x m, innovation U x n⟫_ℝ = 0 := by
  by_cases hmn' : m < n;
  · have h_ortho : ∀ w ∈ M U (m + 1), ⟪innovation U x m, w⟫_ℝ = 0 := by
      intro w hw
      have h_ortho : ⟪(M U m).orthogonalProjection x - x, w⟫_ℝ = 0 := by
        have h_ortho : w ∈ M U m := by
          have h_ortho : M U (m + 1) ≤ M U m := by
            exact range_pow_antitone U ( Nat.le_succ _ );
          exact h_ortho hw;
        rw [ ← neg_sub, inner_neg_left ];
        simp +decide [ h_ortho, Submodule.starProjection_inner_eq_zero ]
      have h_ortho' : ⟪(M U (m + 1)).orthogonalProjection x - x, w⟫_ℝ = 0 := by
        rw [ ← neg_eq_zero, ← inner_neg_left ] ; aesop
      simp_all +decide [ inner_sub_left, inner_sub_right ];
      unfold innovation; simp_all +decide [ sub_eq_iff_eq_add ] ;
      rw [ inner_sub_left, h_ortho, h_ortho', sub_self ];
    apply h_ortho;
    refine' Submodule.sub_mem _ _ _;
    · have h_subset : M U n ≤ M U (m + 1) := by
        exact range_pow_antitone U hmn';
      exact h_subset ( Submodule.coe_mem _ );
    · have h_ortho : M U (n + 1) ≤ M U (m + 1) := by
        exact range_pow_antitone U ( by linarith );
      exact h_ortho ( Submodule.coe_mem _ );
  · have h_ortho : ∀ w ∈ M U (n + 1), ⟪innovation U x n, w⟫_ℝ = 0 := by
      intro w hw
      have h_ortho : ⟪(M U n).orthogonalProjection x - x, w⟫_ℝ = 0 := by
        have h_ortho : w ∈ M U n := by
          exact range_pow_antitone U ( Nat.le_succ _ ) hw;
        rw [ ← neg_sub, inner_neg_left ];
        simp +decide [ h_ortho, Submodule.starProjection_inner_eq_zero ];
      have h_ortho' : ⟪(M U (n + 1)).orthogonalProjection x - x, w⟫_ℝ = 0 := by
        rw [ ← neg_eq_zero, ← inner_neg_left ] ; aesop;
      unfold innovation; simp_all +decide [ inner_sub_left, inner_sub_right ] ;
      linarith;
    rw [ real_inner_comm, h_ortho _ ];
    have h_ortho : M U (m + 1) ≤ M U (n + 1) ∧ M U m ≤ M U (n + 1) := by
      exact ⟨ range_pow_antitone U ( by linarith ), range_pow_antitone U ( by linarith [ Nat.lt_of_le_of_ne ( le_of_not_gt hmn' ) hmn.symm ] ) ⟩;
    exact Submodule.sub_mem _ ( h_ortho.2 ( Submodule.coe_mem _ ) ) ( h_ortho.1 ( Submodule.coe_mem _ ) )

/-! ### Uniqueness of the decomposition -/

/-
**Uniqueness**: if `x = v + d` where `v ∈ shiftSubspace U` and `d ∈ unitarySubspace U`,
then `v = maComponent U x` and `d = deterministicComponent U x`.
-/
theorem decomposition_unique (U : H →ₗᵢ[ℝ] H) (x v d : H)
    (hv : v ∈ shiftSubspace U) (hd : d ∈ unitarySubspace U)
    (hsum : x = v + d) :
    v = maComponent U x ∧ d = deterministicComponent U x := by
  unfold maComponent;
  rw [ hsum, add_sub_assoc, deterministicComponent ];
  -- Since $d$ is in the unitary subspace, its orthogonal projection onto the unitary subspace is itself.
  have h_proj_d : (unitarySubspace U).orthogonalProjection d = d := by
    exact Submodule.starProjection_eq_self_iff.mpr hd;
  simp_all +decide [ Submodule.mem_orthogonal' ];
  exact (starProjection_apply_eq_zero_iff (unitarySubspace U)).mpr hv

/-! ### MA(∞) coefficient structure -/

/-- The MA coefficient `c_j` for the Wold representation of `x`: the norm of the
`j`-th innovation `P_{M_j}(x) - P_{M_{j+1}}(x)`. -/
def maCoeff (U : H →ₗᵢ[ℝ] H) (x : H) (j : ℕ) : ℝ :=
  ‖innovation U x j‖

/-
The partial sum of squared innovation norms telescopes and is bounded by `‖x‖²`.
Since `M_0 = H`, we have `∑_{j<N} ‖ε_j‖² = ‖x - P_{M_N}(x)‖² ≤ ‖x‖²`.
-/
theorem innovation_partial_sum_le (U : H →ₗᵢ[ℝ] H) (x : H) (N : ℕ) :
    ∑ j ∈ Finset.range N, ‖innovation U x j‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  -- Since $M_0 = H$, we have $∑_{j=0}^{N-1} innovation(j) = x - P_{M_N}(x)$.
  have h_sum : ∑ j ∈ Finset.range N, innovation U x j = x - (M U N).orthogonalProjection x := by
    induction N <;> simp_all +decide [ Finset.sum_range_succ ];
    · rw [ eq_comm, sub_eq_zero ];
      convert rfl;
      simp +decide [ Submodule.starProjection_eq_self_iff ];
      exact subset_closure ⟨ x, rfl ⟩;
    · simp +decide [ innovation, sub_add ];
  -- By Pythagoras' theorem, since the innovations are orthogonal, we have:
  have h_pyth : ‖∑ j ∈ Finset.range N, innovation U x j‖^2 = ∑ j ∈ Finset.range N, ‖innovation U x j‖^2 := by
    have h_orthogonal : ∀ i j : ℕ, i ≠ j → ⟪innovation U x i, innovation U x j⟫_ℝ = 0 :=
      fun i j hij => innovation_orthogonal U x hij;
    induction' N with N ih;
    · simp +decide;
    · induction' N + 1 with N ih <;> simp_all +decide [ Finset.sum_range_succ ];
      rw [ @norm_add_sq ℝ ];
      simp_all +decide [ inner_sum, sum_inner ];
      exact Finset.sum_eq_zero fun i hi => h_orthogonal i N ( ne_of_lt ( Finset.mem_range.mp hi ) );
  rw [ ← h_pyth, h_sum ];
  rw [ @norm_sub_sq ℝ ];
  have := ( M U N ).starProjection_inner_eq_zero x;
  specialize this ( ( M U N ).orthogonalProjection x ) ; simp_all +decide [ inner_sub_left, inner_sub_right ];
  linarith [ sq_nonneg ‖ ( M U N ).starProjection x‖ ]

/-
The MA coefficients are square-summable: `∑ ‖ε_j‖² < ∞`.
This follows from the bounded partial sums (`innovation_partial_sum_le`).
-/
theorem maCoeff_sq_summable (U : H →ₗᵢ[ℝ] H) (x : H) :
    Summable (fun j => maCoeff U x j ^ 2) := by
  refine' summable_of_sum_le _ _;
  exact ‖x‖ ^ 2;
  · exact fun _ => sq_nonneg _;
  · intro u;
    -- Let $N$ be the maximum element in the finite set $u$.
    obtain ⟨N, hN⟩ : ∃ N, ∀ j ∈ u, j ≤ N := by
      exact Finset.bddAbove u;
    exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( fun j hj => Finset.mem_range.mpr ( Nat.lt_succ_of_le ( hN j hj ) ) ) fun _ _ _ => sq_nonneg _ ) ( innovation_partial_sum_le U x ( N + 1 ) )

/-! ### Deterministic characterization -/

/-
A vector is deterministic (lies in the unitary subspace) if and only if its
MA component vanishes.
-/
theorem mem_unitarySubspace_iff_maComponent_zero (U : H →ₗᵢ[ℝ] H) (x : H) :
    x ∈ unitarySubspace U ↔ maComponent U x = 0 := by
  constructor;
  · intro hx
    unfold maComponent;
    rw [ sub_eq_zero, eq_comm ];
    exact Submodule.starProjection_eq_self_iff.mpr hx;
  · intro h;
    convert deterministicComponent_mem U x;
    exact eq_of_sub_eq_zero h

/-
A vector is purely nondeterministic (lies in the shift subspace) if and only if
its deterministic component vanishes.
-/
theorem mem_shiftSubspace_iff_deterministicComponent_zero (U : H →ₗᵢ[ℝ] H) (x : H) :
    x ∈ shiftSubspace U ↔ deterministicComponent U x = 0 := by
  constructor <;> intro h;
  · convert Submodule.orthogonalProjection_mem_subspace_eq_self _;
    rotate_left;
    exact ℝ;
    exact H;
    exact Real.instRCLike;
    exact inferInstance;
    exact inferInstance;
    exact ( unitarySubspace U );
    exact unitarySubspace_hasOrthogonalProjection U;
    exact 0;
    simp +decide [ deterministicComponent ];
    exact (starProjection_apply_eq_zero_iff (unitarySubspace U)).mpr h;
  · convert maComponent_mem U x;
    unfold maComponent; aesop;

/-! ### Isometry invariance -/

/-
The adjoint `U*` maps the unitary subspace into itself. Since `U* U = id` on `H`,
for any `d ∈ ⋂_n closure(range U^n)`, we have `U* d ∈ ⋂_n closure(range U^n)` because
`U*` maps `closure(range U^{n+1})` into `closure(range U^n)`.
-/
set_option maxHeartbeats 800000 in
theorem adjoint_unitarySubspace_invariant (U : H →ₗᵢ[ℝ] H) (d : H)
    (hd : d ∈ unitarySubspace U) :
    U.toContinuousLinearMap.adjoint d ∈ unitarySubspace U := by
  -- Since $U$.adjoint is an isometry and $d$ is in the unitary subspace, $U$.adjoint $d$ is also in the unitary subspace.
  have h_adj_unitary : ∀ (n : ℕ), d ∈ (U.toLinearMap ^ (n + 1)).range.topologicalClosure → (U.toContinuousLinearMap.adjoint d) ∈ (U.toLinearMap ^ n).range.topologicalClosure := by
    intro n hn
    obtain ⟨y, hy⟩ : ∃ y : ℕ → H, (∀ k, y k ∈ (U.toLinearMap ^ (n + 1)).range) ∧ Filter.Tendsto y Filter.atTop (nhds d) := by
      exact mem_closure_iff_seq_limit.mp hn;
    have h_adj_unitary : ∀ k, (U.toContinuousLinearMap.adjoint (y k)) ∈ (U.toLinearMap ^ n).range := by
      intro k
      obtain ⟨z, hz⟩ : ∃ z : H, y k = (U.toLinearMap ^ (n + 1)) z := by
        simpa [ eq_comm ] using hy.1 k;
      simp +decide [ hz, pow_succ', LinearMap.comp_apply ];
      use z;
      refine' ext_inner_right ℝ _;
      simp +decide [ ContinuousLinearMap.adjoint_inner_left ];
    exact mem_closure_of_tendsto ( Filter.Tendsto.comp ( ContinuousLinearMap.continuous _ |> Continuous.continuousAt ) hy.2 ) ( Filter.Eventually.of_forall h_adj_unitary );
  unfold unitarySubspace at *;
  simp_all +decide [ Submodule.mem_iInf ]

/-
`U` maps the shift subspace into itself. For `y ∈ (unitarySubspace)ᗮ` and
`d ∈ unitarySubspace`, `⟪U y, d⟫ = ⟪y, U* d⟫ = 0` since `U* d ∈ unitarySubspace`
by `adjoint_unitarySubspace_invariant`.
-/
theorem shiftSubspace_invariant (U : H →ₗᵢ[ℝ] H) (y : H)
    (hy : y ∈ shiftSubspace U) : U y ∈ shiftSubspace U := by
  intro d hd;
  convert hy ( U.toContinuousLinearMap.adjoint d ) ( adjoint_unitarySubspace_invariant U d hd ) using 1;
  rw [ ContinuousLinearMap.adjoint_inner_left ];
  rfl

/-
The deterministic component of `U x` is `U` applied to the deterministic component of `x`.
This reflects the time-shift invariance of the deterministic part.
-/
theorem deterministicComponent_commutes (U : H →ₗᵢ[ℝ] H) (x : H) :
    deterministicComponent U (U x) = U (deterministicComponent U x) := by
  apply Eq.symm;
  apply (decomposition_unique U (U x) (U (maComponent U x)) (U (deterministicComponent U x)) ?_ ?_ ?_).right;
  · apply shiftSubspace_invariant;
    exact maComponent_mem U x;
  · exact unitarySubspace_invariant U _ ( deterministicComponent_mem U x );
  · rw [ ← map_add, maComponent, sub_add_cancel ]

end Wold

end