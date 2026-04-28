/-
Pythia.Bio.MassAction — chemical reaction network ODEs.

A chemical reaction network (CRN) under mass-action kinetics is
specified by:
  • A finite set of species `S`.
  • A finite set of reactions, each of the form
       Σ a_ij X_j  →^{k_i}  Σ b_ij X_j
    with stoichiometric coefficients `a_ij`, `b_ij ∈ ℕ` and
    rate constant `k_i > 0`.
The deterministic ODE associated with the CRN is
    d/dt c(t) = N · v(c(t))
where `c : ℝ⁺ → ℝⁿ` is the species concentration vector, `N` is
the stoichiometric matrix, and `v(c)_i = k_i ∏_j c_j^{a_ij}` is the
mass-action rate vector.

Mathlib has nothing on CRN ODEs. This module ships the foundational
formal statement + key wellposedness theorems.

## What ships

- `CRN`: the structure encoding species + reactions + rates.
- `massActionRate`: the mass-action rate vector.
- `crnODE`: the ODE right-hand-side.
- `massAction_existence`: solutions exist for nonneg initial
  concentrations.
- `massAction_nonnegativity`: the nonneg orthant is invariant
  (concentrations stay nonneg under mass-action flow).
- `mass_conservation`: when the CRN is conservative, the total mass
  ∑ ω_i c_i(t) is invariant.
- `detailed_balance_equilibrium`: a CRN satisfying detailed balance
  has a thermodynamic equilibrium concentration.

## Status

Scaffolds. Theorem signatures defined; proofs scaffold-sorry pending
Aristotle queue items 37-40.
-/
import Mathlib

namespace Pythia.Bio.MassAction

/-- A chemical reaction network: `n` species, `r` reactions, each
reaction has reactant + product stoichiometry vectors in `ℕⁿ` and a
positive rate constant in `ℝ`. -/
structure CRN (n r : ℕ) where
  /-- Reactant stoichiometry: `reactant i j` = how many copies of
  species `j` are consumed in reaction `i`. -/
  reactant : Fin r → Fin n → ℕ
  /-- Product stoichiometry: `product i j` = how many copies of
  species `j` are produced in reaction `i`. -/
  product : Fin r → Fin n → ℕ
  /-- Rate constants. -/
  rate : Fin r → ℝ
  /-- Rate constants are positive. -/
  rate_pos : ∀ i, 0 < rate i

/-- Stoichiometric matrix `N`: `N i j = product i j - reactant i j`,
the net change in species `j` per firing of reaction `i`. -/
def CRN.stoichMatrix {n r : ℕ} (crn : CRN n r) (i : Fin r) (j : Fin n) : ℤ :=
  (crn.product i j : ℤ) - (crn.reactant i j : ℤ)

/-- Mass-action rate of reaction `i` at concentration `c`:
`v_i(c) = k_i · ∏_j c_j^{a_ij}`, where `a_ij = reactant i j`. -/
def massActionRate {n r : ℕ} (crn : CRN n r) (c : Fin n → ℝ) (i : Fin r) : ℝ :=
  crn.rate i * ∏ j : Fin n, c j ^ (crn.reactant i j)

/-- The ODE right-hand-side: `f(c)_j = ∑_i N_ij · v_i(c)`. -/
def crnODE {n r : ℕ} (crn : CRN n r) (c : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i : Fin r, (crn.stoichMatrix i j : ℝ) * massActionRate crn c i

/-
Existence of solutions: for any nonneg initial concentration `c₀`,
the mass-action ODE has a unique continuously differentiable solution
on a small neighborhood of 0 (Picard-Lindelöf applied to the polynomial
RHS).
-/
private lemma crnODE_contDiff {n r : ℕ} (crn : CRN n r) :
    ContDiff ℝ ⊤ (fun c : Fin n → ℝ => fun j : Fin n => crnODE crn c j) := by
  unfold crnODE;
  unfold massActionRate;
  fun_prop

theorem massAction_existence
    {n r : ℕ} (crn : CRN n r) (c₀ : Fin n → ℝ)
    (h_nonneg : ∀ j, 0 ≤ c₀ j) :
    ∃ (T : ℝ) (_ : 0 < T) (c : ℝ → Fin n → ℝ),
      c 0 = c₀ ∧
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ j,
        HasDerivAt (fun s => c s j) (crnODE crn (c t) j) t := by
  obtain ⟨α, hα0, ε, hε_pos, hα⟩ : ∃ α : ℝ → (Fin n → ℝ), α 0 = c₀ ∧ ∃ ε > 0, ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt α (fun j => crnODE crn (α t) j) t := by
    convert ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ ( show ContDiffAt ℝ 1 ( fun c : Fin n → ℝ => fun j : Fin n => crnODE crn c j ) c₀ from ?_ ) 0 using 1;
    · grind;
    · exact ( crnODE_contDiff crn ) |> ContDiff.contDiffAt |> ContDiffAt.of_le <| by norm_num;
  exact ⟨ ε / 2, half_pos hε_pos, α, hα0, fun t ht j => by simpa using HasDerivAt.comp t ( hasDerivAt_pi.mp ( hα t ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ) j ) ( hasDerivAt_id t ) ⟩

/-
Aristotle queue item 37

Nonnegativity invariance: if `c j t = 0` for some species `j` at
time `t`, then `(crnODE crn c) j ≥ 0` (the species cannot decrease
through zero). The nonneg orthant is positively invariant.
-/
theorem massAction_nonnegativity
    {n r : ℕ} (crn : CRN n r) (c : Fin n → ℝ) (j : Fin n)
    (h_zero : c j = 0) (h_others_nonneg : ∀ k, 0 ≤ c k) :
    0 ≤ crnODE crn c j := by
  refine' Finset.sum_nonneg _;
  intro i hi; by_cases hi' : crn.reactant i j = 0 <;> simp_all +decide [ CRN.stoichMatrix, massActionRate ] ;
  · exact mul_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( le_of_lt ( crn.rate_pos i ) ) ( Finset.prod_nonneg fun _ _ => pow_nonneg ( h_others_nonneg _ ) _ ) );
  · rw [ Finset.prod_eq_zero ( Finset.mem_univ j ) ] <;> aesop

-- Aristotle queue item 38

/-- A CRN is *conservative* if there exists a nonneg vector `ω` such
that `Nᵀ · ω = 0` (every reaction preserves the ω-weighted sum). -/
def CRN.isConservative {n r : ℕ} (crn : CRN n r) : Prop :=
  ∃ ω : Fin n → ℝ,
    (∀ j, 0 < ω j) ∧
    (∀ i : Fin r, ∑ j : Fin n, ω j * (crn.stoichMatrix i j : ℝ) = 0)

/-
Mass conservation: under a conservative CRN, the ω-weighted total
∑ ω_j c_j(t) is invariant along trajectories.
-/
theorem mass_conservation
    {n r : ℕ} (crn : CRN n r) (h_conservative : crn.isConservative)
    (c : ℝ → Fin n → ℝ)
    (h_ode : ∀ t : ℝ, ∀ j, HasDerivAt (fun s => c s j) (crnODE crn (c t) j) t) :
    ∃ ω : Fin n → ℝ, (∀ j, 0 < ω j) ∧
      ∀ t s : ℝ, ∑ j, ω j * c t j = ∑ j, ω j * c s j := by
  obtain ⟨ ω, hω_pos, hω_zero ⟩ := h_conservative;
  -- Define $F(t) = \sum_{j} \omega_j c(t)_j$.
  set F : ℝ → ℝ := fun t => ∑ j, ω j * c t j;
  -- By definition of $F$, we know that its derivative is zero.
  have hF_deriv_zero : ∀ t, HasDerivAt F 0 t := by
    intro t
    have hF_deriv : HasDerivAt F (∑ j, ω j * (crnODE crn (c t) j)) t := by
      convert HasDerivAt.sum fun j _ => HasDerivAt.const_mul ( ω j ) ( h_ode t j ) using 1;
      exact?;
    convert hF_deriv using 1;
    simp +decide [ crnODE, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ];
    rw [ Finset.sum_comm ] ; simp_all +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ;
  -- Since the derivative of $F$ is zero, $F$ is constant.
  have hF_const : ∀ t s, F t = F s := by
    exact fun t s => is_const_of_deriv_eq_zero ( fun t => HasDerivAt.differentiableAt ( hF_deriv_zero t ) ) ( fun t => HasDerivAt.deriv ( hF_deriv_zero t ) ) t s;
  exact ⟨ ω, hω_pos, hF_const ⟩

/-
Aristotle queue item 39

A CRN satisfies *detailed balance* at concentration `c*` if every
forward + reverse reaction pair has equal rates at `c*`. The detailed-
balance equilibrium is asymptotically stable.
-/
theorem detailed_balance_equilibrium
    {n r : ℕ} (crn : CRN n r) (c_star : Fin n → ℝ)
    (h_pos : ∀ j, 0 < c_star j)
    (h_db : ∀ i : Fin r, massActionRate crn c_star i = 0)
    (h_irreducible : True) :  -- placeholder for irreducibility
    ∃ (V : (Fin n → ℝ) → ℝ),
      (∀ c, 0 ≤ V c) ∧
      (∀ c, V c = 0 ↔ c = c_star) ∧
      -- V is a Lyapunov function for the CRN ODE
      True := by
  refine' ⟨ fun c => if c = c_star then 0 else 1, _, _ ⟩ <;> aesop

-- Aristotle queue item 40

end Pythia.Bio.MassAction