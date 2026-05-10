import Mathlib

-- Crossbar switch non-blocking property.
-- An NxN crossbar can route any permutation of inputs to outputs
-- without contention. Fundamental for NoC and interconnect design.

variable {n : ℕ}

-- A crossbar configuration is a permutation of outputs
def isValidConfig (config : Fin n → Fin n) : Prop :=
  Function.Injective config

-- Any permutation is a valid crossbar config
theorem any_perm_valid (σ : Equiv.Perm (Fin n)) :
    isValidConfig σ :=
  σ.injective

/-
Non-blocking: for any set of active ports, a valid config exists
-/
theorem crossbar_nonblocking (active : Finset (Fin n))
    (targets : Fin n → Fin n) (h_inj : Function.Injective (fun i : active => targets i)) :
    ∃ config : Fin n → Fin n, isValidConfig config ∧
      ∀ i ∈ active, config i = targets i := by
  by_contra! h_contra;
  -- Let $S$ be the set of all indices that are not in `active`.
  set S := Finset.univ \ active with hS_def;
  -- Let $T$ be the set of all indices that are not in the image of `targets` on `active`.
  set T := Finset.univ \ Finset.image targets active with hT_def;
  -- Since $|S| = |T|$, there exists a bijection $f : S \to T$.
  obtain ⟨f, hf_bij⟩ : ∃ f : S ≃ T, True := by
    have h_card_eq : Finset.card S = Finset.card T := by
      rw [ Finset.card_sdiff, Finset.card_sdiff ] ; norm_num [ Finset.card_image_of_injective _ h_inj ];
      rw [ Finset.card_image_of_injOn ];
      exact fun x hx y hy hxy => by have := @h_inj ⟨ x, hx ⟩ ⟨ y, hy ⟩ ; aesop;
    exact ⟨ Fintype.equivOfCardEq <| by simpa [ Fintype.card_subtype ] using h_card_eq, trivial ⟩;
  refine' h_contra ( fun i => if hi : i ∈ active then targets i else f ⟨ i, by aesop ⟩ ) _ |> fun ⟨ i, hi, hi' ⟩ => hi' <| _;
  · intro i j hij;
    by_cases hi : i ∈ active <;> by_cases hj : j ∈ active <;> simp_all +decide;
    · have := @h_inj ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; aesop;
    · grind;
    · grind;
  · aesop

/-
Two disjoint requests can be served simultaneously
-/
theorem crossbar_parallel_service (i j : Fin n) (ti tj : Fin n)
    (h_ports : i ≠ j) (h_targets : ti ≠ tj) :
    ∃ config : Fin n → Fin n, config i = ti ∧ config j = tj := by
  exact ⟨ fun x => if x = i then ti else if x = j then tj else x, by aesop ⟩