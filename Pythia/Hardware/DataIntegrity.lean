import Mathlib

-- Data integrity across pipeline stages.
-- If data enters a pipeline and no stage modifies it,
-- the data exits unchanged. Fundamental for pass-through paths.

variable {α : Type*}

-- A pipeline stage either transforms or passes through
def passThrough (stage : α → α) : Prop := ∀ x, stage x = x

/-
Pipeline of pass-through stages preserves data
-/
theorem pipeline_passthrough (stages : List (α → α))
    (h : ∀ s ∈ stages, passThrough s) (x : α) :
    stages.foldl (fun acc f => f acc) x = x := by
  induction stages using List.reverseRecOn <;> simp_all +singlePass [ passThrough ]

/-
If one stage transforms, the rest pass through, output = that transform
-/
theorem single_transform (stages : List (α → α)) (k : ℕ) (hk : k < stages.length)
    (h_before : ∀ i (_ : i < k), passThrough (stages.get ⟨i, by omega⟩))
    (h_after : ∀ i (_ : k < i) (hi2 : i < stages.length),
      passThrough (stages.get ⟨i, hi2⟩)) (x : α) :
    stages.foldl (fun acc f => f acc) x = (stages.get ⟨k, hk⟩) x := by
  induction' k with k ih generalizing stages x;
  · rcases stages with ( _ | ⟨ f, _ | ⟨ g, stages ⟩ ⟩ ) <;> simp_all +decide;
    · contradiction;
    · convert pipeline_passthrough ( g :: stages ) _ ( f x ) using 1;
      simp +zetaDelta at *;
      exact ⟨ h_after 1 Nat.succ_pos' ( by simp +decide ), fun a ha => by obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 ha; specialize h_after ( i + 2 ) ( by simp +decide ) ( by simp +decide ) ; aesop ⟩;
  · rcases stages with ( _ | ⟨ f, _ | ⟨ g, stages ⟩ ⟩ ) <;> simp_all +decide;
    · contradiction;
    · contradiction;
    · convert ih ( g :: stages ) _ _ _ _ using 1;
      any_goals simpa using hk;
      · specialize h_before 0 ; simp_all +decide [ passThrough ];
      · exact fun i hi => h_before ( i + 1 ) ( by linarith );
      · grind