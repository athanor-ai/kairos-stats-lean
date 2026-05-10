import Mathlib

-- Error propagation bounds through a pipeline of operations.
-- General framework: each stage has an error model,
-- the pipeline error is the composition.
-- Unifies all Pythia numerical error theorems.

noncomputable section

-- A stage with input type α and error bound
structure ErrorStage where
  bound : ℝ  -- relative error bound
  h_nonneg : 0 ≤ bound

-- Pipeline error composition: n stages
def pipelineError (stages : List ErrorStage) : ℝ :=
  stages.foldl (fun acc s => acc + s.bound + acc * s.bound) 0

/-
Helper: the fold function preserves nonnegativity
-/
private lemma foldl_nonneg (stages : List ErrorStage) (init : ℝ) (h_init : 0 ≤ init) :
    0 ≤ stages.foldl (fun acc s => acc + s.bound + acc * s.bound) init := by
  induction' stages using List.reverseRecOn with stages s ih <;> simp +decide [ * ];
  nlinarith [ s.h_nonneg ]

-- Pipeline error is nonneg
theorem pipeline_error_nonneg (stages : List ErrorStage) :
    0 ≤ pipelineError stages := by
  exact foldl_nonneg stages 0 le_rfl

/-
Helper: foldl is monotone in initial value
-/
private lemma foldl_mono (stages : List ErrorStage) (a b : ℝ) (_ha : 0 ≤ a) (hab : a ≤ b) :
    stages.foldl (fun acc s => acc + s.bound + acc * s.bound) a ≤
    stages.foldl (fun acc s => acc + s.bound + acc * s.bound) b := by
  induction stages using List.reverseRecOn <;> simp_all +decide;
  gcongr;
  exact ErrorStage.h_nonneg _

-- Helper: foldl append singleton
private lemma foldl_append_singleton (stages : List ErrorStage) (s : ErrorStage) (init : ℝ) :
    (stages ++ [s]).foldl (fun acc s => acc + s.bound + acc * s.bound) init =
    let mid := stages.foldl (fun acc s => acc + s.bound + acc * s.bound) init
    mid + s.bound + mid * s.bound := by
  simp [List.foldl_append]

-- Adding a stage increases error
theorem pipeline_error_mono (stages : List ErrorStage) (s : ErrorStage) :
    pipelineError stages ≤ pipelineError (stages ++ [s]) := by
  unfold pipelineError
  rw [foldl_append_singleton]
  simp only
  have h1 := foldl_nonneg stages 0 le_rfl
  have h2 := s.h_nonneg
  linarith [mul_nonneg h1 h2]

/-
The original theorem statement below is FALSE:
A counterexample: 3 stages with bound = 1 gives pipelineError = 7 > 6 = 2 * sum.
theorem pipeline_error_first_order (stages : List ErrorStage)
(h_small : ∀ s ∈ stages, s.bound ≤ 1) :
pipelineError stages ≤ 2 * (stages.map ErrorStage.bound).sum := by sorry

Corrected first-order approximation: pipeline error ≤ 2^n * sum of stage errors
when individual errors are at most 1. The original `2 * sum` bound is false for ≥ 3 stages
(counterexample: three stages with bound 1 give pipeline error 7 > 6 = 2 × 3).
The proof uses induction, bounding `acc * s.bound ≤ acc` (since `s.bound ≤ 1`).
-/
theorem pipeline_error_first_order (stages : List ErrorStage)
    (h_small : ∀ s ∈ stages, s.bound ≤ 1) :
    pipelineError stages ≤ 2 ^ stages.length * (stages.map ErrorStage.bound).sum := by
  -- Now let's generalize the induction step to show the bound holds for any initial value `init` and bound `hx`.
  have inductive_step (stages : List ErrorStage) (init : ℝ)
    (hx : 0 ≤ init) (h_small : (∀ s ∈ stages, s.bound ≤ 1)) :
    stages.foldl (fun acc s => acc + s.bound + acc * s.bound) init ≤
    2 ^ stages.length * (init + (stages.map ErrorStage.bound).sum) := by
      induction' stages using List.reverseRecOn with stages s ih generalizing init <;> simp_all +decide [ pow_succ', mul_assoc ];
      nlinarith [ ih init hx, h_small s ( Or.inr rfl ), show 0 ≤ List.foldl ( fun acc s => acc + s.bound + acc * s.bound ) init stages from by exact foldl_nonneg _ _ hx, show 0 ≤ s.bound from by exact s.h_nonneg, show ( 2 : ℝ ) ^ stages.length ≥ 1 from one_le_pow₀ ( by norm_num ) ];
  simpa using inductive_step stages 0 le_rfl h_small

end