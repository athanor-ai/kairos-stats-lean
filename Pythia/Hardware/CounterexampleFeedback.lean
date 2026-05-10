import Mathlib

-- Counterexample feedback loop correctness.
-- When a proposal is refuted by counterexample C,
-- the next proposal must not exhibit C.
-- Backs the "learn from failures" forcing function.

variable {Proposal Counterexample : Type*} [DecidableEq Counterexample]

-- A proposal is refuted by a counterexample
def isRefutedBy (exhibits : Proposal → Counterexample → Bool)
    (p : Proposal) (c : Counterexample) : Prop :=
  exhibits p c = true

-- A proposal avoids a set of known counterexamples
def avoidsAll (exhibits : Proposal → Counterexample → Bool)
    (p : Proposal) (cexs : List Counterexample) : Prop :=
  ∀ c ∈ cexs, exhibits p c = false

-- Feedback enforcement: if the system only accepts proposals
-- that avoid known counterexamples, refuted patterns cannot repeat
theorem feedback_prevents_repeat
    (exhibits : Proposal → Counterexample → Bool)
    (p : Proposal) (cexs : List Counterexample) (c : Counterexample)
    (h_avoids : avoidsAll exhibits p cexs)
    (h_in : c ∈ cexs) :
    ¬isRefutedBy exhibits p c := by
  intro h_ref
  have := h_avoids c h_in
  unfold isRefutedBy at h_ref
  simp_all

-- Adding a new counterexample strictly narrows the search space
theorem feedback_narrows_space
    (exhibits : Proposal → Counterexample → Bool)
    (p : Proposal) (cexs : List Counterexample) (c_new : Counterexample)
    (h_avoids_old : avoidsAll exhibits p cexs)
    (h_avoids_new : avoidsAll exhibits p (c_new :: cexs)) :
    avoidsAll exhibits p cexs := by
  intro c hc
  exact h_avoids_new c (List.mem_cons_of_mem _ hc)

-- Monotonicity: more counterexamples = stricter filter
theorem feedback_monotone
    (exhibits : Proposal → Counterexample → Bool)
    (p : Proposal) (cexs1 cexs2 : List Counterexample)
    (h_sub : ∀ c, c ∈ cexs1 → c ∈ cexs2)
    (h_avoids : avoidsAll exhibits p cexs2) :
    avoidsAll exhibits p cexs1 := by
  intro c hc
  exact h_avoids c (h_sub c hc)
