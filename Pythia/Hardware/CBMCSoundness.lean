import Mathlib

-- CBMC (C Bounded Model Checker) Soundness — Kroening et al.
-- CBMC unwinds loops up to a bound k, converts to a SAT formula (via SSA),
-- and checks satisfiability. If SAT → real counterexample exists.
-- If UNSAT → no assertion violation within bound k.
--
-- We model:
--   • Programs as transition systems (same style as IC3PDRSoundness.lean)
--   • Loop unwinding as explicit bounded unrolling producing a finite trace tree
--   • SAT formula soundness: a satisfying assignment maps to a concrete execution
--
-- Reference: Kroening & Strichman, "Decision Procedures", Ch. 9;
--            Clarke et al., TACAS 2004.

namespace Pythia.Hardware.CBMCSoundness

/-! ## Transition System -/

/-- A program modelled as a labelled transition system.
    - `State`  : program state (variables + PC)
    - `init`   : initial states
    - `next`   : single-step transition relation
    - `assert` : the safety assertion that must hold at every step
-/
structure CBMCSystem (State : Type*) where
  init   : State → Prop
  next   : State → State → Prop
  assert : State → Prop

/-! ## Execution Traces -/

/-- A *trace of length n* is a function `Fin (n+1) → State` — the (n+1) states
    visited.  Step `i` goes from `trace i.castSucc` to `trace i.succ`. -/
def isTrace {State : Type*} (sys : CBMCSystem State)
    (n : ℕ) (trace : Fin (n + 1) → State) : Prop :=
  sys.init (trace 0) ∧
  ∀ i : Fin n, sys.next (trace i.castSucc) (trace i.succ)

/-- An assertion violation at step `m` of trace `trace`. -/
def violatesAt {State : Type*} (sys : CBMCSystem State)
    (n : ℕ) (trace : Fin (n + 1) → State) (m : Fin (n + 1)) : Prop :=
  isTrace sys n trace ∧ ¬sys.assert (trace m)

/-! ## Loop Unwinding -/

/-- The *unwound program at depth k* accepts exactly the traces of the original
    program whose length is `≤ k`.  We represent it simply as the predicate
    `unwindedProg`. -/
def unwindedProg {State : Type*} (sys : CBMCSystem State) (k : ℕ)
    (n : ℕ) (trace : Fin (n + 1) → State) : Prop :=
  n ≤ k ∧ isTrace sys n trace

/-! ## SAT Formula Abstraction -/

/-- A *SAT formula* for bound `k` is, abstractly, a predicate on assignments.
    We represent an assignment as a function from `ℕ × ℕ` (time × variable
    index) to `Bool` — thin enough for the proofs below while capturing the
    essential structure of CBMC's SSA encoding. -/
def Assignment := ℕ × ℕ → Bool

/-- The CBMC SAT encoding relates an assignment to a concrete execution trace.
    `satEncodes sys k asgn trace` means:
      (a) `trace` is a valid execution of length ≤ k, AND
      (b) the assignment faithfully decodes to `trace`.
    In a full CBMC implementation (b) is enforced by the SSA construction;
    here we axiomatise it as a hypothesis so the soundness proofs remain
    purely propositional. -/
structure SATEncoding (State : Type*) (sys : CBMCSystem State) (k : ℕ) where
  /-- Extract a trace length from an assignment. -/
  traceLen    : Assignment → ℕ
  /-- Extract a state at time `t` from an assignment. -/
  traceState  : Assignment → ℕ → State
  /-- The encoding is *faithful*: every assignment encodes a valid unwound trace. -/
  faithful    : ∀ (asgn : Assignment),
    traceLen asgn ≤ k ∧
    sys.init (traceState asgn 0) ∧
    ∀ i : Fin (traceLen asgn),
      sys.next (traceState asgn i.castSucc) (traceState asgn i.succ)
  /-- The assertion-violation flag in the assignment correctly reflects a
      violation somewhere in the decoded trace. -/
  violation   : ∀ (asgn : Assignment),
    (∃ t : Fin (traceLen asgn + 1), ¬sys.assert (traceState asgn t)) ↔
    (∃ t : ℕ, t ≤ traceLen asgn ∧ ¬sys.assert (traceState asgn t))

/-! ## Theorem 1 — Counterexample Soundness -/

/-- **cbmc_counterexample_sound**: If CBMC finds a counterexample
    (the SAT formula is satisfiable *and* a violation flag is set),
    then there exists a real program execution of length ≤ k that
    violates the assertion. -/
theorem cbmc_counterexample_sound
    {State : Type*}
    (sys : CBMCSystem State)
    (k : ℕ)
    (enc : SATEncoding State sys k)
    -- A satisfying assignment that witnesses a violation
    (asgn : Assignment)
    (h_viol : ∃ t : ℕ, t ≤ enc.traceLen asgn ∧ ¬sys.assert (enc.traceState asgn t)) :
    ∃ (n : ℕ) (trace : Fin (n + 1) → State),
      n ≤ k ∧
      isTrace sys n trace ∧
      ∃ m : Fin (n + 1), ¬sys.assert (trace m) := by
  obtain ⟨h_len, h_init, h_steps⟩ := enc.faithful asgn
  obtain ⟨t, ht_le, ht_bad⟩ := h_viol
  -- Build the concrete trace from the assignment
  let n := enc.traceLen asgn
  -- The trace function mapping Fin (n+1) → State
  let trace : Fin (n + 1) → State := fun i => enc.traceState asgn i.val
  refine ⟨n, trace, h_len, ?_, ?_⟩
  · -- isTrace
    constructor
    · exact h_init
    · intro i
      exact h_steps i
  · -- violation witness
    refine ⟨⟨t, by omega⟩, ?_⟩
    exact ht_bad

/-! ## Theorem 2 — Safe Soundness -/

/-- **cbmc_safe_sound**: If CBMC returns SAFE (no satisfying assignment
    encodes a violation), then no assertion violation exists within bound k. -/
theorem cbmc_safe_sound
    {State : Type*}
    (sys : CBMCSystem State)
    (k : ℕ)
    (enc : SATEncoding State sys k)
    -- CBMC found no violation in any assignment
    (h_no_cex : ∀ (asgn : Assignment),
      ∀ t : ℕ, t ≤ enc.traceLen asgn → sys.assert (enc.traceState asgn t))
    -- Every valid execution trace of length ≤ k is captured by some assignment
    (h_complete : ∀ (n : ℕ) (trace : Fin (n + 1) → State),
      n ≤ k →
      isTrace sys n trace →
      ∃ asgn : Assignment,
        enc.traceLen asgn = n ∧
        ∀ i : ℕ, (hi : i ≤ n) → enc.traceState asgn i = trace ⟨i, Nat.lt_succ_of_le hi⟩) :
    ∀ (n : ℕ) (trace : Fin (n + 1) → State),
      n ≤ k →
      isTrace sys n trace →
      ∀ m : Fin (n + 1), sys.assert (trace m) := by
  intro n trace hn h_trace m
  obtain ⟨asgn, h_len, h_eq⟩ := h_complete n trace hn h_trace
  have h_val : m.val ≤ n := Nat.lt_succ_iff.mp m.isLt
  have h_assert := h_no_cex asgn m.val (h_len ▸ h_val)
  have h_decode := h_eq m.val h_val
  rw [h_decode] at h_assert
  exact h_assert

/-! ## Theorem 3 — Unwinding Preserves Semantics -/

/-- **cbmc_unwinding_preserves_semantics**: The unwound program at depth k
    faithfully represents all executions of the original program up to length k.
    More precisely, `unwindedProg sys k` accepts exactly the traces of
    `isTrace sys` whose length is ≤ k. -/
theorem cbmc_unwinding_preserves_semantics
    {State : Type*}
    (sys : CBMCSystem State)
    (k : ℕ) :
    ∀ (n : ℕ) (trace : Fin (n + 1) → State),
      unwindedProg sys k n trace ↔ (n ≤ k ∧ isTrace sys n trace) := by
  intros n trace
  -- unwindedProg is defined as exactly this conjunction
  rfl

/-! ## Theorem 4 — SAT Assignment Maps to Reachable State -/

/-- **cbmc_sat_implies_reachable**: A satisfying assignment under the CBMC
    encoding maps to a concrete state that is reachable in the original
    program within bound k. -/
theorem cbmc_sat_implies_reachable
    {State : Type*}
    (sys : CBMCSystem State)
    (k : ℕ)
    (enc : SATEncoding State sys k)
    (asgn : Assignment)
    (t : ℕ)
    (ht : t ≤ enc.traceLen asgn) :
    ∃ (n : ℕ) (hn_le : t ≤ n) (trace : Fin (n + 1) → State),
      n ≤ k ∧
      isTrace sys n trace ∧
      enc.traceState asgn t = trace ⟨t, Nat.lt_succ_of_le hn_le⟩ := by
  obtain ⟨h_len, h_init, h_steps⟩ := enc.faithful asgn
  exact ⟨enc.traceLen asgn, ht,
         fun i => enc.traceState asgn i.val,
         h_len, ⟨h_init, h_steps⟩, rfl⟩

/-! ## Corollary — Completeness of Bounded Checking -/

/-- **cbmc_bounded_completeness**: CBMC is *complete* for bounded depth:
    if a violation exists within depth k, CBMC will find it (assuming the
    encoding is complete). -/
theorem cbmc_bounded_completeness
    {State : Type*}
    (sys : CBMCSystem State)
    (k : ℕ)
    (enc : SATEncoding State sys k)
    -- Encoding completeness: every concrete violation maps back to an assignment
    (h_complete : ∀ (n : ℕ) (trace : Fin (n + 1) → State) (m : Fin (n + 1)),
      n ≤ k →
      isTrace sys n trace →
      ¬sys.assert (trace m) →
      ∃ asgn : Assignment,
        ∃ t : ℕ, t ≤ enc.traceLen asgn ∧ ¬sys.assert (enc.traceState asgn t))
    -- There exists a concrete violation within depth k
    (h_viol : ∃ (n : ℕ) (trace : Fin (n + 1) → State) (m : Fin (n + 1)),
      n ≤ k ∧ isTrace sys n trace ∧ ¬sys.assert (trace m)) :
    ∃ (asgn : Assignment),
      ∃ t : ℕ, t ≤ enc.traceLen asgn ∧ ¬sys.assert (enc.traceState asgn t) := by
  obtain ⟨n, trace, m, hn, h_tr, h_bad⟩ := h_viol
  exact h_complete n trace m hn h_tr h_bad

end Pythia.Hardware.CBMCSoundness
