import Mathlib

-- Clock divider: output toggles every N input clock cycles.
-- State machine: counter mod N, output toggles when counter wraps.

structure ClockDivState where
  counter : ℕ
  output : Bool

def clockDivStep (N : ℕ) (s : ClockDivState) : ClockDivState :=
  if s.counter + 1 = N then
    { counter := 0, output := !s.output }
  else
    { counter := s.counter + 1, output := s.output }

def clockDivInit : ClockDivState := { counter := 0, output := false }

noncomputable def clockDivAfter (N : ℕ) : ℕ → ClockDivState
  | 0 => clockDivInit
  | t + 1 => clockDivStep N (clockDivAfter N t)

/-
Counter is always < N (when N > 0)
-/
theorem counter_lt_N (N : ℕ) (hN : 0 < N) (t : ℕ) :
    (clockDivAfter N t).counter < N := by
  induction' t with t ih;
  · exact hN;
  · rw [ show clockDivAfter N ( t + 1 ) = clockDivStep N ( clockDivAfter N t ) from rfl ];
    unfold clockDivStep;
    grind

/-
Helper: if counter = j < N and j + 1 ≠ N, then after one step counter = j + 1 and output unchanged
-/
lemma clockDivStep_not_wrap (N : ℕ) (s : ClockDivState) (h : s.counter + 1 ≠ N) :
    (clockDivStep N s).counter = s.counter + 1 ∧ (clockDivStep N s).output = s.output := by
  unfold clockDivStep; aesop

/-
Helper: if counter + 1 = N, then after one step counter = 0 and output toggled
-/
lemma clockDivStep_wrap (N : ℕ) (s : ClockDivState) (h : s.counter + 1 = N) :
    (clockDivStep N s).counter = 0 ∧ (clockDivStep N s).output = !s.output := by
  unfold clockDivStep; aesop;

/-
Helper: during the middle of a period (j < N, counter starts at 0),
counter = j and output unchanged
-/
lemma counter_during_period (N : ℕ) (hN : 0 < N) (t j : ℕ) (hj : j < N)
    (hc : (clockDivAfter N t).counter = 0) :
    (clockDivAfter N (t + j)).counter = j ∧
    (clockDivAfter N (t + j)).output = (clockDivAfter N t).output := by
  induction' j with j ih;
  · aesop;
  · rw [ Nat.add_succ, show clockDivAfter N ( t + j + 1 ) = clockDivStep N ( clockDivAfter N ( t + j ) ) from rfl ] ; specialize ih ( Nat.lt_of_succ_lt hj ) ; simp_all +decide [ clockDivStep ] ;
    grind

/-
Helper: after exactly N steps from counter=0, counter resets and output toggles
-/
lemma output_toggle_after_N (N : ℕ) (hN : 0 < N) (t : ℕ)
    (hc : (clockDivAfter N t).counter = 0) :
    (clockDivAfter N (t + N)).counter = 0 ∧
    (clockDivAfter N (t + N)).output = !(clockDivAfter N t).output := by
  -- Apply the counter_during_period lemma to show that the output remains unchanged.
  have h_output_unchanged : (clockDivAfter N (t + (N - 1))).counter = N - 1 ∧ (clockDivAfter N (t + (N - 1))).output = (clockDivAfter N t).output := by
    apply counter_during_period N hN t (N - 1) (by
    exact Nat.pred_lt hN.ne') hc;
  rcases N with ( _ | _ | N ) <;> simp_all +arith +decide;
  · exact ⟨ by rw [ show clockDivAfter 1 ( t + 1 ) = clockDivStep 1 ( clockDivAfter 1 t ) from rfl ] ; unfold clockDivStep; aesop, by rw [ show clockDivAfter 1 ( t + 1 ) = clockDivStep 1 ( clockDivAfter 1 t ) from rfl ] ; unfold clockDivStep; aesop ⟩;
  · rw [ show clockDivAfter ( N + 2 ) ( t + N + 2 ) = clockDivStep ( N + 2 ) ( clockDivAfter ( N + 2 ) ( t + N + 1 ) ) from rfl ] ; simp_all +decide [ clockDivStep ] ;

/-
Helper: counter is 0 at every multiple of N
-/
lemma counter_at_multiple (N : ℕ) (hN : 0 < N) (k : ℕ) :
    (clockDivAfter N (k * N)).counter = 0 := by
  induction' k with k ih;
  · aesop;
  · convert output_toggle_after_N N hN ( k * N ) ih |>.1 using 1;
    rw [ Nat.succ_mul ]

/-
Output toggles exactly at multiples of N
Note: `Nat.even` was corrected to `Odd` since the output starts at `false`
and toggles at each multiple of N, so at step k*N the output is true iff k is odd.
-/
theorem output_at_multiple (N : ℕ) (hN : 0 < N) (k : ℕ) :
    (clockDivAfter N (k * N)).output = decide (Odd k) := by
  induction' k with k ih;
  · aesop;
  · rw [ Nat.succ_mul ];
    rw [ output_toggle_after_N N hN ( k * N ) ( counter_at_multiple N hN k ) |>.2, ih ] ; simp +decide [ parity_simps ];
    grind

/-
Output is stable between toggles
-/
theorem output_stable (N : ℕ) (hN : 1 < N) (t : ℕ)
    (h : (clockDivAfter N t).counter + 1 ≠ N) :
    (clockDivAfter N (t + 1)).output = (clockDivAfter N t).output := by
  exact ( clockDivStep_not_wrap N ( clockDivAfter N t ) h ) |>.2