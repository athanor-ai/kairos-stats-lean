/-
Copyright (c) 2024 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia

Pythia.Hardware.FIFOOrdering — FIFO ordering invariant.

A FIFO queue modelled as a `List α` with:
  - push : append to tail
  - pop  : remove from head

The fundamental invariant: data comes out in the same order it went in.
-/

import Mathlib

namespace Pythia.Hardware.FIFOOrdering

/-! ## FIFO operations -/

/-- Push an element onto the tail of the FIFO. -/
def fifoPush (fifo : List α) (x : α) : List α := fifo ++ [x]

/-- Pop an element from the head of the FIFO.
    Returns `(some head, tail)` for a non-empty FIFO, or `(none, [])` for empty. -/
def fifoPop (fifo : List α) : Option α × List α :=
  match fifo with
  | [] => (none, [])
  | h :: t => (some h, t)

/-! ## Basic lemmas -/

@[simp]
lemma fifoPush_def (fifo : List α) (x : α) : fifoPush fifo x = fifo ++ [x] := rfl

@[simp]
lemma fifoPop_nil : fifoPop ([] : List α) = (none, []) := rfl

@[simp]
lemma fifoPop_cons (h : α) (t : List α) : fifoPop (h :: t) = (some h, t) := rfl

/-! ## Theorem 1 : Push [a, b, c] then pop 3 times gives [a, b, c] -/

/-- Pushing elements `a`, `b`, `c` onto an empty FIFO and then popping three times
    yields them in FIFO order: first `a`, then `b`, then `c`. -/
theorem fifo_push_pop_order (a b c : α) :
    let q₀ : List α := []
    let q₁ := fifoPush q₀ a
    let q₂ := fifoPush q₁ b
    let q₃ := fifoPush q₂ c
    let (v₁, q₄) := fifoPop q₃
    let (v₂, q₅) := fifoPop q₄
    let (v₃, _q₆) := fifoPop q₅
    v₁ = some a ∧ v₂ = some b ∧ v₃ = some c := by
  simp [fifoPush, fifoPop]

/-! ## Theorem 2 : Push increases length by 1 -/

/-- Pushing an element onto a FIFO increases its length by exactly 1. -/
theorem fifo_push_increases_length (fifo : List α) (x : α) :
    (fifoPush fifo x).length = fifo.length + 1 := by
  simp [fifoPush]

/-! ## Theorem 3 : Pop on non-empty decreases length by 1 -/

/-- Popping from a non-empty FIFO yields a remainder whose length is
    exactly one less than the original. -/
theorem fifo_pop_decreases_length (fifo : List α) (h : fifo ≠ []) :
    (fifoPop fifo).2.length = fifo.length - 1 := by
  cases fifo with
  | nil => contradiction
  | cons hd tl => simp [fifoPop]

/-! ## Theorem 4 : Pop returns the oldest element (head) -/

/-- Popping from a non-empty FIFO returns the head of the list — the oldest element. -/
theorem fifo_pop_returns_head (fifo : List α) (h : fifo ≠ []) :
    (fifoPop fifo).1 = fifo.head? := by
  cases fifo with
  | nil => contradiction
  | cons hd tl => simp [fifoPop]

/-! ## Theorem 5 : Push preserves existing elements -/

/-- Pushing a new element does not change the existing contents.
    The resulting list is the original FIFO with the new element appended. -/
theorem fifo_push_preserves_existing (fifo : List α) (x : α) :
    (fifoPush fifo x).take fifo.length = fifo := by
  simp [fifoPush]

/-! ## Theorem 6 : Fundamental ordering invariant -/

/-- Helper: `n` successive pops from a list return the elements in list order. -/
def popN : ℕ → List α → List (Option α)
  | 0, _ => []
  | n + 1, q =>
    let (v, q') := fifoPop q
    v :: popN n q'

/-- The pop-sequence of a list is exactly the list's elements in order, padded
    with `none` once the queue is empty. -/
lemma popN_eq_map_get? (l : List α) :
    popN l.length l = l.map some := by
  induction l with
  | nil => simp [popN]
  | cons h t ih =>
    simp [popN, fifoPop, ih]

/-- Fundamental FIFO ordering invariant.

    For any two elements `a` and `b` pushed into an initially-empty FIFO
    where `a` is pushed first (logical time t₁) and `b` is pushed second
    (logical time t₂ > t₁), the pop sequence returns `a` at step 0 and
    `b` at step 1 — i.e., `a` is popped strictly before `b`.

    This is the machine-checked proof that the list model faithfully
    implements FIFO ordering. -/
theorem fifo_ordering_invariant (a b : α) :
    let q₀ : List α := []
    let q₁ := fifoPush q₀ a   -- a pushed at time t₁
    let q₂ := fifoPush q₁ b   -- b pushed at time t₂ > t₁
    -- Pop sequence must return a before b
    let pops := popN 2 q₂
    pops = [some a, some b] := by
  simp [popN, fifoPush, fifoPop]

end Pythia.Hardware.FIFOOrdering
