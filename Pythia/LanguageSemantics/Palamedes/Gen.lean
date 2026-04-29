/-
Copyright (c) 2025 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Aesop

/-!
# Intermediate Language for Generators

This module introduces an intermediate langauge for generators. They are loosely based on [free
generators][goldsteinParsingRandomness2022], although not exactly the same. The most important
aspect of the `Gen` type is that it is an inductive structure --- i.e., data --- not a function.
This means that it can be _interpreted_ in multiple ways, which we demonstrate later.
-/

namespace Raw

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | pick : Gen α → Gen α → Gen α
  | indexed : (Nat → Gen (Option α)) → Gen α
  | assume : (b : Bool) → (b → Gen α) → Gen α

end Raw

def Gen (α : Type) := Raw.Gen α

namespace Gen

instance : Pure Gen where
  pure a := Raw.Gen.ret a

instance : Bind Gen where
  bind x f := Raw.Gen.bind x f

instance : Monad Gen where

def pick (x y : Gen α) : Gen α := Raw.Gen.pick x y

def assume (b : Bool) (f : b → Gen α) : Gen α := Raw.Gen.assume b f

def indexed (f : Nat → Gen (Option α)) : Gen α := Raw.Gen.indexed f

def support : Gen α → α → Prop
  | .ret a => (. = a)
  | .pick x y => fun a => support x a ∨ support y a
  | .indexed f => fun a =>
    (∀ v n m, support (f n) (some v) → support (f (n + m)) (some v))
      ∧  ∃ n, support (f n) (some a)
  | .bind x f => fun b => ∃ a, support x a ∧ support (f a) b
  | .assume b f => fun a => ∃ h : b, support (f h) a

namespace Support

@[simp]
theorem support_pure :
    support (pure a) = (· = a) := by
  simp [support]

@[simp]
theorem support_bind :
    support (x >>= f) = fun b => ∃ a, support x a ∧ support (f a) b := by
  simp [support]

@[simp]
theorem support_pick :
    support (pick x y) = fun a => support x a ∨ support y a := by
  simp [support, pick]

@[simp]
theorem support_assume :
    support (assume b f) = fun a => ∃ h : b, support (f h) a := by
  simp [support, assume]

@[simp]
theorem support_indexed :
    support (indexed f) = fun a =>
      (∀ v n m, support (f n) (some v) → support (f (n + m)) (some v))
        ∧ ∃ n, support (f n) (some a) := by
  simp [support, indexed]

@[simp]
theorem support_map :
    support (f <$> x) = fun b => ∃ a, support x a ∧ b = f a := by
  simp [Functor.map]

@[simp]
theorem support_dite
  {b : Bool} {g1 : b = true → Gen α} {g2 : ¬ (b = true) → Gen α } :
  support (if h : b then g1 h else g2 h) = fun a =>
    if h : b then support (g1 h) a else support (g2 h) a := by
  cases b <;> simp_all

end Support

end Gen

notation v " ∈ " "〚" g "〛" => Gen.support g v
