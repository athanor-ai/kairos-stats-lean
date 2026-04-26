/-
Pythia.Tactic.TightTail — the tail-bound calculator.

A *tail-bound calculator*: given concrete parameters (sub-Gaussian σ,
support bound b, sub-gamma variance V, sample size n, deviation ε),
this module evaluates every registered concentration inequality
numerically and reports which one gives the tightest bound.

This is the kind of question a working statistician asks at a
whiteboard ("for n = 1000 samples bounded in [0, 1] with σ = 0.3,
what's the sharpest tail bound on `P(X̄ - μ > 0.05)`?") and that no
general-purpose proof assistant currently answers. Lean's `simp` and
`aesop` close proofs; they don't *select inequalities*. Pythia does
both.

## Usage

```
import Pythia.Tactic.TightTail
open Pythia in
#eval TightTail.report (σ := 0.3) (b := 1) (n := 1000) (ε := 0.05)
```

prints a sorted table of every applicable bound, with the tightest
labeled. The unused parameters can be omitted (they default to 0,
which makes the corresponding bound `none` when the regime demands a
positive value).

## What gets evaluated

  • Hoeffding:    exp(-2 n ε² / b²)
  • Bernstein:    exp(-n ε² / (2 (σ² + b ε / 3)))
  • Sub-Gaussian: exp(-n ε² / (2 σ²))
  • Sub-gamma:    exp(-n ε² / (2 (V + c ε)))   (when V, c provided)
  • Markov:       μ / ε                         (when μ provided)
  • Chebyshev:    σ² / (n ε²)                   (when σ provided)

## Why this is more than a proof tactic

The other pythia tactics (`pythia`, `stats_ineq`, `anytime_valid`,
`z3_check`) close goals. `TightTail.report` instead helps the user
*pick* the goal: which inequality is worth invoking on this problem.
Lean plus Mathlib gives a closure tactic on a pre-stated bound;
pythia adds the upstream step of choosing the bound. That's the
difference between a tactic library and a domain calculator.

## Status

v1 (this file): hard-coded formula table, single-source query via
`#eval`.

v2: read formulas from a `@[tail_bound]` attribute registry so users
can add their own bounds.

v3: rank by SHARPNESS-AT-PARAMETERS not just numeric value (e.g. flag
when the parameter regime puts a bound within ε of optimal vs. when
it's a constant factor off).
-/
import Mathlib

namespace Pythia
namespace TightTail

/-- A single tail-bound family: name + closure that maps parameters
to a numeric bound. `none` means "this bound doesn't apply for the
given parameter regime" (e.g. Bernstein requires `b > 0`). -/
structure Family where
  /-- Display name. -/
  name : String
  /-- Short textbook reference. -/
  ref : String
  /-- Compute the bound from `(σ, b, V, c, n, ε, μ)`. Any unused
  parameter is set to its default by the caller. Return `none` when
  out-of-fragment. -/
  bound : (σ b V c n ε μ : Float) → Option Float

/-- Hoeffding for bounded iid: `P(X̄ - μ ≥ ε) ≤ exp(-2 n ε² / b²)`.
Requires `b > 0`. -/
def hoeffding : Family where
  name := "Hoeffding"
  ref := "Hoeffding 1963"
  bound := fun _ b _ _ n ε _ =>
    if b > 0 then some (Float.exp (-2.0 * n * ε * ε / (b * b)))
    else none

/-- Bernstein for bounded zero-mean iid: `P(X̄ ≥ ε) ≤
exp(-n ε² / (2 (σ² + b ε / 3)))`. Requires `b > 0` and `σ > 0`. -/
def bernstein : Family where
  name := "Bernstein"
  ref := "Bernstein 1924"
  bound := fun σ b _ _ n ε _ =>
    if b > 0 && σ > 0 then
      some (Float.exp (-n * ε * ε / (2.0 * (σ * σ + b * ε / 3.0))))
    else none

/-- Sub-Gaussian Chernoff: `P(X̄ ≥ ε) ≤ exp(-n ε² / (2 σ²))`.
Requires `σ > 0`. -/
def subGaussian : Family where
  name := "Sub-Gaussian"
  ref := "Boucheron-Lugosi-Massart 2013 §2.3"
  bound := fun σ _ _ _ n ε _ =>
    if σ > 0 then some (Float.exp (-n * ε * ε / (2.0 * σ * σ)))
    else none

/-- Sub-gamma: `P(X̄ ≥ ε) ≤ exp(-n ε² / (2 (V + c ε)))`.
Requires `V > 0` and `c ≥ 0`. -/
def subGamma : Family where
  name := "Sub-gamma"
  ref := "Boucheron-Lugosi-Massart 2013 §2.4"
  bound := fun _ _ V c n ε _ =>
    if V > 0 && c ≥ 0 then
      some (Float.exp (-n * ε * ε / (2.0 * (V + c * ε))))
    else none

/-- Markov: `P(X ≥ ε) ≤ μ / ε` for nonneg X. Requires `μ > 0` and
`ε > 0`. -/
def markov : Family where
  name := "Markov"
  ref := "Markov 1884"
  bound := fun _ _ _ _ _ ε μ =>
    if ε > 0 && μ > 0 then some (μ / ε) else none

/-- Chebyshev: `P(|X̄ - μ| ≥ ε) ≤ σ² / (n ε²)`. Requires `σ > 0` and
`ε > 0`. -/
def chebyshev : Family where
  name := "Chebyshev"
  ref := "Chebyshev 1867"
  bound := fun σ _ _ _ n ε _ =>
    if σ > 0 && ε > 0 then some (σ * σ / (n * ε * ε))
    else none

/-- The registered families. v2 will read this from a
`@[tail_bound]` attribute extension; for now the table is fixed. -/
def registry : List Family :=
  [hoeffding, bernstein, subGaussian, subGamma, markov, chebyshev]

/-- Format a single line of the report. -/
def formatLine (rank : Nat) (f : Family) (b : Float) : String :=
  let marker := if rank = 0 then "*" else " "
  s!"  {marker} {f.name.rightpad 14} ≤ {b}    ({f.ref})"

/-- Build the report by evaluating each family at the given
parameters, dropping the `none`s, sorting by tightness, and labeling
the sharpest. Use named arguments for clarity:
`#eval TightTail.report (σ := 0.3) (b := 1) (n := 1000) (ε := 0.05)`.
Defaults are zero so unused parameters can be omitted. -/
def report
    (σ : Float := 0.0) (b : Float := 0.0) (V : Float := 0.0)
    (c : Float := 0.0) (n : Float := 0.0) (ε : Float := 0.0)
    (μ : Float := 0.0) : String := Id.run do
  let evaluated := registry.filterMap fun f =>
    f.bound σ b V c n ε μ |>.map fun bnd => (f, bnd)
  let sorted := evaluated.mergeSort (fun (_, b₁) (_, b₂) => b₁ ≤ b₂)
  let header := s!"#tight_tail @ (σ={σ}, b={b}, V={V}, c={c}, n={n}, ε={ε}, μ={μ}):\n"
  let lines := sorted.zipIdx.map (fun ((f, b), rank) => formatLine rank f b)
  let footer :=
    if sorted.isEmpty then
      "\n  (no bounds applicable in this parameter regime: supply more parameters.)"
    else
      "\n  * tightest bound at these parameters."
  return header ++ String.intercalate "\n" lines ++ footer

end TightTail
end Pythia
