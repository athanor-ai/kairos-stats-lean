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

  - Hoeffding:    exp(-2 n ε² / b²)
  - Bernstein:    exp(-n ε² / (2 (σ² + b ε / 3)))
  - Sub-Gaussian: exp(-n ε² / (2 σ²))
  - Sub-gamma:    exp(-n ε² / (2 (V + c ε)))   (when V, c provided)
  - Markov:       μ / ε                         (when μ provided)
  - Chebyshev:    σ² / (n ε²)                   (when σ provided)

## Architecture

v2 (this file): `TightTail` now uses the `Pythia.Family` struct and
`Pythia.genericReport` from `Pythia.Tactic.DomainCalculator`.
The top-level `report` signature is identical to v1 so all existing
call sites (`#eval TightTail.report (σ := ...) (b := ...) ...`)
continue to work without change.

v3 (planned): rank by SHARPNESS-AT-PARAMETERS, not just numeric
value (flag when the parameter regime puts a bound within ε of
optimal vs. when it's a constant factor off).

## Why this is more than a proof tactic

The other pythia tactics (`pythia`, `stats_ineq`, `anytime_valid`,
`z3_check`) close goals. `TightTail.report` instead helps the user
*pick* the goal: which inequality is worth invoking on this problem.
Lean plus Mathlib gives a closure tactic on a pre-stated bound;
pythia adds the upstream step of choosing the bound. That's the
difference between a tactic library and a domain calculator.
-/
import Mathlib
import Pythia.Tactic.DomainCalculator

namespace Pythia
namespace TightTail

/-! ### Parameter struct

`TailParam` bundles the seven floating-point parameters that the
tail-bound families consume. All fields default to `0.0`; callers use
named arguments (`report (σ := 0.3) (b := 1) (n := 1000) (ε := 0.05)`)
and omit inapplicable parameters. -/

structure TailParam where
  σ : Float := 0.0
  b : Float := 0.0
  V : Float := 0.0
  c : Float := 0.0
  n : Float := 0.0
  ε : Float := 0.0
  μ : Float := 0.0
  deriving Inhabited

/-! ### Domain tag -/

/-- Phantom type that identifies the tail-bound calculator as a
`DomainCalculator` instance. No data, only type-level identity. -/
structure TailBound where

/-! ### Family definitions (six standard bounds) -/

/-- Hoeffding for bounded iid: `P(X̄ - μ ≥ ε) ≤ exp(-2 n ε² / b²)`.
Requires `b > 0`. -/
def hoeffding : Family TailParam Float where
  name := "Hoeffding"
  ref := "Hoeffding 1963"
  compute := fun p =>
    if p.b > 0 then some (Float.exp (-2.0 * p.n * p.ε * p.ε / (p.b * p.b)))
    else none

/-- Bernstein for bounded zero-mean iid: `P(X̄ ≥ ε) ≤
exp(-n ε² / (2 (σ² + b ε / 3)))`. Requires `b > 0` and `σ > 0`. -/
def bernstein : Family TailParam Float where
  name := "Bernstein"
  ref := "Bernstein 1924"
  compute := fun p =>
    if p.b > 0 && p.σ > 0 then
      some (Float.exp (-p.n * p.ε * p.ε / (2.0 * (p.σ * p.σ + p.b * p.ε / 3.0))))
    else none

/-- Sub-Gaussian Chernoff: `P(X̄ ≥ ε) ≤ exp(-n ε² / (2 σ²))`.
Requires `σ > 0`. -/
def subGaussian : Family TailParam Float where
  name := "Sub-Gaussian"
  ref := "Boucheron-Lugosi-Massart 2013 §2.3"
  compute := fun p =>
    if p.σ > 0 then some (Float.exp (-p.n * p.ε * p.ε / (2.0 * p.σ * p.σ)))
    else none

/-- Sub-gamma: `P(X̄ ≥ ε) ≤ exp(-n ε² / (2 (V + c ε)))`.
Requires `V > 0` and `c ≥ 0`. -/
def subGamma : Family TailParam Float where
  name := "Sub-gamma"
  ref := "Boucheron-Lugosi-Massart 2013 §2.4"
  compute := fun p =>
    if p.V > 0 && p.c ≥ 0 then
      some (Float.exp (-p.n * p.ε * p.ε / (2.0 * (p.V + p.c * p.ε))))
    else none

/-- Markov: `P(X ≥ ε) ≤ μ / ε` for nonneg X. Requires `μ > 0` and
`ε > 0`. -/
def markov : Family TailParam Float where
  name := "Markov"
  ref := "Markov 1884"
  compute := fun p =>
    if p.ε > 0 && p.μ > 0 then some (p.μ / p.ε) else none

/-- Chebyshev: `P(|X̄ - μ| ≥ ε) ≤ σ² / (n ε²)`. Requires `σ > 0` and
`ε > 0`. -/
def chebyshev : Family TailParam Float where
  name := "Chebyshev"
  ref := "Chebyshev 1867"
  compute := fun p =>
    if p.σ > 0 && p.ε > 0 then some (p.σ * p.σ / (p.n * p.ε * p.ε))
    else none

/-- The registered families. v3 will read this from a
`@[tail_bound]` attribute extension; for now the table is fixed. -/
def registry : List (Family TailParam Float) :=
  [hoeffding, bernstein, subGaussian, subGamma, markov, chebyshev]

/-- Format a single line of the report. -/
def formatLine (rank : Nat) (f : Family TailParam Float) (b : Float) : String :=
  let marker := if rank = 0 then "*" else " "
  s!"  {marker} {f.name.rightpad 14} ≤ {b}    ({f.ref})"

/-! ### DomainCalculator instance -/

/-- `DomainCalculator TailBound`: wires the tail-bound domain into the
generic calculator typeclass. -/
instance : DomainCalculator TailBound where
  name := "tail-bound"
  Param := TailParam
  Output := Float
  families := registry
  formatLine := formatLine
  report := fun p =>
    let header :=
      s!"#tight_tail @ (σ={p.σ}, b={p.b}, V={p.V}, c={p.c}, n={p.n}, ε={p.ε}, μ={p.μ}):\n"
    let footer_nonempty := "\n  * tightest bound at these parameters."
    let footer_empty :=
      "\n  (no bounds applicable in this parameter regime: supply more parameters.)"
    genericReport registry formatLine header footer_nonempty footer_empty p

/-! ### Public API (unchanged from v1) -/

/-- Build the report by evaluating each family at the given
parameters, dropping the `none`s, sorting by tightness, and labeling
the sharpest. Use named arguments for clarity:
`#eval TightTail.report (σ := 0.3) (b := 1) (n := 1000) (ε := 0.05)`.
Defaults are zero so unused parameters can be omitted.

This is a thin wrapper around `DomainCalculator.report` that
preserves the v1 named-argument API exactly. -/
def report
    (σ : Float := 0.0) (b : Float := 0.0) (V : Float := 0.0)
    (c : Float := 0.0) (n : Float := 0.0) (ε : Float := 0.0)
    (μ : Float := 0.0) : String :=
  (inferInstance : DomainCalculator TailBound).report
    { σ := σ, b := b, V := V, c := c, n := n, ε := ε, μ := μ }

end TightTail
end Pythia
