/-
Pythia.Tactic.DomainCalculator — generic domain-calculator typeclass.

A *domain calculator* knows how to evaluate a family of inequalities
or formulae at concrete parameters and report which one gives the
tightest result. The typeclass here abstracts over the *domain*
(tail bounds, actuarial premiums, etc.) so that each domain can
register its own families and still share the reporting machinery.

## Design

The central concept is a `Family (Param Output)`: a named formula
that maps parameters to an optional numeric output. `Output` must
have a `LE` instance so families can be sorted by tightness.

The `DomainCalculator` typeclass wraps:
  - a list of registered families,
  - a line-formatter for the tabular report, and
  - a top-level `report` entry point.

Clients instantiate the typeclass for their concrete domain; the
shared `genericReport` function handles evaluation, sorting, and
labelling.

## Parameterization

`DomainCalculator Domain` is parameterized by a phantom type
`Domain` that distinguishes different calculator instances.
Concretely, `TightTail` introduces `TailBound` as its domain tag
and instantiates `DomainCalculator TailBound`.

## Axiom policy

No `sorry`, no added axioms. This module is pure `def`/`structure`/
`class`; it imports `Mathlib` for `List.mergeSort` and `String`
helpers only.
-/
import Mathlib

namespace Pythia

/-- A single formula family parameterized by `Param` (the input
struct) and `Output` (the numeric result type, e.g. `Float` or
`Option Float`). `compute` returns `none` when the formula is
inapplicable in the given parameter regime. -/
structure Family (Param Output : Type) where
  /-- Display name shown in the report. -/
  name : String
  /-- Short textbook reference. -/
  ref : String
  /-- Compute the bound. Returns `none` when out of regime. -/
  compute : Param → Option Output

/-- A domain calculator for domain tag `Domain`. Each domain
instantiates this typeclass by supplying its family list, a
line-formatter, and the `report` entry point.

Fields:
- `name`       : display name of the calculator (e.g. "tail-bound").
- `Param`      : the parameter struct type for this domain.
- `Output`     : numeric output type (typically `Float`).
- `families`   : the registered family list.
- `formatLine` : format one line of the report given rank, family,
                 and output value.
- `report`     : evaluate all families at `p`, sort by `Output`,
                 label the sharpest, and return a formatted string.
-/
class DomainCalculator (Domain : Type) where
  /-- Display name of this domain calculator. -/
  name : String
  /-- Parameter struct for this domain. -/
  Param : Type
  /-- Numeric output type for this domain. -/
  Output : Type
  /-- Registered formula families. -/
  families : List (Family Param Output)
  /-- Format one report line. `rank = 0` is the tightest. -/
  formatLine : Nat → Family Param Output → Output → String
  /-- Evaluate all families at `p` and return a formatted report. -/
  report : Param → String

/-- Generic report builder shared by all domain calculators.

Evaluates each family in `families` at `p` via `compute`, drops
`none`s, sorts ascending by `Output` (so the smallest value, i.e.
the tightest bound, comes first), then emits a formatted table with
`formatLine`. The `header` and `footer` strings are supplied by the
caller for domain-specific text. -/
def genericReport
    {Param Output : Type}
    [LE Output] [DecidableRel (LE.le (α := Output))]
    (families : List (Family Param Output))
    (formatLine : Nat → Family Param Output → Output → String)
    (header : String)
    (footer_nonempty : String)
    (footer_empty : String)
    (p : Param) : String := Id.run do
  let evaluated := families.filterMap fun f =>
    (f.compute p).map fun out => (f, out)
  let sorted := evaluated.mergeSort (fun (_, o₁) (_, o₂) => o₁ ≤ o₂)
  let lines := sorted.zipIdx.map (fun ((f, out), rank) => formatLine rank f out)
  if sorted.isEmpty then
    return header ++ footer_empty
  else
    return header ++ String.intercalate "\n" lines ++ footer_nonempty

end Pythia
