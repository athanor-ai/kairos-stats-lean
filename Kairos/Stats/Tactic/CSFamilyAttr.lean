/-
Kairos.Stats.Tactic.CSFamilyAttr — `@[cs_family]` attribute and
`#cs_families` command.

Phase B v0.2.0 piece 2 (after the `anytime_valid` tactic). Lets users
register CS families in a fleet-wide table, queryable via the
`#cs_families` command. Foundation for future auto-derivation of
admissibility + slack instances per family.

## Examples

Register a new CS family:
```
@[cs_family]
noncomputable def myFamily : CSFamily where
  eta := myEta
  slackFn := fun σ bp => mySlack σ bp.bits
```

List all registered families:
```
#cs_families
-- Kairos.Stats.familyHR
-- Kairos.Stats.familyBetting
-- Kairos.Stats.familyVector
-- Kairos.Stats.familyAsymptotic
-- MyNamespace.myFamily
```

## Status

Iteration 1: registration + listing. The attribute records the
declaration name in a scoped environment extension. Future iterations
will:
* Auto-derive `Admissible` instance via the boundary + rate fields.
* Auto-derive `quantizationSlack` via the rate.
* Allow named-argument syntax `@[cs_family name := "myFamily"]`.

-/
import Kairos.Stats.BenchDefs
import Lean

namespace Kairos.Stats

open Lean Elab

/-- Environment extension storing the names of all `@[cs_family]`-tagged
declarations. -/
initialize csFamilyExt :
    SimpleScopedEnvExtension Name (Std.HashSet Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := ∅
  }

/-- The `@[cs_family]` attribute. Marks a `CSFamily`-typed definition
as a registered family. The declaration name is recorded in
`csFamilyExt` and is enumerable via `#cs_families`. -/
initialize registerBuiltinAttribute {
  name := `cs_family
  descr := "Register a CSFamily declaration so it appears in #cs_families."
  add := fun decl _stx _kind => do
    csFamilyExt.add decl
}

/-- `#cs_families` — print every registered CS family. -/
elab "#cs_families" : command => do
  let env ← getEnv
  let s := csFamilyExt.getState env
  if s.isEmpty then
    logInfo "no families registered (use @[cs_family] to register one)"
  else
    let names := s.toList
    let lines := names.map (fun n => m!"  • {n}")
    logInfo (m!"registered cs families ({names.length}):" ++ MessageData.joinSep lines "\n")

end Kairos.Stats
