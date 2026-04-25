/-
Kairos.Stats.Tactic.VilleCmd — `#ville` elaborator command.

Prints the `eta` and `slackFn` fields of a registered `CSFamily`
declaration, formatted as a brief info message.

## Example

```
#ville Kairos.Stats.familyHR
-- family:  Kairos.Stats.familyHR
--   eta:     Kairos.Stats.familyHR.eta
--   slackFn: Kairos.Stats.familyHR.slackFn
```
-/
import Kairos.Stats.BenchDefs
import Lean

namespace Kairos.Stats

open Lean Elab

/-- `#ville myCS` — print the `eta` and `slackFn` of a `CSFamily` declaration.
Looks up the name in the environment and emits an info message with the
two field-projection names.  Emits an error if the name is not found,
or a warning if the resolved constant is not of type `CSFamily`. -/
elab "#ville " name:ident : command => do
  let env ← getEnv
  let nm := name.getId
  match env.find? nm with
  | none =>
    Lean.logError m!"#ville: unknown declaration '{nm}'"
  | some ci =>
    -- Best-effort type check: warn when the type is not CSFamily.
    let isCsFamily : Bool :=
      match ci.type.getAppFn with
      | .const n _ => n == `Kairos.Stats.CSFamily
      | _ => false
    if !isCsFamily then
      Lean.logWarning m!"#ville: '{nm}' does not appear to be a CSFamily \
        (type head: {ci.type})"
    Lean.logInfo m!"family:  {nm}\n  eta:     {nm}.eta\n  slackFn: {nm}.slackFn"

end Kairos.Stats
