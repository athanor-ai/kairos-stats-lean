/-
examples/03_cs_families_introspection.lean — discoverability commands.

`#cs_families` enumerates registered `@[cs_family]` declarations.
`#ville` previews the Ville statement applied to a chosen family +
parameters. Both are info-only commands; the real work happens at the
theorem level (admissibility, ranking).
-/
import Kairos.Stats.Tactic.CSFamilyRegistry
import Kairos.Stats.Tactic.VilleCmd

open Kairos.Stats

#cs_families
