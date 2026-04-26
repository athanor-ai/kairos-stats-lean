/-
Pythia.Tactic.CSFamilyRegistry — registers the four canonical
CS families with the `@[cs_family]` attribute.

This file exists separately from `BenchDefs.lean` (where the families
are defined) and `CSFamilyAttr.lean` (where the attribute lives) to
avoid a circular dependency: `CSFamilyAttr` imports `BenchDefs` for
the `CSFamily` structure type, so `BenchDefs` cannot import the
attribute itself. The split-out registry file imports both and
attaches the attribute via `attribute [cs_family]`.

After this file is imported, `#cs_families` lists all four canonical
families.
-/
import Pythia.Tactic.CSFamilyAttr

namespace Pythia

attribute [cs_family] familyHR familyBetting familyVector familyAsymptotic

end Pythia
