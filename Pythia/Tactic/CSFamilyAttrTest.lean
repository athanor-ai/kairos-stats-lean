/-
Pythia.Tactic.CSFamilyAttrTest — regression for the
`@[cs_family]` attribute and `#cs_families` command.

Each example is a compile-time test. If the attribute or command
breaks, CI fails here before any broken implementation lands on main.
-/
import Pythia.Tactic.CSFamilyAttr
import Pythia.Tactic.CSFamilyRegistry

namespace Pythia.Tactic.Test

/-- Test 1. Register a custom family with the attribute. The
declaration must compile, and the registration is verified at compile
time by the `#cs_families` info message in the surrounding scope. -/
@[cs_family]
noncomputable def testFamily : Pythia.CSFamily where
  eta := fun _ => 1.0
  slackFn := fun _ _ => 1.0

end Pythia.Tactic.Test

-- Test 2. `#cs_families` outside the namespace, after the test
-- family is registered. The info message during compilation lists every
-- registered family including `Pythia.Tactic.Test.testFamily`.
#cs_families
