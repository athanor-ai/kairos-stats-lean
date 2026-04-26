/-
Pythia.Tactic.VilleCmdTest — regression for the `#ville` command.

Each bare `#ville` call below is a compile-time test: it succeeds if the
named declaration exists in the environment and emits the expected info
message.  CI failure here means the elaborator or the registry broke.
-/
import Pythia.Tactic.VilleCmd
import Pythia.Tactic.CSFamilyRegistry

-- Test 1: HR family
#ville Pythia.familyHR

-- Test 2: Betting family
#ville Pythia.familyBetting
