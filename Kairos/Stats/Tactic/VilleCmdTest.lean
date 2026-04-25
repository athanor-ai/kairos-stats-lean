/-
Kairos.Stats.Tactic.VilleCmdTest — regression for the `#ville` command.

Each bare `#ville` call below is a compile-time test: it succeeds if the
named declaration exists in the environment and emits the expected info
message.  CI failure here means the elaborator or the registry broke.
-/
import Kairos.Stats.Tactic.VilleCmd
import Kairos.Stats.Tactic.CSFamilyRegistry

-- Test 1: HR family
#ville Kairos.Stats.familyHR

-- Test 2: Betting family
#ville Kairos.Stats.familyBetting
