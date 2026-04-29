import Pythia.LanguageSemantics.Palamedes.Gen
import Pythia.LanguageSemantics.Palamedes.CorrectGen
import Pythia.LanguageSemantics.Palamedes.Total
import Pythia.LanguageSemantics.Palamedes.Data.Nat

section TypeDef
/- adapted from https://github.com/QuickChick/QuickChick/tree/master/examples/ifc-basic -/

inductive Label where
  | low
  | high

inductive Atom where
  | atm (n : Nat) (l : Label)

end TypeDef

namespace Gen

@[irreducible]
def arbLabel  : Gen Label :=
  pick (pure .low) (pure .high)

@[simp]
theorem support_arbLabel : support arbLabel = fun _ => True := by
  funext v
  cases v <;> simp_all [arbLabel]

namespace CorrectGen

@[reducible]
def s_arbLabel : @CorrectGen Label (fun _ => True) :=
  Subtype.mk arbLabel <| by
    funext v
    simp

@[reducible]
def s_arbAtom
    {P : Atom → Prop}
    (g : CorrectGen (fun (a : Atom) => ∃ (n : Nat) (l : Label), P (.atm n l) ∧ a = .atm n l)) :
    CorrectGen (fun (a : Atom) => P a) :=
  Subtype.mk g.val <| by
    funext (.atm n l)
    simp_all [g.property]

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbLabel : total arbLabel := by
  simp [arbLabel]

end Total

end Gen

namespace PrettyPrint

def Label.toString : Label → String
  | .low => "low"
  | .high => "high"

instance : ToString Label where
  toString := Label.toString

def Atom.toString : Atom → String
  | .atm n l => s!"({n} {l})"

instance : ToString Atom where
  toString := Atom.toString

end PrettyPrint
