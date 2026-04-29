import Pythia.LanguageSemantics.Palamedes.Gen
import Pythia.LanguageSemantics.Palamedes.CorrectGen
import Pythia.LanguageSemantics.Palamedes.Total

namespace Gen

def arbBool : Gen Bool := pick (pure true) (pure false)

namespace CorrectGen

@[reducible]
def s_arbBool : @CorrectGen Bool (fun _ => True) :=
  Subtype.mk arbBool (by simp [arbBool])

@[reducible]
def s_caseBool
    {Q : α → Prop}
    {P : α → Bool → Prop}
    (b : Bool)
    (h : ∀ {a}, P a b = Q a)
    (gt : CorrectGen (fun a => P a true))
    (gf : CorrectGen (fun a => P a false)) :
    CorrectGen Q :=
  Subtype.mk (if h : b then gt.val else gf.val) <| by
    match b with
    | true => simp [gt.property, h]
    | false => simp [gf.property, h]

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbBool : total (arbBool : Gen Bool) := by
  simp [arbBool]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_Bool_rec (hf : total gf) (ht : total gt) : total (Bool.rec gf gt b) := by
  cases b <;> simp_all

end Total

end Gen
