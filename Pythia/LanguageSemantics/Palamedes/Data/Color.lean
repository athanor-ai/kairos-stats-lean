import Pythia.LanguageSemantics.Palamedes.Gen
import Pythia.LanguageSemantics.Palamedes.CorrectGen
import Pythia.LanguageSemantics.Palamedes.Total

section TypeDef

inductive Color where
  | red
  | black
deriving DecidableEq

@[simp]
theorem Color.exists_color {P : Color → Prop} : (∃ c, P c) ↔ P .red ∨ P .black := by
  apply Iff.intro <;> intro h
  . let ⟨c, h⟩ := h
    cases c <;> aesop
  . cases h <;> aesop

def Color.toString : Color → String
  | .red => "red"
  | .black => "black"

instance : ToString Color where
  toString := Color.toString

end TypeDef

namespace Gen

def arbColor : Gen Color := pick (pure .red) (pure .black)

@[simp]
theorem support_arbColor :
    support arbColor = fun _ => True := by
    funext x; cases x <;> simp_all [arbColor]

namespace CorrectGen

@[reducible]
def s_arbColor : @CorrectGen Color (fun _ => True) :=
  Subtype.mk arbColor <| by
    funext v
    simp

@[reducible]
def s_caseColor
    {Q : α → Prop}
    {P : α → Color → Prop}
    (c: Color)
    (h : ∀ {a}, P a c = Q a)
    (gr : CorrectGen (fun a => P a .red))
    (gb : CorrectGen (fun a => P a .black)) :
    CorrectGen Q :=
  Subtype.mk (if c = .red then gr.val else gb.val) <| by
    match c with
    | .red => simp [gr.property, h]
    | .black => simp [gb.property, h]

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbColor : total (arbColor : Gen Color) := by
  simp [arbColor]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_color_rec (hf : total gr) (ht : total gb) : total (Color.rec gr gb c) := by
  cases c <;> simp_all

end Total

end Gen
