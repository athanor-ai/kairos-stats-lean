import Pythia.LanguageSemantics.Palamedes.Gen
import Pythia.LanguageSemantics.Palamedes.CorrectGen
import Pythia.LanguageSemantics.Palamedes.Total

namespace Gen

@[reducible]
def arbUnit : Gen Unit := pure ()

namespace CorrectGen

@[reducible]
def s_arbUnit : @CorrectGen Unit (fun _ => True) :=
  Subtype.mk arbUnit (by simp [arbUnit])

end CorrectGen

end Gen
