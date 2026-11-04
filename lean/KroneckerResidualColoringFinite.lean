import KroneckerProgramExecution

/-! The union of all surplus classes is finite: the grading determines its surplus uniquely. -/
set_option autoImplicit false
namespace KroneckerSurplusColoringFinite
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerProgramExecution

def surplusForget {m : ℕ} {U : List Bool} (a : SurplusColorings m U) : Coloring m U.length := a.2.val

theorem connected_surplus_unique {m c d : ℕ} {es : List Edge}
    (h : Connected m es c) (h' : Connected m es d) : c=d := by
  have hc := connected_surplus h
  have hd := connected_surplus h'
  omega

theorem surplusForget_injective (m : ℕ) (U : List Bool) :
    Function.Injective (@surplusForget m U) := by
  intro a b he
  rcases a with ⟨c,g,hg⟩
  rcases b with ⟨d,h,hh⟩
  change g=h at he
  subst h
  have hcd := connected_surplus_unique hg hh
  subst d
  rfl

noncomputable instance surplusFintype (m : ℕ) (U : List Bool) : Fintype (SurplusColorings m U) :=
  Fintype.ofInjective surplusForget (surplusForget_injective m U)

end KroneckerSurplusColoringFinite
