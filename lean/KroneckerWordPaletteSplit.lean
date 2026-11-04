import KroneckerOrientationPositions
import KroneckerInputRecovery

/-! Reindex actual word colors into horizontal and vertical arrays without losing data. -/
set_option autoImplicit false
namespace KroneckerWordPaletteSplit
open KroneckerColoring KroneckerOrientationPositions KroneckerInputRecovery

noncomputable def splitColoring {m : ℕ} (U : List Bool) (g : Coloring m U.length) :
    Input m (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) :=
  ⟨fun j => g ((Fintype.equivFin (Positions U true)).symm j).val,
   fun j => g ((Fintype.equivFin (Positions U false)).symm j).val⟩

theorem split_horizontal {m : ℕ} (U : List Bool) (g : Coloring m U.length)
    (i : Positions U true) :
    (splitColoring U g).1 (Fintype.equivFin (Positions U true) i)=g i.val := by
  simp [splitColoring]

theorem split_vertical {m : ℕ} (U : List Bool) (g : Coloring m U.length)
    (i : Positions U false) :
    (splitColoring U g).2 (Fintype.equivFin (Positions U false) i)=g i.val := by
  simp [splitColoring]

theorem splitColoring_injective {m : ℕ} (U : List Bool) :
    Function.Injective (splitColoring (m:=m) U) := by
  intro g h he
  funext i
  cases hb : U[i.val] with
  | false =>
    have hv := congrFun (congrArg Prod.snd he)
      (Fintype.equivFin (Positions U false) ⟨i,hb⟩)
    simpa only [split_vertical] using hv
  | true =>
    have hh := congrFun (congrArg Prod.fst he)
      (Fintype.equivFin (Positions U true) ⟨i,hb⟩)
    simpa only [split_horizontal] using hh

end KroneckerWordPaletteSplit
