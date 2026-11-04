import KroneckerWordCounts
import Mathlib.Data.Fintype.Fin

/-! Exact horizontal and vertical position counts for a literal finite path. -/
set_option autoImplicit false
namespace KroneckerOrientationPositions
open KroneckerStack KroneckerWordCounts

abbrev Positions (U : List Bool) (b : Bool) := {i : Fin U.length // U[i.val]=b}

set_option backward.isDefEq.respectTransparency false in
theorem positions_card (U : List Bool) (b : Bool) :
    Fintype.card (Positions U b)=U.count b := by
  have h := Fin.card_filter_univ_eq_vector_get_eq_count b (⟨U,rfl⟩ : List.Vector Bool U.length)
  simpa [Positions, Fintype.card_subtype, List.Vector.get] using h

theorem runWord_horizontal_count (rs : List ℕ) : (runWord rs).count true=rs.length := by
  induction rs with
  | nil => simp [runWord]
  | cons r rs ih => simpa [runWord,runShape,List.count_replicate] using ih


end KroneckerOrientationPositions
