import KroneckerManuscriptBlockStatements
import KroneckerReadableMain

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace KroneckerManuscriptFixedCoverCount
open KroneckerMarkedLatticeInputs KroneckerLatticeFamilyCounting
open KroneckerEnumeratedCoverClasses KroneckerStableChainCoverData
open KroneckerScopedModuli KroneckerScopedWeistApplication KroneckerOrdinarySingularEuler

variable {n a : ℕ} {x : ℝ} (hx : 100000 ≤ x) (ha : ((n : ℝ)+2)*x=a)

theorem inputs_subset_enumerated : inputs hx ha ⊆ enumeratedInputs hx ha := by
  intro X hX
  obtain ⟨Y,_,rfl⟩ := Finset.mem_image.mp hX
  exact Finset.mem_image.mpr ⟨includeMarked hx ha Y,Finset.mem_univ _,rfl⟩

theorem coverClasses_subset_enumerated : coverClasses hx ha ⊆ enumeratedCoverClasses hx ha := by
  intro q hq
  obtain ⟨X,_,rfl⟩ := Finset.mem_image.mp hq
  let Y : {X // X ∈ enumeratedInputs hx ha} :=
    ⟨X.val,inputs_subset_enumerated hx ha X.property⟩
  exact Finset.mem_image.mpr ⟨Y,Finset.mem_attach _ _,rfl⟩

theorem fixed_cover_localization (G : Geometry) (W : Weist G) (hc : a.Coprime (n+2)) :
    ((coverClasses hx ha).card : ℤ) ≤
      ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+n+2))
        (baseAdmissible G a (a+n+2)) := by
  have hc' : ((coverClasses hx ha).card : ℤ) ≤ (enumeratedCoverClasses hx ha).card := by
    exact_mod_cast Finset.card_le_card (coverClasses_subset_enumerated hx ha)
  exact hc'.trans (KroneckerScopedWeistCountedLower.counted_card_le G W n a x hx ha hc)

theorem fixed_cover_localization_manuscript (hc : a.Coprime (n+2)) :
    ((coverClasses hx ha).card : ℤ) ≤
      ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+n+2))
        (baseAdmissible KroneckerReadableMain.geometry a (a+n+2)) :=
  fixed_cover_localization hx ha KroneckerReadableMain.geometry KroneckerReadableMain.localization hc

end KroneckerManuscriptFixedCoverCount
#print axioms KroneckerManuscriptFixedCoverCount.fixed_cover_localization_manuscript
