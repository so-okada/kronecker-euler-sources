import KroneckerQuiverPullbackComposition

/-! Arrow equivalences transport the full character group of an abelian cover,
including each distinguished unit displacement and composition of transports. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbelianCharacterReindex
open KroneckerAbelianCover
variable {A B C : Type}
attribute [local instance] Classical.decEq Classical.propDecidable

def reindex (e : A ≃ B) : Character A ≃+ Character B where
  toFun χ b := χ (e.symm b)
  invFun ψ a := ψ (e a)
  left_inv χ := by funext a; simp
  right_inv ψ := by funext b; simp
  map_add' χ ψ := rfl

theorem reindex_apply (e : A ≃ B) (χ : Character A) (b : B) : reindex e χ b = χ (e.symm b) := rfl

theorem reindex_unit (e : A ≃ B) (a : A) : reindex e (unit a) = unit (e a) := by
  funext b
  change unit a (e.symm b) = unit (e a) b
  by_cases h : b = e a
  · subst b
    rw [e.symm_apply_apply]
    simp [unit]
  · have h' : e.symm b ≠ a := by
      intro he
      apply h
      simpa using congrArg e he
    simp [unit,h,h']

theorem reindex_refl (χ : Character A) : reindex (Equiv.refl A) χ = χ := rfl

theorem reindex_trans (e : A ≃ B) (f : B ≃ C) (χ : Character A) :
    reindex (e.trans f) χ = reindex f (reindex e χ) := rfl

theorem reindex_symm (e : A ≃ B) (χ : Character A) : reindex e.symm (reindex e χ) = χ := by
  funext a
  simp [reindex]

end KroneckerAbelianCharacterReindex
