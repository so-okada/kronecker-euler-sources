import KroneckerColoredLeafTransport

set_option autoImplicit false
namespace KroneckerFiniteColoredTables
open KroneckerProperColoredReflection KroneckerColoredIncidenceIso KroneckerColoredAutomorphismGroup
attribute [local instance] Classical.propDecidable

/-- An actual finite colored incidence table: `none` is an absent edge. -/
structure ColoredTable (I J : Type) where
  code : I → J → Option (Fin 3)
  atSource : ∀ i j k d,code i j=some d → code i k=some d → j=k
  atSink : ∀ i k j d,code i j=some d → code k j=some d → i=k

variable {I J : Type}

theorem table_ext {T U : ColoredTable I J} (h : T.code=U.code) : T=U := by
  cases T; cases U; cases h; rfl

noncomputable instance [Fintype I] [Fintype J] : Fintype (ColoredTable I J) := by
  classical
  exact Fintype.ofInjective ColoredTable.code (fun _ _ => table_ext)

def Incidence (T : ColoredTable I J) (i : I) (j : J) : Prop := ∃ d,T.code i j=some d

noncomputable def coloring (T : ColoredTable I J) : ProperColoring (Incidence T) where
  color := fun _ _ h => Classical.choose h
  at_source := by
    intro i j k h
    change Classical.choose j.2=Classical.choose k.2 at h
    apply Subtype.ext
    exact T.atSource i j k (Classical.choose j.2) (Classical.choose_spec j.2)
      (by rw [h]; exact Classical.choose_spec k.2)
  at_sink := by
    intro j i k h
    change Classical.choose i.2=Classical.choose k.2 at h
    apply Subtype.ext
    exact T.atSink i k j (Classical.choose i.2) (Classical.choose_spec i.2)
      (by rw [h]; exact Classical.choose_spec k.2)

theorem code_color (T : ColoredTable I J) (i : I) (j : J) (h : Incidence T i j) :
    T.code i j=some ((coloring T).color i j h) := Classical.choose_spec h

theorem code_eq_some_iff (T : ColoredTable I J) (i : I) (j : J) (d : Fin 3) :
    T.code i j=some d ↔ ∃ h : Incidence T i j,(coloring T).color i j h=d := by
  constructor
  · intro h
    exact ⟨⟨d,h⟩,Option.some.inj ((code_color T i j ⟨d,h⟩).symm.trans h)⟩
  · rintro ⟨h,rfl⟩
    exact code_color T i j h

noncomputable def ofColoring {R : I → J → Prop} (C : ProperColoring R) : ColoredTable I J where
  code i j := if h : R i j then some (C.color i j h) else none
  atSource := by
    intro i j k d hj hk
    by_cases h₁ : R i j
    · by_cases h₂ : R i k
      · simp only [dite_eq_left h₁] at hj
        simp only [dite_eq_left h₂] at hk
        exact congrArg Subtype.val (C.at_source i (a₁:=⟨j,h₁⟩) (a₂:=⟨k,h₂⟩)
          (Option.some.inj (hj.trans hk.symm)))
      · simp [h₂] at hk
    · simp [h₁] at hj
  atSink := by
    intro i k j d hi hk
    by_cases h₁ : R i j
    · by_cases h₂ : R k j
      · simp only [dite_eq_left h₁] at hi
        simp only [dite_eq_left h₂] at hk
        exact congrArg Subtype.val (C.at_sink j (a₁:=⟨i,h₁⟩) (a₂:=⟨k,h₂⟩)
          (Option.some.inj (hi.trans hk.symm)))
      · simp [h₂] at hk
    · simp [h₁] at hi

theorem of_coloring_incidence {R : I → J → Prop} (C : ProperColoring R) (i : I) (j : J) :
    Incidence (ofColoring C) i j ↔ R i j := by
  simp only [Incidence,ofColoring]
  split_ifs with h <;> simp [h]

noncomputable def ofColoringIso {R : I → J → Prop} (C : ProperColoring R) :
    ColoredIso C (coloring (ofColoring C)) where
  source := Equiv.refl I
  sink := Equiv.refl J
  incidence := of_coloring_incidence C
  color := by
    intro i j h
    apply Option.some.inj
    exact (code_color (ofColoring C) i j _).symm.trans (by simp [ofColoring,h])


end KroneckerFiniteColoredTables
