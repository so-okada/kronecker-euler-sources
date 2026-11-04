import KroneckerFiniteColoredTables

set_option autoImplicit false
namespace KroneckerTableIsomorphisms
open KroneckerFiniteColoredTables KroneckerColoredIncidenceIso KroneckerColoredAutomorphismGroup

variable {I J I' J' : Type} (T : ColoredTable I J) (U : ColoredTable I' J')

theorem iso_preserves_code (e : ColoredIso (coloring T) (coloring U)) (i : I) (j : J) :
    U.code (e.source i) (e.sink j)=T.code i j := by
  classical
  cases h : T.code i j with
  | none =>
    cases h' : U.code (e.source i) (e.sink j) with
    | none => rfl
    | some d =>
      obtain ⟨c,hc⟩ := (e.incidence i j).mp ⟨d,h'⟩
      rw [h] at hc
      contradiction
  | some d =>
    obtain ⟨hi,hd⟩ := (code_eq_some_iff T i j d).mp h
    exact (code_eq_some_iff U _ _ d).mpr ⟨(e.incidence i j).mpr hi,(e.color i j hi).trans hd⟩

noncomputable def isoOfCode (s : I ≃ I') (t : J ≃ J')
    (h : ∀ i j,U.code (s i) (t j)=T.code i j) : ColoredIso (coloring T) (coloring U) where
  source := s
  sink := t
  incidence := by intro i j; simp only [Incidence,h]
  color := by
    intro i j hr
    apply Option.some.inj
    exact (code_color U _ _ _).symm.trans ((h i j).trans (code_color T i j hr))



end KroneckerTableIsomorphisms
