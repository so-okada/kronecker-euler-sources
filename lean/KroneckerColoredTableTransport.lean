import KroneckerTableIsomorphisms

section

set_option autoImplicit false
namespace KroneckerColoredTableRestrictions
open KroneckerFiniteColoredTables KroneckerBipartiteIncidence

variable {I J I' J' : Type}

def comapTable (T : ColoredTable I J) (s : I' ↪ I) (t : J' ↪ J) : ColoredTable I' J' where
  code i j := T.code (s i) (t j)
  atSource _ _ _ d hj hk := t.injective (T.atSource _ _ _ d hj hk)
  atSink _ _ _ d hi hk := s.injective (T.atSink _ _ _ d hi hk)

/-- Restriction retains the actual option-valued colored incidences. -/
def restrictTable (T : ColoredTable I J) (P : I → Prop) (Q : J → Prop) :
    ColoredTable {i // P i} {j // Q j} :=
  comapTable T (Function.Embedding.subtype P) (Function.Embedding.subtype Q)

def restrictedVertexEquiv (P : I → Prop) (Q : J → Prop) :
    ({i // P i} ⊕ {j // Q j}) ≃ {v : I ⊕ J // Sum.elim P Q v} where
  toFun
    | .inl i => ⟨.inl i.1,i.2⟩
    | .inr j => ⟨.inr j.1,j.2⟩
  invFun v := match v with
    | ⟨.inl i,h⟩ => .inl ⟨i,h⟩
    | ⟨.inr j,h⟩ => .inr ⟨j,h⟩
  left_inv := by intro v; cases v <;> rfl
  right_inv := by rintro ⟨v,h⟩; cases v <;> rfl

def restrictionGraphIso (T : ColoredTable I J) (P : I → Prop) (Q : J → Prop) :
    incidenceGraph (Incidence (restrictTable T P Q)) ≃g
      (incidenceGraph (Incidence T)).induce {v | Sum.elim P Q v} where
  toEquiv := restrictedVertexEquiv P Q
  map_rel_iff' := by intro u v; cases u <;> cases v <;> rfl

def restrictSinkTable (T : ColoredTable I J) (Q : J → Prop) : ColoredTable I {j // Q j} :=
  comapTable T (Function.Embedding.refl I) (Function.Embedding.subtype Q)

def restrictedSinkVertexEquiv (Q : J → Prop) :
    (I ⊕ {j // Q j}) ≃ {v : I ⊕ J // Sum.elim (fun _ => True) Q v} where
  toFun
    | .inl i => ⟨.inl i,True.intro⟩
    | .inr j => ⟨.inr j.1,j.2⟩
  invFun v := match v with
    | ⟨.inl i,_⟩ => .inl i
    | ⟨.inr j,h⟩ => .inr ⟨j,h⟩
  left_inv := by intro v; cases v <;> rfl
  right_inv := by rintro ⟨v,h⟩; cases v <;> rfl

def sinkRestrictionGraphIso (T : ColoredTable I J) (Q : J → Prop) :
    incidenceGraph (Incidence (restrictSinkTable T Q)) ≃g
      (incidenceGraph (Incidence T)).induce {v | Sum.elim (fun _ => True) Q v} where
  toEquiv := restrictedSinkVertexEquiv Q
  map_rel_iff' := by intro u v; cases u <;> cases v <;> rfl


end KroneckerColoredTableRestrictions
end

section

set_option autoImplicit false
namespace KroneckerColoredTableTransport
open KroneckerFiniteColoredTables KroneckerColoredTableRestrictions
open KroneckerColoredIncidenceIso KroneckerTableIsomorphisms

variable {I J I' J' : Type}

def transportTable (T : ColoredTable I J) (s : I ≃ I') (t : J ≃ J') : ColoredTable I' J' :=
  comapTable T s.symm.toEmbedding t.symm.toEmbedding

noncomputable def transportIso (T : ColoredTable I J) (s : I ≃ I') (t : J ≃ J') :
    ColoredIso (coloring T) (coloring (transportTable T s t)) :=
  isoOfCode _ _ s t (fun i j => by simp [transportTable,comapTable])

theorem transport_table_roundtrip (T : ColoredTable I J) (s : I ≃ I') (t : J ≃ J') :
    transportTable (transportTable T s t) s.symm t.symm=T := by
  apply table_ext
  funext i j
  simp [transportTable,comapTable]

theorem transport_table_composition {I'' J'' : Type}
    (T : ColoredTable I J) (s : I ≃ I') (t : J ≃ J') (u : I' ≃ I'') (v : J' ≃ J'') :
    transportTable (transportTable T s t) u v=transportTable T (s.trans u) (t.trans v) :=
  table_ext rfl

end KroneckerColoredTableTransport
end

