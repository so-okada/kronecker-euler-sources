import KroneckerBranchObjectTransport
import KroneckerBranchClassWeights

/- Original module: KroneckerBranchNormalForms -/
section
set_option autoImplicit false
namespace KroneckerBranchNormalForms
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerBranchObjectTransport
open KroneckerColoredTableTransport KroneckerColoredIncidenceIso

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}

noncomputable def sourceNormalForm (S : SourceObject I J d) :
    SourceObject (Fin (Fintype.card I)) (Fin (2*Fintype.card I)) d :=
  transportSourceObject S (Fintype.equivFin I)
    (Fintype.equivOfCardEq (by rw [Fintype.card_fin]; exact source_object_dimensions S))

noncomputable def sinkNormalForm (S : SinkObject I J d) :
    SinkObject (Fin (Fintype.card I)) (Fin (2*Fintype.card I+1)) d :=
  transportSinkObject S (Fintype.equivFin I)
    (Fintype.equivOfCardEq (by rw [Fintype.card_fin]; exact sink_object_dimensions S))



end KroneckerBranchNormalForms
end

/- Original module: KroneckerCanonicalBranchClasses -/
section
set_option autoImplicit false
namespace KroneckerCanonicalBranchClasses
section Part0
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerBranchObjectTransport
open KroneckerColoredTableTransport KroneckerColoredIncidenceIso

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3} {n : ℕ}

/-- Normalize to a specified source degree, with its actual cardinality as evidence. -/
noncomputable def sourceAtDegree (S : SourceObject I J d) (h : Fintype.card I=n) :
    SourceObject (Fin n) (Fin (2*n)) d :=
  transportSourceObject S (Fintype.equivOfCardEq (by simpa using h))
    (Fintype.equivOfCardEq (by simpa [h] using source_object_dimensions S))

noncomputable def sinkAtDegree (S : SinkObject I J d) (h : Fintype.card I=n) :
    SinkObject (Fin n) (Fin (2*n+1)) d :=
  transportSinkObject S (Fintype.equivOfCardEq (by simpa using h))
    (Fintype.equivOfCardEq (by simpa [h] using sink_object_dimensions S))

theorem source_at_degree_iso (S : SourceObject I J d) (h : Fintype.card I=n) :
    ∃ e : ColoredIso (coloring S.1.1) (coloring (sourceAtDegree S h).1.1),
      e.source S.1.2=(sourceAtDegree S h).1.2 :=
  ⟨transportIso S.1.1 _ _,rfl⟩

theorem sink_at_degree_iso (S : SinkObject I J d) (h : Fintype.card I=n) :
    ∃ e : ColoredIso (coloring S.1.1) (coloring (sinkAtDegree S h).1.1),
      e.sink S.1.2=(sinkAtDegree S h).1.2 :=
  ⟨transportIso S.1.1 _ _,rfl⟩

end Part0

section Part1
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerFiniteBranchClasses
open KroneckerBranchClassRelations KroneckerColoredIncidenceIso

variable {I J I' J' : Type} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
variable {d : Fin 3} {n : ℕ}

noncomputable def sourceClassOf (S : SourceObject I J d) (h : Fintype.card I=n) :
    SourceDegreeClass n d := Quotient.mk'' (sourceAtDegree S h)
noncomputable def sinkClassOf (S : SinkObject I J d) (h : Fintype.card I=n) :
    SinkDegreeClass n d := Quotient.mk'' (sinkAtDegree S h)

/-- Equality of canonical classes detects the actual pointed isomorphism across different carriers. -/
theorem source_class_of_eq_iff (S : SourceObject I J d) (T : SourceObject I' J' d)
    (h : Fintype.card I=n) (h' : Fintype.card I'=n) :
    sourceClassOf S h=sourceClassOf T h' ↔
      ∃ e : ColoredIso (coloring S.1.1) (coloring T.1.1),e.source S.1.2=T.1.2 := by
  obtain ⟨a,ha⟩ := source_at_degree_iso S h
  obtain ⟨b,hb⟩ := source_at_degree_iso T h'
  unfold sourceClassOf
  rw [source_class_eq_iff]
  constructor
  · rintro ⟨e,he⟩
    refine ⟨a.trans (e.trans b.symm),?_⟩
    change b.source.symm (e.source (a.source S.1.2))=T.1.2
    rw [ha,he,←hb,Equiv.symm_apply_apply]
  · rintro ⟨e,he⟩
    refine ⟨a.symm.trans (e.trans b),?_⟩
    change b.source (e.source (a.source.symm (sourceAtDegree S h).1.2))=(sourceAtDegree T h').1.2
    rw [←ha,Equiv.symm_apply_apply,he,hb]

theorem sink_class_of_eq_iff (S : SinkObject I J d) (T : SinkObject I' J' d)
    (h : Fintype.card I=n) (h' : Fintype.card I'=n) :
    sinkClassOf S h=sinkClassOf T h' ↔
      ∃ e : ColoredIso (coloring S.1.1) (coloring T.1.1),e.sink S.1.2=T.1.2 := by
  obtain ⟨a,ha⟩ := sink_at_degree_iso S h
  obtain ⟨b,hb⟩ := sink_at_degree_iso T h'
  unfold sinkClassOf
  rw [sink_class_eq_iff]
  constructor
  · rintro ⟨e,he⟩
    refine ⟨a.trans (e.trans b.symm),?_⟩
    change b.sink.symm (e.sink (a.sink S.1.2))=T.1.2
    rw [ha,he,←hb,Equiv.symm_apply_apply]
  · rintro ⟨e,he⟩
    refine ⟨a.symm.trans (e.trans b),?_⟩
    change b.sink (e.sink (a.sink.symm (sinkAtDegree S h).1.2))=(sinkAtDegree T h').1.2
    rw [←ha,Equiv.symm_apply_apply,he,hb]

theorem source_class_of_canonical (S : SourceObject (Fin n) (Fin (2*n)) d) :
    sourceClassOf S (Fintype.card_fin n)=Quotient.mk'' S := by
  obtain ⟨e,he⟩ := source_at_degree_iso S (Fintype.card_fin n)
  apply Quotient.sound
  refine ⟨e.symm,?_⟩
  change e.source.symm (sourceAtDegree S _).1.2=S.1.2
  rw [←he,Equiv.symm_apply_apply]

theorem sink_class_of_canonical (S : SinkObject (Fin n) (Fin (2*n+1)) d) :
    sinkClassOf S (Fintype.card_fin n)=Quotient.mk'' S := by
  obtain ⟨e,he⟩ := sink_at_degree_iso S (Fintype.card_fin n)
  apply Quotient.sound
  refine ⟨e.symm,?_⟩
  change e.sink.symm (sinkAtDegree S _).1.2=S.1.2
  rw [←he,Equiv.symm_apply_apply]

end Part1

section Part2
open KroneckerFiniteBranchObjects
open KroneckerBranchClassWeights KroneckerBranchWeights

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3} {n : ℕ}
variable {R : Type*} [CommSemiring R]

theorem canonical_source_weight (S : SourceObject I J d) (h : Fintype.card I=n)
    (x : R) (y : Fin 3 → R) :
    sourceClassWeight x y (sourceClassOf S h)=sourceWeight S.1.1 x y := by
  obtain ⟨e,_⟩ := source_at_degree_iso S h
  exact (source_weight_iso e x y).symm

theorem canonical_sink_weight (S : SinkObject I J d) (h : Fintype.card I=n)
    (x : R) (y : Fin 3 → R) :
    sinkClassWeight x y (sinkClassOf S h)=sinkWeight S.1.1 S.1.2 d x y := by
  obtain ⟨e,he⟩ := sink_at_degree_iso S h
  have hw := sink_weight_iso e S.1.2 d x y
  rw [he] at hw
  exact hw.symm

end Part2

end KroneckerCanonicalBranchClasses
end
