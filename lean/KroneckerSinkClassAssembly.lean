import KroneckerColoredTableTranspose
import KroneckerSourceClassAssembly

/- Original module: KroneckerColoredSinkAttachment -/
section
set_option autoImplicit false
namespace KroneckerColoredSinkAttachment
open KroneckerFiniteColoredTables KroneckerBipartiteIncidence KroneckerColoredTableTranspose
open KroneckerColoredSourceAttachment KroneckerSourceAttachmentTree
attribute [local instance] Classical.propDecidable

variable {K : Type} {I J : K → Type}
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,I k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k j,(T k).code (r k) j≠some (c k))

noncomputable def sinkAttachment : ColoredTable (Σ k,I k) (Option (Σ k,J k)) :=
  transposeTable (sourceAttachment (fun k => transposeTable (T k)) r c hc hr)

theorem sink_attachment_root_code (k : K) (i : I k) :
    (sinkAttachment T r c hc hr).code ⟨k,i⟩ none=
      if i=r k then some (c k) else none :=
  attachment_root_code (fun k => transposeTable (T k)) r c hc hr k i

theorem sink_attachment_internal_code (k : K) (i : I k) (j : J k) :
    (sinkAttachment T r c hc hr).code ⟨k,i⟩ (some ⟨k,j⟩)=(T k).code i j :=
  attachment_internal_code (fun k => transposeTable (T k)) r c hc hr k j i

theorem sink_attachment_cross_code {k l : K} (h : k≠l) (i : I k) (j : J l) :
    (sinkAttachment T r c hc hr).code ⟨k,i⟩ (some ⟨l,j⟩)=none :=
  attachment_cross_code (fun k => transposeTable (T k)) r c hc hr h.symm j i

theorem sink_attachment_tree [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
    (hT : ∀ k,(incidenceGraph (Incidence (T k))).IsTree) :
    (incidenceGraph (Incidence (sinkAttachment T r c hc hr))).IsTree := by
  apply (transpose_tree_iff _).mpr
  exact source_attachment_tree _ r c hc hr (fun k => (transpose_tree_iff (T k)).mpr (hT k))

end KroneckerColoredSinkAttachment
end

/- Original module: KroneckerSinkAssemblyLeafDictionary -/
section
set_option autoImplicit false
namespace KroneckerSinkAssemblyLeafDictionary
open KroneckerFiniteColoredTables KroneckerColoredSinkAttachment KroneckerColoredTableTranspose
open KroneckerColoredSourceAttachment KroneckerSourceAttachmentNeighbors KroneckerSourceAttachmentColors
open KroneckerTableLeafMarks KroneckerSinkBranchLeafProfile
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {K : Type} {I J : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)]
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,I k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k j,(T k).code (r k) j≠some (c k))

set_option backward.isDefEq.respectTransparency false in
theorem sink_assembly_old_leaf (k : K) (j : J k) (e : Fin 3) :
    LeafMark (sinkAttachment T r c hc hr) e (some ⟨k,j⟩) ↔ LeafMark (T k) e j := by
  unfold LeafMark
  change (Fintype.card {i // Incidence
    (sourceAttachment (fun k => transposeTable (T k)) r c hc hr) (some ⟨k,j⟩) i}=1 ∧
    ∃ i,(sourceAttachment (fun k => transposeTable (T k)) r c hc hr).code (some ⟨k,j⟩) i=some e) ↔ _
  rw [attachment_internal_degree,attachment_component_colors]
  rfl

theorem sink_assembly_nonroot_leaf (d e : Fin 3) (k : K) (j : J k) :
    SinkLeaf (sinkAttachment T r c hc hr) none d e (some ⟨k,j⟩) ↔ LeafMark (T k) e j := by
  simp only [SinkLeaf,ne_eq,reduceCtorEq,not_false_eq_true,true_and,false_and,or_false]
  exact sink_assembly_old_leaf T r c hc hr k j e

theorem sink_assembly_root_leaf (d e : Fin 3) :
    SinkLeaf (sinkAttachment T r c hc hr) none d e none ↔ IsEmpty K ∧ e=d := by
  rw [sink_leaf_root]
  apply and_congr_left
  intro _
  constructor
  · intro h
    exact ⟨fun k => h ⟨k,r k⟩ ⟨c k,by rw [sink_attachment_root_code,ite_eq_left rfl]⟩⟩
  · intro h i
    exact False.elim (h.false i.1)

theorem sink_assembly_leaf_count [∀ k,Fintype (J k)] (d e : Fin 3) :
    Fintype.card {j // SinkLeaf (sinkAttachment T r c hc hr) none d e j}=
      (∑ k,Fintype.card {j // LeafMark (T k) e j})+(if IsEmpty K ∧ e=d then 1 else 0) := by
  simp only [Fintype.card_subtype,Finset.card_filter,Fintype.sum_option,Fintype.sum_sigma,
    sink_assembly_nonroot_leaf,sink_assembly_root_leaf]
  omega

end KroneckerSinkAssemblyLeafDictionary
end

/- Original module: KroneckerSinkAssemblyWeights -/
section
set_option autoImplicit false
namespace KroneckerSinkAssemblyWeights
open KroneckerFiniteColoredTables KroneckerColoredSinkAttachment KroneckerTableLeafMarks
open KroneckerSinkBranchLeafProfile KroneckerBranchWeights KroneckerGradedProfileWeights
open KroneckerSinkAssemblyLeafDictionary
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {R : Type*} [CommSemiring R] {K : Type} {I J : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]

/-- The isolated-root alternative contributes the parent-color variable; occupied ports contribute child products. -/
theorem sink_assembly_weight (T : ∀ k,ColoredTable (I k) (J k))
    (r : ∀ k,I k) (c : K → Fin 3) (hc : Function.Injective c)
    (hr : ∀ k j,(T k).code (r k) j≠some (c k))
    (d : Fin 3) (x : R) (y : Fin 3 → R) :
    sinkWeight (sinkAttachment T r c hc hr) none d x y=
      if IsEmpty K then y d else ∏ k,sourceWeight (T k) x y := by
  classical
  unfold sinkWeight sourceWeight
  simp only [Fintype.card_sigma,sink_assembly_leaf_count]
  by_cases he : IsEmpty K
  · let : IsEmpty K := he
    simp only [he,ite_true,Finset.univ_eq_empty,Finset.sum_empty,Nat.zero_add,true_and]
    exact graded_weight_leaf x y d
  · simp only [he,false_and,ite_false,Nat.add_zero]
    exact graded_weight_sum x y _ _

end KroneckerSinkAssemblyWeights
end

/- Original module: KroneckerSinkAttachmentClassification -/
section
set_option autoImplicit false
namespace KroneckerSinkAttachmentClassification
open KroneckerFiniteColoredTables KroneckerBipartiteIncidence KroneckerColoredIncidenceIso
open KroneckerColoredTableTranspose KroneckerColoredSinkAttachment KroneckerAttachmentClassification
open KroneckerAttachmentIsomorphisms

variable {K : Type} {I J I' J' : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
variable [∀ k,Fintype (I' k)] [∀ k,Fintype (J' k)]
variable (T : ∀ k,ColoredTable (I k) (J k)) (U : ∀ k,ColoredTable (I' k) (J' k))
variable (r : ∀ k,I k) (s : ∀ k,I' k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k j,(T k).code (r k) j≠some (c k))
variable (hs : ∀ k j,(U k).code (s k) j≠some (c k))

/-- Sink-rooted assemblies have the same exact component-class classification, with the bipartition reversed. -/
theorem sink_attachment_iso_iff
    (hT : ∀ k,(incidenceGraph (Incidence (T k))).IsTree)
    (hU : ∀ k,(incidenceGraph (Incidence (U k))).IsTree) :
    (∃ e : ColoredIso (coloring (sinkAttachment T r c hc hr))
      (coloring (sinkAttachment U s c hc hs)),e.sink none=none) ↔
    ∀ k,∃ e : ColoredIso (coloring (T k)) (coloring (U k)),e.source (r k)=s k := by
  have h := source_attachment_iso_iff (fun k => transposeTable (T k))
    (fun k => transposeTable (U k)) r s c hc hr hs
    (fun k => (transpose_tree_iff _).mpr (hT k)) (fun k => (transpose_tree_iff _).mpr (hU k))
  constructor
  · rintro ⟨e,he⟩ k
    obtain ⟨f,hf⟩ := h.mp ⟨transposeColoredIso e,he⟩ k
    exact ⟨transposeColoredIso f,hf⟩
  · intro h'
    have hh : ∀ k,∃ e : ColoredIso (coloring (transposeTable (T k)))
        (coloring (transposeTable (U k))),e.sink (r k)=s k := by
      intro k
      obtain ⟨e,he⟩ := h' k
      exact ⟨transposeColoredIso e,he⟩
    obtain ⟨e,he⟩ := h.mpr hh
    exact ⟨transposeColoredIso e,he⟩

end KroneckerSinkAttachmentClassification
end

/- Original module: KroneckerSinkBranchAssembly -/
section
set_option autoImplicit false
namespace KroneckerSinkBranchAssembly
open KroneckerFiniteColoredTables KroneckerBipartiteIncidence KroneckerColoredSinkAttachment
open KroneckerLeafDeletedSourceBranch KroneckerOutgoingSinkBranches

variable {K : Type} {I J : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,I k) (c : K → Fin 3)

/-- Every optional family at distinct nonparent colors supplies a sink branch, including no children. -/
theorem assemble_sink_branch (d : Fin 3) (hc : Function.Injective c)
    (hd : ∀ k,c k≠d) (hT : ∀ k,IsSourceBranch (T k) (r k) (c k)) :
    IsSinkBranch (sinkAttachment T r c hc (fun k => source_branch_parent_color_absent (hT k))) none d := by
  refine ⟨sink_attachment_tree T r c hc _ (fun k => (hT k).1),?_,?_⟩
  · rintro ⟨k,i⟩ e
    by_cases hi : i=r k
    · by_cases he : e=c k
      · refine ⟨none,?_⟩
        rw [sink_attachment_root_code,ite_eq_left hi,he]
      · obtain ⟨j,hj⟩ := ((hT k).2 i e).mpr (Or.inr he)
        exact ⟨some ⟨k,j⟩,(sink_attachment_internal_code T r c hc _ k i j).trans hj⟩
    · obtain ⟨j,hj⟩ := ((hT k).2 i e).mpr (Or.inl hi)
      exact ⟨some ⟨k,j⟩,(sink_attachment_internal_code T r c hc _ k i j).trans hj⟩
  · rintro ⟨k,i⟩ h
    rw [sink_attachment_root_code] at h
    by_cases hi : i=r k
    · rw [ite_eq_left hi] at h
      exact hd k (Option.some.inj h)
    · simp [hi] at h

theorem sink_assembly_grade : Fintype.card (Σ k,I k)=∑ k,Fintype.card (I k) :=
  Fintype.card_sigma

end KroneckerSinkBranchAssembly
end

/- Original module: KroneckerSinkClassAssembly -/
section
set_option autoImplicit false
namespace KroneckerSinkClassAssembly
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerFiniteBranchClasses
open KroneckerBranchClassRelations KroneckerCanonicalBranchClasses KroneckerColoredIncidenceIso
open KroneckerSourceClassAssembly KroneckerColoredSinkAttachment KroneckerSinkBranchAssembly
open KroneckerSinkAttachmentClassification KroneckerLeafDeletedSourceBranch
open KroneckerBranchClassWeights KroneckerSinkAssemblyWeights KroneckerBranchWeights
open KroneckerColoredTableTranspose KroneckerSourceAttachmentColors
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {d : Fin 3}

def occupiedColor (s : Finset (OtherColors d)) (k : s) : Fin 3 := k.1.1

theorem occupied_color_injective (s : Finset (OtherColors d)) : Function.Injective (occupiedColor s) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

noncomputable def assembleSinkObjects (s : Finset (OtherColors d)) {I J : s → Type}
    [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
    (S : ∀ k,SourceObject (I k) (J k) (occupiedColor s k)) :
    SinkObject (Σ k,I k) (Option (Σ k,J k)) d :=
  ⟨(sinkAttachment (fun k => (S k).1.1) (fun k => (S k).1.2) (occupiedColor s)
    (occupied_color_injective s) (fun k => source_branch_parent_color_absent (S k).2),none),
    assemble_sink_branch _ _ _ d (occupied_color_injective s) (fun k => k.1.2) (fun k => (S k).2)⟩

theorem sink_objects_class_iff (s : Finset (OtherColors d)) {I J I' J' : s → Type}
    [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
    [∀ k,Fintype (I' k)] [∀ k,Fintype (J' k)]
    (S : ∀ k,SourceObject (I k) (J k) (occupiedColor s k))
    (T : ∀ k,SourceObject (I' k) (J' k) (occupiedColor s k))
    {N : ℕ} (h : Fintype.card (Σ k,I k)=N) (h' : Fintype.card (Σ k,I' k)=N) :
    sinkClassOf (assembleSinkObjects s S) h=sinkClassOf (assembleSinkObjects s T) h' ↔
      ∀ k,∃ e : ColoredIso (coloring (S k).1.1) (coloring (T k).1.1),
        e.source (S k).1.2=(T k).1.2 := by
  rw [sink_class_of_eq_iff]
  exact sink_attachment_iso_iff _ _ _ _ _ (occupied_color_injective s)
    (fun k => source_branch_parent_color_absent (S k).2)
    (fun k => source_branch_parent_color_absent (T k).2)
    (fun k => (S k).2.1) (fun k => (T k).2.1)

noncomputable def sinkFromObjects (s : Finset (OtherColors d)) (n : s → ℕ)
    (S : ∀ k,SourceObject (Fin (n k)) (Fin (2*n k)) (occupiedColor s k)) :
    SinkDegreeClass (∑ k,n k) d :=
  sinkClassOf (assembleSinkObjects s S) (by simp [Fintype.card_sigma])

noncomputable def sinkFromClasses (s : Finset (OtherColors d)) (n : s → ℕ)
    (q : ∀ k,SourceDegreeClass (n k) (occupiedColor s k)) : SinkDegreeClass (∑ k,n k) d :=
  sinkFromObjects s n (fun k => (q k).out)

theorem sink_from_classes_representatives (s : Finset (OtherColors d)) (n : s → ℕ)
    (S : ∀ k,SourceObject (Fin (n k)) (Fin (2*n k)) (occupiedColor s k)) :
    sinkFromClasses s n (fun k => Quotient.mk'' (S k))=sinkFromObjects s n S := by
  apply (sink_objects_class_iff _ _ _ _ _).mpr
  intro k
  exact Quotient.exact (Quotient.out_eq' (Quotient.mk'' (S k) : SourceDegreeClass (n k) (occupiedColor s k)))

theorem sink_from_classes_injective (s : Finset (OtherColors d)) (n : s → ℕ) :
    Function.Injective (sinkFromClasses s n) := by
  intro q q' h
  have hc := (sink_objects_class_iff _ _ _ _ _).mp h
  funext k
  have he : (Quotient.mk'' (q k).out : SourceDegreeClass (n k) (occupiedColor s k))=
      Quotient.mk'' (q' k).out := Quotient.sound (hc k)
  simpa only [Quotient.out_eq'] using he

set_option backward.isDefEq.respectTransparency false in
theorem sink_from_classes_weight {R : Type*} [CommSemiring R]
    (s : Finset (OtherColors d)) (n : s → ℕ)
    (q : ∀ k,SourceDegreeClass (n k) (occupiedColor s k)) (x : R) (y : Fin 3 → R) :
    sinkClassWeight x y (sinkFromClasses s n q)=
      if IsEmpty s then y d else ∏ k,sourceClassWeight x y (q k) := by
  rw [sinkFromClasses,sinkFromObjects,canonical_sink_weight]
  dsimp only [assembleSinkObjects]
  rw [sink_assembly_weight]
  split_ifs
  · rfl
  · apply Finset.prod_congr rfl
    intro k _
    exact congrArg (sourceClassWeight x y) (Quotient.out_eq' (q k))

/-- Occupancy is exactly recoverable from the root colors of the assembled table. -/
theorem sink_objects_occupied (s : Finset (OtherColors d)) {I J : s → Type}
    [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
    (S : ∀ k,SourceObject (I k) (J k) (occupiedColor s k)) (e : OtherColors d) :
    (∃ i,(assembleSinkObjects s S).1.1.code i none=some e.1) ↔ e∈s := by
  have h := attachment_root_colors (fun k => transposeTable (S k).1.1)
    (fun k => (S k).1.2) (occupiedColor s) (occupied_color_injective s)
    (fun k => source_branch_parent_color_absent (S k).2) e.1
  change (∃ i,(assembleSinkObjects s S).1.1.code i none=some e.1) ↔ _ at h
  rw [h]
  constructor
  · rintro ⟨k,hk⟩
    have he : k.1=e := Subtype.ext hk
    exact he ▸ k.2
  · intro he
    exact ⟨⟨e,he⟩,rfl⟩

end KroneckerSinkClassAssembly
end
