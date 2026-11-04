import KroneckerSourceAttachmentColors
import KroneckerCanonicalBranchClasses
import KroneckerAttachmentClassification

/- Original module: KroneckerAttachmentSinkDegrees -/
section
set_option autoImplicit false
namespace KroneckerAttachmentSinkDegrees
open KroneckerFiniteColoredTables KroneckerColoredSourceAttachment
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {K : Type} {I J : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)]
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))

theorem attachment_sink_degree (k : K) (j : J k) :
    Fintype.card {i // Incidence (sourceAttachment T r c hc hr) i ⟨k,j⟩}=
      Fintype.card {i // Incidence (T k) i j}+(if j=r k then 1 else 0) := by
  classical
  simp only [Fintype.card_subtype,Finset.card_filter]
  rw [Fintype.sum_option,Fintype.sum_sigma,Finset.sum_eq_single k]
  · simp only [attachment_root_incidence,attachment_internal_incidence]
    omega
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro i _
    have hn : ¬Incidence (sourceAttachment T r c hc hr) (some ⟨l,i⟩) ⟨k,j⟩ := by
      rintro ⟨d,hd⟩
      rw [attachment_cross_code T r c hc hr hl i j] at hd
      contradiction
    simp [hn]
  · intro hn
    exact False.elim (hn (Finset.mem_univ k))

omit [Fintype K] [∀ k,Fintype (I k)] in
theorem attachment_sink_colors (k : K) (j : J k) (e : Fin 3) :
    (∃ i,(sourceAttachment T r c hc hr).code i ⟨k,j⟩=some e) ↔
      (∃ i,(T k).code i j=some e) ∨ (j=r k ∧ c k=e) := by
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | none =>
      exact Or.inr ((KroneckerSourceAttachmentEdges.attach_root_edge T r c k j e).mp
        ((attachment_code_iff T r c hc hr _ _ e).mp hi))
    | some p =>
      rcases p with ⟨l,i⟩
      have he : l=k := KroneckerSourceAttachmentEdges.attach_component_index T r c
        ((attachment_code_iff T r c hc hr _ _ e).mp hi)
      subst l
      exact Or.inl ⟨i,(attachment_internal_code T r c hc hr k i j).symm.trans hi⟩
  · rintro (⟨i,hi⟩ | ⟨hj,he⟩)
    · exact ⟨some ⟨k,i⟩,(attachment_internal_code T r c hc hr k i j).trans hi⟩
    · refine ⟨none,?_⟩
      rw [attachment_root_code,ite_eq_left hj,he]

end KroneckerAttachmentSinkDegrees
end

/- Original module: KroneckerSourceAssemblyLeafDictionary -/
section
set_option autoImplicit false
namespace KroneckerSourceAssemblyLeafDictionary
open KroneckerFiniteColoredTables KroneckerColoredSourceAttachment KroneckerTableLeafMarks
open KroneckerAttachmentSinkDegrees KroneckerSinkBranchLeafProfile
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {K : Type} {I J : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)]
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))

/-- Parent attachment realizes exactly the corrected sink-branch leaf convention. -/
theorem source_assembly_leaf_iff (k : K) (j : J k) (e : Fin 3) :
    LeafMark (sourceAttachment T r c hc hr) e ⟨k,j⟩ ↔ SinkLeaf (T k) (r k) (c k) e j := by
  have hz : Fintype.card {i // Incidence (T k) i (r k)}=0 ↔ ∀ i,¬Incidence (T k) i (r k) := by
    rw [Fintype.card_eq_zero_iff,isEmpty_subtype]
  by_cases hj : j=r k
  · subst j
    rw [sink_leaf_root]
    unfold LeafMark
    rw [attachment_sink_degree,attachment_sink_colors,ite_eq_left rfl]
    constructor
    · rintro ⟨hd,he⟩
      have hn := hz.mp (by omega)
      refine ⟨hn,?_⟩
      rcases he with ⟨i,hi⟩ | ⟨_,hi⟩
      · exact False.elim (hn i ⟨e,hi⟩)
      · exact hi.symm
    · rintro ⟨hn,he⟩
      have hd := hz.mpr hn
      exact ⟨by omega,Or.inr ⟨rfl,he.symm⟩⟩
  · simp only [SinkLeaf,ne_eq,hj,not_false_eq_true,true_and,false_and,or_false]
    unfold LeafMark
    rw [attachment_sink_degree,attachment_sink_colors,ite_eq_right hj]
    simp only [Nat.add_zero,hj,false_and,or_false]

theorem source_assembly_leaf_count [∀ k,Fintype (J k)] (e : Fin 3) :
    Fintype.card {j // LeafMark (sourceAttachment T r c hc hr) e j}=
      ∑ k,Fintype.card {j // SinkLeaf (T k) (r k) (c k) e j} := by
  simp only [Fintype.card_subtype,Finset.card_filter,Fintype.sum_sigma,source_assembly_leaf_iff]

end KroneckerSourceAssemblyLeafDictionary
end

/- Original module: KroneckerSourceAssemblyWeights -/
section
set_option autoImplicit false
namespace KroneckerSourceAssemblyWeights
open KroneckerFiniteColoredTables KroneckerColoredSourceAttachment KroneckerTableLeafMarks
open KroneckerSinkBranchLeafProfile KroneckerBranchWeights KroneckerGradedProfileWeights
open KroneckerSourceAssemblyLeafDictionary
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {R : Type*} [CommSemiring R] {K : Type} {I J : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]

/-- The factor x times the product of child weights is derived from the actual assembled table. -/
theorem source_assembly_weight (T : ∀ k,ColoredTable (I k) (J k))
    (r : ∀ k,J k) (c : K → Fin 3) (hc : Function.Injective c)
    (hr : ∀ k i,(T k).code i (r k)≠some (c k)) (x : R) (y : Fin 3 → R) :
    sourceWeight (sourceAttachment T r c hc hr) x y=
      x*∏ k,sinkWeight (T k) (r k) (c k) x y := by
  unfold sourceWeight sinkWeight
  simp only [Fintype.card_option,Fintype.card_sigma,source_assembly_leaf_count]
  have h := graded_weight_add x y (∑ k,Fintype.card (I k)) 1
    (fun e => ∑ k,Fintype.card {j // SinkLeaf (T k) (r k) (c k) e j}) (fun _ => 0)
  simp only [Nat.add_zero,graded_weight_source] at h
  rw [h,graded_weight_sum,mul_comm]

end KroneckerSourceAssemblyWeights
end

/- Original module: KroneckerSourceBranchAssembly -/
section
set_option autoImplicit false
namespace KroneckerSourceBranchAssembly
open KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerColoredSourceAttachment KroneckerSourceAttachmentTree KroneckerSourceAttachmentColors
open KroneckerOutgoingSinkBranches KroneckerLeafDeletedSourceBranch

variable {K : Type} {I J : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)

/-- Two actual sink branches at exactly the nonparent colors assemble to a source branch. -/
theorem assemble_source_branch (d : Fin 3) (hc : Function.Injective c)
    (hcolors : ∀ e,(∃ k,c k=e) ↔ e≠d)
    (hT : ∀ k,IsSinkBranch (T k) (r k) (c k)) :
    IsSourceBranch (sourceAttachment T r c hc (fun k => (hT k).2.2)) none d := by
  refine ⟨source_attachment_tree T r c hc _ (fun k => (hT k).1),?_⟩
  intro i e
  cases i with
  | none => simpa only [ne_eq,not_true_eq_false,false_or] using
      (attachment_root_colors T r c hc _ e).trans (hcolors e)
  | some p =>
    rw [attachment_component_colors]
    constructor
    · intro _; exact Or.inl (by simp)
    · intro _; exact (hT p.1).2.1 p.2 e

theorem source_assembly_grade :
    Fintype.card (Option (Σ k,I k))=1+∑ k,Fintype.card (I k) := by
  simp [Fintype.card_option,Fintype.card_sigma,Nat.add_comm]

end KroneckerSourceBranchAssembly
end

/- Original module: KroneckerSourceClassAssembly -/
section
set_option autoImplicit false
namespace KroneckerSourceClassAssembly
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerFiniteBranchClasses
open KroneckerBranchClassRelations KroneckerCanonicalBranchClasses KroneckerColoredIncidenceIso
open KroneckerColoredSourceAttachment KroneckerSourceBranchAssembly KroneckerAttachmentClassification
open KroneckerBranchClassWeights KroneckerSourceAssemblyWeights KroneckerBranchWeights
attribute [local instance] Classical.propDecidable
open scoped BigOperators

abbrev OtherColors (d : Fin 3) := {e : Fin 3 // e≠d}

variable {d : Fin 3}

theorem other_colors_range (e : Fin 3) : (∃ k : OtherColors d,k.1=e) ↔ e≠d := by
  constructor
  · rintro ⟨k,rfl⟩; exact k.2
  · intro h; exact ⟨⟨e,h⟩,rfl⟩

noncomputable def assembleSourceObjects {I J : OtherColors d → Type}
    [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
    (S : ∀ k,SinkObject (I k) (J k) k.1) :
    SourceObject (Option (Σ k,I k)) (Σ k,J k) d :=
  ⟨(sourceAttachment (fun k => (S k).1.1) (fun k => (S k).1.2) Subtype.val
    Subtype.val_injective (fun k => (S k).2.2.2),none),
    assemble_source_branch _ _ _ d Subtype.val_injective other_colors_range (fun k => (S k).2)⟩

theorem source_objects_class_iff {I J I' J' : OtherColors d → Type}
    [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
    [∀ k,Fintype (I' k)] [∀ k,Fintype (J' k)]
    (S : ∀ k,SinkObject (I k) (J k) k.1) (T : ∀ k,SinkObject (I' k) (J' k) k.1)
    {N : ℕ} (h : Fintype.card (Option (Σ k,I k))=N)
    (h' : Fintype.card (Option (Σ k,I' k))=N) :
    sourceClassOf (assembleSourceObjects S) h=sourceClassOf (assembleSourceObjects T) h' ↔
      ∀ k,∃ e : ColoredIso (coloring (S k).1.1) (coloring (T k).1.1),
        e.sink (S k).1.2=(T k).1.2 := by
  rw [source_class_of_eq_iff]
  exact source_attachment_iso_iff _ _ _ _ _ Subtype.val_injective
    (fun k => (S k).2.2.2) (fun k => (T k).2.2.2)
    (fun k => (S k).2.1) (fun k => (T k).2.1)

noncomputable def sourceFromObjects (n : OtherColors d → ℕ)
    (S : ∀ k,SinkObject (Fin (n k)) (Fin (2*n k+1)) k.1) :
    SourceDegreeClass ((∑ k,n k)+1) d :=
  sourceClassOf (assembleSourceObjects S) (by simp [Fintype.card_option,Fintype.card_sigma])

noncomputable def sourceFromClasses (n : OtherColors d → ℕ)
    (q : ∀ k,SinkDegreeClass (n k) k.1) : SourceDegreeClass ((∑ k,n k)+1) d :=
  sourceFromObjects n (fun k => (q k).out)

/-- Assembly on actual class representatives is independent of every representative choice. -/
theorem source_from_classes_representatives (n : OtherColors d → ℕ)
    (S : ∀ k,SinkObject (Fin (n k)) (Fin (2*n k+1)) k.1) :
    sourceFromClasses n (fun k => Quotient.mk'' (S k))=sourceFromObjects n S := by
  apply (source_objects_class_iff _ _ _ _).mpr
  intro k
  exact Quotient.exact (Quotient.out_eq' (Quotient.mk'' (S k) : SinkDegreeClass (n k) k.1))

theorem source_from_classes_injective (n : OtherColors d → ℕ) :
    Function.Injective (sourceFromClasses n) := by
  intro q q' h
  have hc := (source_objects_class_iff _ _ _ _).mp h
  funext k
  have he : (Quotient.mk'' (q k).out : SinkDegreeClass (n k) k.1)=Quotient.mk'' (q' k).out :=
    Quotient.sound (hc k)
  simpa only [Quotient.out_eq'] using he

/-- The weight of the descended class map is the actual source root times the child product. -/
theorem source_from_classes_weight {R : Type*} [CommSemiring R]
    (n : OtherColors d → ℕ) (q : ∀ k,SinkDegreeClass (n k) k.1)
    (x : R) (y : Fin 3 → R) :
    sourceClassWeight x y (sourceFromClasses n q)=x*∏ k,sinkClassWeight x y (q k) := by
  rw [sourceFromClasses,sourceFromObjects,canonical_source_weight]
  dsimp only [assembleSourceObjects]
  rw [source_assembly_weight]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  have h : sinkClassWeight x y (Quotient.mk'' (q k).out : SinkDegreeClass (n k) k.1)=
      sinkClassWeight x y (q k) := congrArg (sinkClassWeight x y) (Quotient.out_eq' (q k))
  exact h

end KroneckerSourceClassAssembly
end
