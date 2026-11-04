import KroneckerRetainedSubrepresentations
import KroneckerProperColoredReflection

/- Original module: KroneckerLeafPruningRetraction -/
section
set_option autoImplicit false
namespace KroneckerLeafPruningRetraction
open SimpleGraph KroneckerBipartiteIncidence KroneckerRetainedReflectionKernels
attribute [local instance] Classical.propDecidable

def retainedIncidence {I J : Type*} [Fintype I] (R : I → J → Prop) : Retained R → I → Prop :=
  fun j i => R i j.1

def includeVertex {I J : Type*} [Fintype I] (R : I → J → Prop) : (Retained R ⊕ I) → I ⊕ J
  | .inl j => .inr j.1
  | .inr i => .inl i

theorem include_vertex_injective {I J : Type*} [Fintype I] (R : I → J → Prop) :
    Function.Injective (includeVertex R) := by
  intro a b h
  cases a <;> cases b <;> simp_all [includeVertex,Subtype.ext_iff]

def inclusionHom {I J : Type*} [Fintype I] (R : I → J → Prop) :
    incidenceGraph (retainedIncidence R) →g incidenceGraph R where
  toFun := includeVertex R
  map_rel' := by
    intro a b h
    cases a <;> cases b <;> exact h

noncomputable def pruneVertex {I J : Type*} [Fintype I] (R : I → J → Prop)
    (hpos : ∀ j,∃ i,R i j) : (I ⊕ J) → Retained R ⊕ I
  | .inl i => .inr i
  | .inr j => if h : 2≤Fintype.card {i // R i j} then .inl ⟨j,h⟩
      else .inr (Classical.choose (hpos j))

theorem prune_inclusion {I J : Type*} [Fintype I] (R : I → J → Prop)
    (hpos : ∀ j,∃ i,R i j) (v : Retained R ⊕ I) :
    pruneVertex R hpos (includeVertex R v)=v := by
  cases v with
  | inl j => simp [includeVertex,pruneVertex,j.2]
  | inr i => rfl

theorem prune_leaf_neighbor {I J : Type*} [Fintype I] (R : I → J → Prop)
    (hpos : ∀ j,∃ i,R i j) {i : I} {j : J}
    (hj : ¬2≤Fintype.card {i // R i j}) (hij : R i j) :
    pruneVertex R hpos (.inr j)=.inr i := by
  haveI : Subsingleton {i // R i j} :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have he : Classical.choose (hpos j)=i := congrArg Subtype.val (Subsingleton.elim
    (⟨Classical.choose (hpos j),Classical.choose_spec (hpos j)⟩ : {i // R i j}) ⟨i,hij⟩)
  simp [pruneVertex,hj,he]

theorem prune_incidence_reachable {I J : Type*} [Fintype I] (R : I → J → Prop)
    (hpos : ∀ j,∃ i,R i j) {i : I} {j : J} (hij : R i j) :
    (incidenceGraph (retainedIncidence R)).Reachable
      (pruneVertex R hpos (.inl i)) (pruneVertex R hpos (.inr j)) := by
  by_cases hj : 2≤Fintype.card {i // R i j}
  · have h : (incidenceGraph (retainedIncidence R)).Adj (.inr i) (.inl ⟨j,hj⟩) := hij
    simpa [pruneVertex,hj] using h.reachable
  · rw [prune_leaf_neighbor R hpos hj hij]
    exact Reachable.refl _

theorem prune_adjacency_reachable {I J : Type*} [Fintype I] (R : I → J → Prop)
    (hpos : ∀ j,∃ i,R i j) {u v : I ⊕ J} (h : (incidenceGraph R).Adj u v) :
    (incidenceGraph (retainedIncidence R)).Reachable (pruneVertex R hpos u) (pruneVertex R hpos v) := by
  cases u with
  | inl i => cases v with
    | inl k => exact False.elim h
    | inr j => exact prune_incidence_reachable R hpos h
  | inr j => cases v with
    | inr k => exact False.elim h
    | inl i => exact (prune_incidence_reachable R hpos h).symm

theorem prune_walk_reachable {I J : Type*} [Fintype I] (R : I → J → Prop)
    (hpos : ∀ j,∃ i,R i j) {u v : I ⊕ J} (p : (incidenceGraph R).Walk u v) :
    (incidenceGraph (retainedIncidence R)).Reachable (pruneVertex R hpos u) (pruneVertex R hpos v) := by
  induction p with
  | nil => exact Reachable.refl _
  | cons h p ih => exact (prune_adjacency_reachable R hpos h).trans ih

end KroneckerLeafPruningRetraction
end

/- Original module: KroneckerRetainedSupportTree -/
section
set_option autoImplicit false
namespace KroneckerRetainedSupportTree
open SimpleGraph KroneckerBipartiteIncidence KroneckerRetainedReflectionKernels
open KroneckerLeafPruningRetraction KroneckerSaturatedTreeDimensions
attribute [local instance] Classical.propDecidable

theorem retained_support_connected {I J : Type*} [Fintype I] [Nonempty I]
    (R : I → J → Prop) (hpos : ∀ j,∃ i,R i j) (hc : (incidenceGraph R).Connected) :
    (incidenceGraph (retainedIncidence R)).Connected := by
  refine { preconnected := ?_, nonempty := ⟨.inr (Classical.arbitrary I)⟩ }
  intro u v
  obtain ⟨p⟩ := hc (includeVertex R u) (includeVertex R v)
  simpa only [prune_inclusion] using prune_walk_reachable R hpos p

theorem retained_support_acyclic {I J : Type*} [Fintype I]
    (R : I → J → Prop) (ha : (incidenceGraph R).IsAcyclic) :
    (incidenceGraph (retainedIncidence R)).IsAcyclic :=
  ha.comap (inclusionHom R) (include_vertex_injective R)

/-- Omitting the old leaves really leaves a connected acyclic reflected support. -/
theorem retained_support_tree {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (R : I → J → Prop) (hT : (incidenceGraph R).IsTree) :
    (incidenceGraph (retainedIncidence R)).IsTree := by
  have hpos : ∀ j,∃ i,R i j := by
    intro j
    have hn := Fintype.card_pos_iff.mp (saturated_sink_degree_positive R hT j)
    obtain ⟨i,hi⟩ := hn
    exact ⟨i,hi⟩
  exact ⟨retained_support_connected R hpos hT.connected,retained_support_acyclic R hT.isAcyclic⟩

end KroneckerRetainedSupportTree
end

/- Original module: KroneckerRetainedBlockSupport -/
section
set_option autoImplicit false
namespace KroneckerRetainedBlockSupport
open SimpleGraph Module KroneckerLinearCoverBlocks KroneckerReflectionKernel
open KroneckerRetainedReflectionKernels KroneckerLeafPruningRetraction
open KroneckerRetainedSupportTree KroneckerProperColoredReflection KroneckerBipartiteIncidence
attribute [local instance] Classical.propDecidable

def linearSupport (B : LinearCoverBlock) : B.Source → B.Sink → Prop := fun s t => B.arrow s t≠0
def supportGraph (B : LinearCoverBlock) := incidenceGraph (linearSupport B)

theorem retained_projection_surjective {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) (j : Retained R) (i : I) (h : R i j.1) :
    Function.Surjective ((retainedBlock R).arrow j i) := by
  haveI : Nontrivial {k // R k j.1} := Fintype.one_lt_card_iff_nontrivial.mp j.2
  obtain ⟨k,hk⟩ := exists_ne (⟨i,h⟩ : {k // R k j.1})
  simpa [retainedBlock,h] using reflection_projection_surjective ⟨i,h⟩ k (Ne.symm hk)

/-- The retained incidence graph is exactly the nonzero-arrow support. -/
theorem retained_support_iff {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) (j : Retained R) (i : I) :
    linearSupport (retainedBlock R) j i ↔ R i j.1 := by
  constructor
  · intro hs
    by_contra h
    exact hs (by simp [retainedBlock,h])
  · intro h hz
    obtain ⟨x,hx⟩ := retained_projection_surjective R j i h 1
    rw [hz] at hx
    norm_num at hx

theorem retained_support_graph {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) : supportGraph (retainedBlock R)=incidenceGraph (retainedIncidence R) := by
  unfold supportGraph
  congr 1
  funext j i
  exact propext (retained_support_iff R j i)

noncomputable def retainedColoring {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) : ProperColoring (linearSupport (retainedBlock R)) where
  color := fun j i h => C.color i j.1 ((retained_support_iff R j i).mp h)
  at_source := by
    intro j i k h
    have he := C.at_sink j.1 (a₁:=⟨i.1,(retained_support_iff R j i.1).mp i.2⟩)
      (a₂:=⟨k.1,(retained_support_iff R j k.1).mp k.2⟩) h
    exact Subtype.ext (congrArg (fun x : {i // R i j.1} => x.1) he)
  at_sink := by
    intro i j k h
    have he := C.at_source i (a₁:=⟨j.1.1,(retained_support_iff R j.1 i).mp j.2⟩)
      (a₂:=⟨k.1.1,(retained_support_iff R k.1 i).mp k.2⟩) h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : {j // R i j} => x.1) he))

theorem retained_nonzero_support_tree {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (R : I → J → Prop) (hT : (incidenceGraph R).IsTree) :
    (supportGraph (retainedBlock R)).IsTree := by
  rw [retained_support_graph]
  exact retained_support_tree R hT

theorem retained_source_degree {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) (j : Retained R) :
    (supportGraph (retainedBlock R)).degree (.inl j)=Fintype.card {i // R i j.1} := by
  rw [retained_support_graph,KroneckerBipartiteIncidence.left_degree]
  rfl

theorem retained_dimension_degree_pairs {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (j : Retained R) :
    (finrank ℂ ((retainedBlock R).Space j)=1 ∧
      (supportGraph (retainedBlock R)).degree (.inl j)=2) ∨
    (finrank ℂ ((retainedBlock R).Space j)=2 ∧
      (supportGraph (retainedBlock R)).degree (.inl j)=3) := by
  rw [retained_source_degree]
  exact colored_reflection_dimensions C j.1 ((retained_iff_kernel_positive R j.1).mp j.2)

end KroneckerRetainedBlockSupport
end
