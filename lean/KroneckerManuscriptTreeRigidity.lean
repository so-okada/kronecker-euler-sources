import KroneckerUnrootedColoredRigidity
noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
namespace KroneckerManuscriptTreeRigidity
structure ProperColoring {K I J : Type} (R : I → J → Prop) where
  color : ∀ i j, R i j → K
  at_source : ∀ i, Function.Injective (fun j : {j // R i j} => color i j j.property)
  at_sink : ∀ j, Function.Injective (fun i : {i // R i j} => color i j i.property)
end KroneckerManuscriptTreeRigidity

namespace KroneckerManuscriptTreeRigidity
variable {K : Type}
open KroneckerManuscriptTreeRigidity KroneckerBipartiteIncidence
attribute [local instance] Classical.propDecidable

structure ColoredIso {I J I' J' : Type} {R : I → J → Prop} {R' : I' → J' → Prop}
    (C : ProperColoring (K:=K) R) (C' : ProperColoring (K:=K) R') where
  source : I ≃ I'
  sink : J ≃ J'
  incidence : ∀ i j,R' (source i) (sink j) ↔ R i j
  color : ∀ i j (h : R i j),C'.color (source i) (sink j) ((incidence i j).mpr h)=C.color i j h

namespace ColoredIso
variable {I J I' J' I'' J'' : Type} {R : I → J → Prop} {R' : I' → J' → Prop}
  {R'' : I'' → J'' → Prop} {C : ProperColoring (K:=K) R} {C' : ProperColoring (K:=K) R'}
  {C'' : ProperColoring (K:=K) R''}

def symm (e : ColoredIso C C') : ColoredIso C' C where
  source := e.source.symm
  sink := e.sink.symm
  incidence := by intro i j; simpa using (e.incidence (e.source.symm i) (e.sink.symm j)).symm
  color := by intro i j h; simpa using (e.color (e.source.symm i) (e.sink.symm j) _).symm

def trans (e : ColoredIso C C') (f : ColoredIso C' C'') : ColoredIso C C'' where
  source := e.source.trans f.source
  sink := e.sink.trans f.sink
  incidence := by intro i j; exact (f.incidence _ _).trans (e.incidence i j)
  color := by intro i j h; exact (f.color _ _ _).trans (e.color i j h)

def sourceNeighbors (e : ColoredIso C C') (i : I) : {j // R i j} ≃ {j // R' (e.source i) j} where
  toFun j := ⟨e.sink j,(e.incidence i j).mpr j.2⟩
  invFun j := ⟨e.sink.symm j,(e.incidence i (e.sink.symm j)).mp (by simpa using j.2)⟩
  left_inv := by intro j; apply Subtype.ext; exact e.sink.symm_apply_apply j
  right_inv := by intro j; apply Subtype.ext; exact e.sink.apply_symm_apply j

def sinkNeighbors (e : ColoredIso C C') (j : J) : {i // R i j} ≃ {i // R' i (e.sink j)} where
  toFun i := ⟨e.source i,(e.incidence i j).mpr i.2⟩
  invFun i := ⟨e.source.symm i,(e.incidence (e.source.symm i) j).mp (by simpa using i.2)⟩
  left_inv := by intro i; apply Subtype.ext; exact e.source.symm_apply_apply i
  right_inv := by intro i; apply Subtype.ext; exact e.source.apply_symm_apply i

theorem source_degree [Fintype J] [Fintype J'] (e : ColoredIso C C') (i : I) :
    Fintype.card {j // R' (e.source i) j}=Fintype.card {j // R i j} :=
  (Fintype.card_congr (e.sourceNeighbors i)).symm

theorem sink_degree [Fintype I] [Fintype I'] (e : ColoredIso C C') (j : J) :
    Fintype.card {i // R' i (e.sink j)}=Fintype.card {i // R i j} :=
  (Fintype.card_congr (e.sinkNeighbors j)).symm

def graphIso (e : ColoredIso C C') : incidenceGraph R ≃g incidenceGraph R' where
  toEquiv := Equiv.sumCongr e.source e.sink
  map_rel_iff' := by
    intro u v
    cases u <;> cases v <;> simp only [Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr]
    · rfl
    · exact e.incidence _ _
    · exact e.incidence _ _
    · rfl

end ColoredIso
end KroneckerManuscriptTreeRigidity

namespace KroneckerManuscriptTreeRigidity.RootRigidity
variable {K : Type}
open SimpleGraph KroneckerManuscriptTreeRigidity KroneckerManuscriptTreeRigidity
open KroneckerBipartiteIncidence

variable {I J : Type} {R : I → J → Prop} {C : ProperColoring (K:=K) R}

theorem source_fix_propagates (e : ColoredIso C C) {i : I} {j : J}
    (hi : e.source i=i) (h : R i j) : e.sink j=j := by
  have hr : R i (e.sink j) := by simpa only [hi] using (e.incidence i j).mpr h
  have hc : C.color i (e.sink j) hr=C.color i j h := by simpa only [hi] using e.color i j h
  exact congrArg Subtype.val (C.at_source i (a₁:=⟨e.sink j,hr⟩) (a₂:=⟨j,h⟩) hc)

theorem sink_fix_propagates (e : ColoredIso C C) {i : I} {j : J}
    (hj : e.sink j=j) (h : R i j) : e.source i=i := by
  have hr : R (e.source i) j := by simpa only [hj] using (e.incidence i j).mpr h
  have hc : C.color (e.source i) j hr=C.color i j h := by simpa only [hj] using e.color i j h
  exact congrArg Subtype.val (C.at_sink j (a₁:=⟨e.source i,hr⟩) (a₂:=⟨i,h⟩) hc)

theorem fixed_adjacent (e : ColoredIso C C) {u v : I ⊕ J}
    (hu : e.graphIso u=u) (h : (incidenceGraph R).Adj u v) : e.graphIso v=v := by
  cases u with
  | inl i => cases v with
    | inl k => exact False.elim h
    | inr j =>
      have hi : e.source i=i := Sum.inl.inj hu
      exact congrArg Sum.inr (source_fix_propagates e hi h)
  | inr j => cases v with
    | inr k => exact False.elim h
    | inl i =>
      have hj : e.sink j=j := Sum.inr.inj hu
      exact congrArg Sum.inl (sink_fix_propagates e hj h)

theorem fixed_along_walk (e : ColoredIso C C) {u v : I ⊕ J} (p : (incidenceGraph R).Walk u v) :
    e.graphIso u=u → e.graphIso v=v := by
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hu => ih (fixed_adjacent e hu h)

/-- A color- and bipartition-preserving automorphism fixing one vertex is
identity on a connected support. Finiteness and acyclicity are not needed. -/
theorem connected_root_rigidity (hR : (incidenceGraph R).Connected)
    (e : ColoredIso C C) (u : I ⊕ J) (hu : e.graphIso u=u) :
    (∀ i,e.source i=i) ∧ (∀ j,e.sink j=j) := by
  have hv : ∀ v,e.graphIso v=v := by
    intro v
    obtain ⟨p⟩ := hR.preconnected u v
    exact fixed_along_walk e p hu
  exact ⟨fun i => Sum.inl.inj (hv (.inl i)),fun j => Sum.inr.inj (hv (.inr j))⟩

end KroneckerManuscriptTreeRigidity.RootRigidity

namespace KroneckerManuscriptTreeRigidity.AutomorphismGroup
variable {K : Type}
open KroneckerManuscriptTreeRigidity KroneckerManuscriptTreeRigidity

variable {I J I' J' : Type} {R : I → J → Prop} {R' : I' → J' → Prop}
  {C : ProperColoring (K:=K) R} {C' : ProperColoring (K:=K) R'}

theorem iso_ext {e f : ColoredIso C C'} (hs : e.source=f.source) (ht : e.sink=f.sink) : e=f := by
  cases e; cases f; cases hs; cases ht; rfl

def identity (C : ProperColoring (K:=K) R) : ColoredIso C C where
  source := Equiv.refl I
  sink := Equiv.refl J
  incidence := by intro i j; rfl
  color := by intro i j h; rfl

/-- Multiplication is composition in the permutation-group convention. -/
instance automorphismGroup (C : ProperColoring (K:=K) R) : Group (ColoredIso C C) where
  one := identity C
  mul e f := f.trans e
  inv := ColoredIso.symm
  mul_assoc e f g := by apply iso_ext <;> rfl
  one_mul e := by apply iso_ext <;> rfl
  mul_one e := by apply iso_ext <;> rfl
  inv_mul_cancel e := by
    apply iso_ext <;> apply Equiv.ext <;> intro x <;>
      exact Equiv.symm_apply_apply _ x

theorem automorphism_pair_injective :
    Function.Injective (fun e : ColoredIso C C => (e.source,e.sink)) := by
  intro e f h
  exact iso_ext (congrArg Prod.fst h) (congrArg Prod.snd h)

noncomputable instance automorphismFintype [Fintype I] [Fintype J] : Fintype (ColoredIso C C) := by
  classical
  exact Fintype.ofInjective _ automorphism_pair_injective

theorem automorphism_eq_one_iff (e : ColoredIso C C) :
    e=1 ↔ (∀ i,e.source i=i) ∧ (∀ j,e.sink j=j) := by
  constructor
  · rintro rfl; exact ⟨fun _ => rfl,fun _ => rfl⟩
  · rintro ⟨hs,ht⟩
    exact iso_ext (Equiv.ext hs) (Equiv.ext ht)

end KroneckerManuscriptTreeRigidity.AutomorphismGroup

namespace KroneckerManuscriptTreeRigidity.FreeActions
variable {K : Type}
open KroneckerManuscriptTreeRigidity KroneckerManuscriptTreeRigidity
open KroneckerManuscriptTreeRigidity.AutomorphismGroup KroneckerManuscriptTreeRigidity.RootRigidity KroneckerBipartiteIncidence

variable {I J : Type} {R : I → J → Prop} (C : ProperColoring (K:=K) R)

def sourceAction : MulAction (ColoredIso C C) I where
  smul e i := e.source i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def sinkAction : MulAction (ColoredIso C C) J where
  smul e j := e.sink j
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def edgeAction : MulAction (ColoredIso C C) {p : I × J // R p.1 p.2} where
  smul e p := ⟨(e.source p.1.1,e.sink p.1.2),(e.incidence _ _).mpr p.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem source_action_free (hR : (incidenceGraph R).Connected) (e : ColoredIso C C)
    (i : I) (h : e.source i=i) : e=1 :=
  (automorphism_eq_one_iff e).mpr (connected_root_rigidity hR e (.inl i) (congrArg Sum.inl h))

theorem sink_action_free (hR : (incidenceGraph R).Connected) (e : ColoredIso C C)
    (j : J) (h : e.sink j=j) : e=1 :=
  (automorphism_eq_one_iff e).mpr (connected_root_rigidity hR e (.inr j) (congrArg Sum.inr h))

theorem edge_action_free (hR : (incidenceGraph R).Connected) (e : ColoredIso C C)
    (p : {p : I × J // R p.1 p.2})
    (h : (edgeAction C).smul e p=p) : e=1 := by
  apply source_action_free C hR e p.1.1
  exact congrArg (fun q => q.1.1) h

end KroneckerManuscriptTreeRigidity.FreeActions

namespace KroneckerManuscriptTreeRigidity.Divisibility
variable {K : Type}

/-- A free action partitions a finite set into copies of the actual group. -/
theorem free_action_card_dvd {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X] (hfree : ∀ g : G,∀ x : X,g • x=x → g=1) :
    Fintype.card G ∣ Fintype.card X := by
  classical
  have hs : ∀ x : X,MulAction.stabilizer G x=⊥ := by
    intro x
    apply le_antisymm _ bot_le
    intro g hg
    exact (Subgroup.mem_bot).mpr (hfree g x hg)
  have hc := Fintype.card_congr (MulAction.selfEquivOrbitsQuotientProd hs)
  rw [Fintype.card_prod] at hc
  exact ⟨Fintype.card (Quotient (MulAction.orbitRel G X)),by simpa [mul_comm] using hc⟩

open KroneckerManuscriptTreeRigidity KroneckerManuscriptTreeRigidity KroneckerBipartiteIncidence
open KroneckerManuscriptTreeRigidity.FreeActions KroneckerManuscriptTreeRigidity.AutomorphismGroup
attribute [local instance] Classical.propDecidable

theorem automorphism_card_divisibility {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring (K:=K) R) (hR : (incidenceGraph R).Connected) :
    Fintype.card (ColoredIso C C) ∣ Fintype.card I ∧
    Fintype.card (ColoredIso C C) ∣ Fintype.card J ∧
    Fintype.card (ColoredIso C C) ∣ Fintype.card {p : I × J // R p.1 p.2} := by
  refine ⟨?_,?_,?_⟩
  · let := sourceAction C
    exact free_action_card_dvd (source_action_free C hR)
  · let := sinkAction C
    exact free_action_card_dvd (sink_action_free C hR)
  · let := edgeAction C
    exact free_action_card_dvd (edge_action_free C hR)

end KroneckerManuscriptTreeRigidity.Divisibility

namespace KroneckerManuscriptTreeRigidity.Unrooted
variable {K : Type}
open KroneckerManuscriptTreeRigidity KroneckerManuscriptTreeRigidity KroneckerBipartiteIncidence
open KroneckerManuscriptTreeRigidity.AutomorphismGroup KroneckerManuscriptTreeRigidity.Divisibility SimpleGraph
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem tree_incidence_card {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hT : (incidenceGraph R).IsTree) :
    Fintype.card {p : I × J // R p.1 p.2}+1=Fintype.card I+Fintype.card J := by
  classical
  have hs := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype R)
  rw [Fintype.card_sigma] at hs
  have he := hT.card_edgeFinset
  have hd := (incidenceGraph R).sum_degrees_eq_twice_card_edges
  rw [incidence_degree_sum] at hd
  rw [Fintype.card_sum] at he
  omega

/-- The order of a free automorphism group divides both vertices and edges;
the Euler characteristic of a finite tree forces that order to be one. -/
theorem tree_automorphism_card {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring (K:=K) R) (hT : (incidenceGraph R).IsTree) :
    Fintype.card (ColoredIso C C)=1 := by
  obtain ⟨hi,hj,he⟩ := automorphism_card_divisibility C hT.connected
  have hv := dvd_add hi hj
  rw [←tree_incidence_card R hT] at hv
  apply Nat.eq_one_of_dvd_one
  simpa using Nat.dvd_sub hv he

theorem unrooted_rigidity {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring (K:=K) R) (hT : (incidenceGraph R).IsTree)
    (e : ColoredIso C C) : e=1 := by
  haveI : Subsingleton (ColoredIso C C) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (tree_automorphism_card C hT))
  exact Subsingleton.elim _ _

theorem tree_iso_unique {I J I' J' : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} {R' : I' → J' → Prop}
    {C : ProperColoring (K:=K) R} {C' : ProperColoring (K:=K) R'}
    (hT : (incidenceGraph R).IsTree) (e f : ColoredIso C C') : e=f := by
  have h := unrooted_rigidity C hT (e.trans f.symm)
  apply iso_ext <;> apply Equiv.ext <;> intro x
  · have hx := congrArg (fun g : ColoredIso C C => g.source x) h
    change f.source.symm (e.source x) = x at hx
    exact f.source.symm.injective (hx.trans (f.source.symm_apply_apply x).symm)
  · have hx := congrArg (fun g : ColoredIso C C => g.sink x) h
    change f.sink.symm (e.sink x) = x at hx
    exact f.sink.symm.injective (hx.trans (f.sink.symm_apply_apply x).symm)

end KroneckerManuscriptTreeRigidity.Unrooted
