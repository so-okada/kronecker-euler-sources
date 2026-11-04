import KroneckerManuscriptFurtherDefinitions
import KroneckerExactSlotCounts
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace KroneckerManuscriptBranchCounting
open KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerLeafDeletedSourceBranch KroneckerOutgoingSinkBranches
open KroneckerSourceBranchDegrees KroneckerFiniteBranchClasses
attribute [local instance] Classical.propDecidable

/-- The PDF branch conditions on the tree before the parent vertex is adjoined. -/
def SourceBranchCondition {I J : Type} [Fintype J] (T : ColoredTable I J) (r : I) (d : Fin 3) : Prop :=
  (incidenceGraph (Incidence T)).IsTree ∧
  (∀ i, Fintype.card {j // Incidence T i j} = if i=r then 2 else 3) ∧
  (∀ j, T.code r j ≠ some d)
def SinkBranchCondition {I J : Type} [Fintype J] (T : ColoredTable I J) (r : J) (d : Fin 3) : Prop :=
  (incidenceGraph (Incidence T)).IsTree ∧
  (∀ i, Fintype.card {j // Incidence T i j} = 3) ∧
  (∀ i, T.code i r ≠ some d)

theorem full_colors_of_degree_three {I J : Type} [Fintype J]
    (T : ColoredTable I J) (i : I) (h : Fintype.card {j // Incidence T i j}=3) :
    ∀ e, ∃ j, T.code i j=some e := by
  have hb := (Fintype.bijective_iff_injective_and_card
    (fun j : {j // Incidence T i j} => (coloring T).color i j j.property)).mpr
    ⟨(coloring T).at_source i, by simpa using h⟩
  intro e
  obtain ⟨j,hj⟩ := hb.2 e
  exact ⟨j, (code_color T i j j.property).trans (congrArg some hj)⟩

theorem source_branch_iff {I J : Type} [Fintype J]
    (T : ColoredTable I J) (r : I) (d : Fin 3) :
    IsSourceBranch T r d ↔ SourceBranchCondition T r d := by
  constructor
  · intro h
    exact ⟨h.1,source_branch_degrees h,source_branch_parent_color_absent h⟩
  · rintro ⟨ht,hd,ha⟩
    refine ⟨ht,?_⟩
    intro i e
    by_cases hi : i=r
    · subst i
      let f : {j // Incidence T r j} → {e : Fin 3 // e≠d} :=
        fun j => ⟨(coloring T).color r j j.property,by
          intro h
          exact ha j ((code_color T r j j.property).trans (congrArg some h))⟩
      have hf : Function.Injective f := by
        intro j k h
        exact (coloring T).at_source r (congrArg Subtype.val h)
      have hb := (Fintype.bijective_iff_injective_and_card f).mpr
        ⟨hf,by simpa using hd r⟩
      constructor
      · rintro ⟨j,hj⟩
        exact Or.inr (fun he => ha j (he ▸ hj))
      · intro he
        have he' : e≠d := he.resolve_left (not_not_intro rfl)
        obtain ⟨j,hj⟩ := hb.2 ⟨e,he'⟩
        exact ⟨j,(code_color T r j j.property).trans (congrArg some (congrArg Subtype.val hj))⟩
    · exact ⟨fun _ => Or.inl hi,fun _ => full_colors_of_degree_three T i (by simpa [hi] using hd i) e⟩

theorem sink_branch_iff {I J : Type} [Fintype J]
    (T : ColoredTable I J) (r : J) (d : Fin 3) :
    IsSinkBranch T r d ↔ SinkBranchCondition T r d := by
  constructor
  · intro h
    exact ⟨h.1,KroneckerSinkBranchSizes.sink_branch_source_degrees h,h.2.2⟩
  · rintro ⟨ht,hd,ha⟩
    exact ⟨ht,fun i => full_colors_of_degree_three T i (hd i),ha⟩

/-- Rigidity applies to every finite properly colored bipartite incidence tree. -/
theorem colored_tree_rigidity {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : KroneckerProperColoredReflection.ProperColoring R)
    (ht : (incidenceGraph R).IsTree) (f : KroneckerColoredIncidenceIso.ColoredIso C C) : f=1 :=
  KroneckerUnrootedColoredRigidity.unrooted_rigidity C ht f

abbrev LeafPoly := MvPolynomial (Fin 3) ℚ
def T (d : Fin 3) : PowerSeries LeafPoly :=
  KroneckerActualBranchSeries.sourceSeries MvPolynomial.X d
def D (d : Fin 3) : PowerSeries LeafPoly :=
  KroneckerActualBranchSeries.sinkSeries MvPolynomial.X d
def U : PowerSeries LeafPoly := PowerSeries.mk (fun n =>
  KroneckerTreeLeafEnumerator.leafEnumerator (Fin n) (Fin (2*n+1)))
def leafDerivative (d : Fin 3) (F : PowerSeries LeafPoly) : PowerSeries LeafPoly :=
  PowerSeries.mk (fun n => MvPolynomial.pderiv d (PowerSeries.coeff n F))

theorem leaf_derivative (d : Fin 3) : leafDerivative d U = T d := by
  apply PowerSeries.ext
  intro n
  simpa [leafDerivative,U,T] using KroneckerActualLeafDerivative.actual_leaf_derivative n d

open KroneckerThreeColorBranchGrammar
theorem source_series_equation (d : Fin 3) :
    T d = PowerSeries.X * D (nextColor d) * D (lastColor d) :=
  actual_source_grammar MvPolynomial.X d
theorem sink_series_equation (d : Fin 3) :
    D d = PowerSeries.C (MvPolynomial.X d) + T (nextColor d) + T (lastColor d) +
      T (nextColor d)*T (lastColor d) := actual_sink_grammar MvPolynomial.X d

def P (j : ℕ) (d : Fin 3) : ℕ := Fintype.card
  (KroneckerReflectedSingleSlotCounts.SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d)
def Q (j : ℕ) (d e : Fin 3) : ℕ := Fintype.card
  (KroneckerReflectedPairSlotCounts.PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d e)
theorem single_slot_count (j : ℕ) (d : Fin 3) :
    (P j d : ℚ) = ((4*j+4).choose (j+1) : ℚ)/(3*j+4) :=
  KroneckerReflectedSingleSlotCounts.reflected_single_slot_closed_count j d
theorem same_slot_count (j : ℕ) (hj : 1≤j) (d : Fin 3) :
    Q j d d = 2*(4*j+2).choose (j-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  simpa [Q,Nat.add_mul,Nat.mul_add,Nat.add_assoc] using
    KroneckerReflectedPairSlotCounts.reflected_same_slot_count n d
theorem different_slot_ratio (j : ℕ) (hj : 1≤j) {d e : Fin 3} (hde : d≠e) :
    (Q j d e : ℚ) = ((2*j+3 : ℚ)/(2*j))*(Q j d d : ℚ) := by
  have h := KroneckerReflectedPairSlotCounts.reflected_slot_pair_ratio j hde
  change 2*j*Q j d e=(2*j+3)*Q j d d at h
  have hq : (2*j : ℚ)*(Q j d e : ℚ)=(2*j+3)*(Q j d d : ℚ) := by exact_mod_cast h
  have hjq : (j:ℚ)≠0 := by exact_mod_cast (by omega : j≠0)
  field_simp
  nlinarith [hq]
theorem different_slot_ge_same (j : ℕ) {d e : Fin 3} (hde : d≠e) : Q j d d ≤ Q j d e :=
  KroneckerReflectedPairSlotCounts.reflected_slot_pair_comparison j hde
end KroneckerManuscriptBranchCounting


namespace KroneckerManuscriptQuiverDefinitions
/-- The fixed-tree branch set in Definition `def:colored-branches`.
The bipartition is explicit; the manuscript assumes B is a finite tree. -/
def Branch (B : Graph) (b : B.Bipartition) (d : Fin 3) :=
  {p : (B.Edge → Fin 3) × B.Vert //
    (∀ v e f, v ∈ B.boundary e → v ∈ B.boundary f → p.1 e = p.1 f → e = f) ∧
    (∀ e, p.2 ∈ B.boundary e → p.1 e ≠ d) ∧
    (∀ v ∈ b.sources, B.degree v = if v = p.2 then 2 else 3)}

/-- The named arrow coloring pulled back along a covering. -/
def Quiver.CovCol {Q T : Quiver} (p : Q.Covering T) (c : T.Arrow → Fin 3) :
    Q.Arrow → Fin 3 := fun a => c (p.edge a)

@[simp] theorem Quiver.covCol_apply {Q T : Quiver} (p : Q.Covering T)
    (c : T.Arrow → Fin 3) (a : Q.Arrow) : Quiver.CovCol p c a = c (p.edge a) := rfl

namespace LabeledChain
/-- The manuscript uses c=n+1. Existing Ch is retained for source compatibility. -/
abbrev LSTrivCh (n : ℕ) : Graph := Ch n
end LabeledChain
end KroneckerManuscriptQuiverDefinitions

set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.Branch
set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.Quiver.CovCol
set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.Quiver.covCol_apply
set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.LabeledChain.LSTrivCh
set_option pp.fullNames true in
#print axioms KroneckerFiniteBranchObjects.source_object_dimensions
set_option pp.fullNames true in
#print axioms KroneckerFiniteBranchObjects.sink_object_dimensions
set_option pp.fullNames true in
#print axioms KroneckerFiniteBranchClasses.source_degree_zero
