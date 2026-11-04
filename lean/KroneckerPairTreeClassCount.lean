import KroneckerTablePairMarks
import KroneckerMarkedClassIsomorphisms

set_option autoImplicit false
namespace KroneckerPairTreeClassCount
open KroneckerFiniteColoredTables KroneckerTableLeafMarks KroneckerTablePairMarks
open KroneckerSaturatedTableAction KroneckerLabelledTreeClassCount KroneckerTableRelabeling
open KroneckerFreeQuotientFibers
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable (I J : Type) [Fintype I] [Fintype J] (d e : Fin 3)

abbrev PairTable := {p : SaturatedTable I J × (J × J) // PairMark p.1.1 d e p.2}

variable {I J d e}

noncomputable def relabelPair (p : Equiv.Perm I × Equiv.Perm J) (M : PairTable I J d e) :
    PairTable I J d e := ⟨(p • M.1.1,(p.2 M.1.2.1,p.2 M.1.2.2)),
      (pair_mark_transport (relabelIso p M.1.1.1) d e M.1.2).mpr M.2⟩

noncomputable instance pairRelabelAction : MulAction (Equiv.Perm I × Equiv.Perm J) (PairTable I J d e) where
  smul := relabelPair
  one_smul M := by apply Subtype.ext; apply Prod.ext; exact one_smul _ _; rfl
  mul_smul p q M := by apply Subtype.ext; apply Prod.ext; exact mul_smul p q M.1.1; rfl

def forgetPair (M : PairTable I J d e) : SaturatedTable I J := M.1.1

theorem forget_pair_equivariant (p : Equiv.Perm I × Equiv.Perm J) (M : PairTable I J d e) :
    forgetPair (p • M)=p • forgetPair M := rfl

def pairFiberEquiv (T : SaturatedTable I J) :
    {M : PairTable I J d e // forgetPair M=T} ≃ {p // PairMark T.1 d e p} where
  toFun M := ⟨M.1.1.2,by
    have h := M.1.2
    change PairMark (forgetPair M.1).1 d e M.1.1.2 at h
    rwa [M.2] at h⟩
  invFun p := ⟨⟨(T,p.1),p.2⟩,rfl⟩
  left_inv M := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext M.2.symm rfl
  right_inv p := rfl

abbrev PairClass (I J : Type) [Fintype I] [Fintype J] (d e : Fin 3) :=
  Quotient (MulAction.orbitRel (Equiv.Perm I × Equiv.Perm J) (PairTable I J d e))

noncomputable def forgetOnClasses : PairClass I J d e → TreeClass I J :=
  quotientMap forgetPair forget_pair_equivariant

noncomputable def pairClassFiberEquiv (T : SaturatedTable I J) :
    {p // PairMark T.1 d e p} ≃ {q : PairClass I J d e // forgetOnClasses q=Quotient.mk'' T} :=
  (pairFiberEquiv T).symm.trans
    (quotientFiberEquiv forgetPair forget_pair_equivariant saturated_relabel_free T)

theorem pair_classes_sum : Fintype.card (PairClass I J d e)=
    ∑ q : TreeClass I J,Fintype.card {p // PairMark q.out.1 d e p} := by
  rw [←Fintype.card_congr (Equiv.sigmaFiberEquiv (forgetOnClasses (I:=I) (J:=J) (d:=d) (e:=e))),
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro q _
  have h := (Fintype.card_congr (pairClassFiberEquiv (d:=d) (e:=e) q.out)).symm
  simpa only [Quotient.out_eq'] using h

/-- Same-color ordered marks contribute the falling factorial N(N-1),
with no diagonal and no quotient by reversal. -/
theorem equal_color_class_count : Fintype.card (PairClass I J d d)=
    ∑ q : TreeClass I J,Fintype.card {j // LeafMark q.out.1 d j}*
      (Fintype.card {j // LeafMark q.out.1 d j}-1) := by
  rw [pair_classes_sum]
  exact Finset.sum_congr rfl (fun q _ => equal_color_pair_count q.out.1 d)

theorem distinct_color_class_count (hde : d≠e) : Fintype.card (PairClass I J d e)=
    ∑ q : TreeClass I J,Fintype.card {j // LeafMark q.out.1 d j}*
      Fintype.card {j // LeafMark q.out.1 e j} := by
  rw [pair_classes_sum]
  exact Finset.sum_congr rfl (fun q _ => distinct_color_pair_count q.out.1 hde)

end KroneckerPairTreeClassCount
