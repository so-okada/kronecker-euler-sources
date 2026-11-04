import KroneckerManuscriptFurtherDefinitions
import Mathlib.CategoryTheory.Equivalence
noncomputable section
open Classical CategoryTheory
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions.Representation

structure Supported {Q : Quiver} (U : Set Q.Vert) where
  rep : Representation Q
  outside_zero : ∀ v, v ∉ U → Subsingleton (rep.Space v)

instance supportedCategory {Q : Quiver} (U : Set Q.Vert) : Category (Supported U) where
  Hom R S := Hom R.rep S.rep
  id R := Hom.id R.rep
  comp f g := g.comp f
  id_comp f := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; rfl
  comp_id f := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; rfl
  assoc f g h := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; rfl

def restriction {Q : Quiver} (U : Set Q.Vert) : Supported U ⥤ Representation (Q.fullSubquiver U) where
  obj R := Res U R.rep
  map f := ResHom U f
  map_id R := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; rfl
  map_comp f g := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; rfl
def extension {Q : Quiver} (U : Set Q.Vert) : Representation (Q.fullSubquiver U) ⥤ Supported U where
  obj R := ⟨ExtZero U R, extZero_off_support U R⟩
  map f := ExtZeroHom U f
  map_id R := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; funext h; rfl
  map_comp f g := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; funext h; rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def supportedUnit {Q : Quiver} (U : Set Q.Vert) (R : Supported U) :
    Hom R.rep (ExtZero U (Res U R.rep)) where
  vertexMap v :=
    { toFun := fun x _ => x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  commutes a := by
    apply LinearMap.ext
    intro x
    change (fun _ => R.rep.arrow a x) = (ExtZero U (Res U R.rep)).arrow a (fun _ => x)
    funext ht
    by_cases hs : Q.source a ∈ U
    · simp [ExtZero,Res,hs]; rfl
    · haveI := R.outside_zero (Q.source a) hs
      have hx : x=0 := Subsingleton.elim _ _
      simp [ExtZero,Res,hs,hx]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def supportedUnitInv {Q : Quiver} (U : Set Q.Vert) (R : Supported U) :
    Hom (ExtZero U (Res U R.rep)) R.rep where
  vertexMap v := if hv : v ∈ U then
    { toFun := fun x => x ⟨hv⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl } else 0
  commutes a := by
    apply LinearMap.ext
    intro x
    by_cases ht : Q.target a ∈ U
    · by_cases hs : Q.source a ∈ U
      · simp [ExtZero,Res,hs,ht,arrowOverHom,spaceCast,Quiver.Hom.id]; rfl
      · simp [ExtZero,Res,hs,ht,arrowOverHom,spaceCast,Quiver.Hom.id]
    · haveI := R.outside_zero (Q.target a) ht
      exact @Subsingleton.elim (R.rep.Space (Q.target a)) (R.outside_zero (Q.target a) ht) _ _

def supportedUnitIso {Q : Quiver} (U : Set Q.Vert) (R : Supported U) :
    R ≅ (restriction U ⋙ extension U).obj R where
  hom := supportedUnit U R
  inv := supportedUnitInv U R
  hom_inv_id := by
    apply HomOver.ext
    intro v
    apply LinearMap.ext
    intro x
    change (supportedUnitInv U R).vertexMap v ((supportedUnit U R).vertexMap v x) = x
    by_cases hv : v ∈ U
    · simp [supportedUnit,supportedUnitInv,hv]; rfl
    · haveI := R.outside_zero v hv
      exact @Subsingleton.elim (R.rep.Space v) (R.outside_zero v hv) _ _
  inv_hom_id := by
    apply HomOver.ext
    intro v
    apply LinearMap.ext
    intro x
    change (supportedUnit U R).vertexMap v ((supportedUnitInv U R).vertexMap v x) = x
    funext h
    have hv : v ∈ U := h.down
    simp [supportedUnit,supportedUnitInv,hv]; rfl

def restrictedCounit {Q : Quiver} (U : Set Q.Vert) (R : Representation (Q.fullSubquiver U)) :
    Hom (Res U (ExtZero U R)) R where
  vertexMap v := (extZeroAt U R v).toLinearMap
  commutes a := by
    apply LinearMap.ext
    intro x
    change (ExtZero U R).arrow a.val x ⟨a.property.2⟩ = R.arrow a (x ⟨a.property.1⟩)
    simp [ExtZero,a.property.1]; rfl
def restrictedCounitInv {Q : Quiver} (U : Set Q.Vert) (R : Representation (Q.fullSubquiver U)) :
    Hom R (Res U (ExtZero U R)) where
  vertexMap v := (extZeroAt U R v).symm.toLinearMap
  commutes a := by
    apply LinearMap.ext
    intro x
    funext h
    change R.arrow a x = (ExtZero U R).arrow a.val (fun _ => x) h
    simp [ExtZero,a.property.1]; rfl
def restrictedCounitIso {Q : Quiver} (U : Set Q.Vert) (R : Representation (Q.fullSubquiver U)) :
    (extension U ⋙ restriction U).obj R ≅ R where
  hom := restrictedCounit U R
  inv := restrictedCounitInv U R
  hom_inv_id := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; funext h; rfl
  inv_hom_id := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; rfl

def supportEquivalence {Q : Quiver} (U : Set Q.Vert) : Supported U ≌ Representation (Q.fullSubquiver U) where
  functor := restriction U
  inverse := extension U
  unitIso := NatIso.ofComponents (supportedUnitIso U) (by intro R S f; apply HomOver.ext; intro v; apply LinearMap.ext; intro x; funext h; rfl)
  counitIso := NatIso.ofComponents (restrictedCounitIso U) (by intro R S f; apply HomOver.ext; intro v; apply LinearMap.ext; intro x; rfl)
  functor_unitIso_comp R := by apply HomOver.ext; intro v; apply LinearMap.ext; intro x; rfl

theorem supported_iff_repSupp_subset {Q : Quiver} (U : Set Q.Vert) (R : Representation Q) :
    (∀ v, v ∉ U → Subsingleton (R.Space v)) ↔ R.RepSupp ⊆ U := by
  constructor
  · intro h v hv
    by_contra hn
    exact (not_nontrivial_iff_subsingleton.mpr (h v hn)) hv
  · intro h v hv
    exact not_nontrivial_iff_subsingleton.mp (fun hn => hv (h hn))

def restrictSubrep {Q : Quiver} (U : Set Q.Vert) (R : Representation Q) (W : R.SubRep) :
    (Res U R).SubRep where
  space v := W.space v.val
  invariant a := W.invariant a.val
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def extendSubrep {Q : Quiver} (U : Set Q.Vert) (R : Supported U) (W : (Res U R.rep).SubRep) :
    R.rep.SubRep where
  space v := if hv : v ∈ U then W.space ⟨v,hv⟩ else ⊥
  invariant a := by
    intro x hx
    by_cases hs : Q.source a ∈ U
    · by_cases ht : Q.target a ∈ U
      · exact (by
          have hx' : x ∈ W.space ⟨Q.source a,hs⟩ := by simpa [hs] using hx
          have h := W.invariant ⟨a,hs,ht⟩ x hx'
          simp only [dite_eq_left ht]
          exact h)
      · haveI := R.outside_zero (Q.target a) ht
        have hz : R.rep.arrow a x=0 := Subsingleton.elim _ _
        simpa [ht,hz]
    · have hz : x=0 := by simpa [hs] using hx
      subst x
      simp

private theorem subrep_ext {Q : Quiver} {R : Representation Q} {W Z : R.SubRep}
    (h : ∀ v, W.space v = Z.space v) : W=Z := by
  cases W
  cases Z
  congr
  exact funext h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def subrepEquivalence {Q : Quiver} (U : Set Q.Vert) (R : Supported U) :
    R.rep.SubRep ≃ (Res U R.rep).SubRep where
  toFun := restrictSubrep U R.rep
  invFun := extendSubrep U R
  left_inv W := by
    apply subrep_ext
    intro v
    by_cases hv : v ∈ U
    · simp [extendSubrep,restrictSubrep,hv]
    · haveI := R.outside_zero v hv
      exact Subsingleton.elim _ _
  right_inv W := by
    apply subrep_ext
    intro v
    simp only [extendSubrep, restrictSubrep, dite_eq_left v.property]
    rfl

theorem subrep_dimension_preserved {Q : Quiver} (U : Set Q.Vert) (R : Supported U)
    (W : R.rep.SubRep) (v : U) :
    Module.finrank ℂ ((subrepEquivalence U R W).space v) =
      Module.finrank ℂ (W.space v.val) := rfl
end KroneckerManuscriptQuiverDefinitions.Representation
