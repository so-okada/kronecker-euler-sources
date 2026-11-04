import KroneckerAbelianQuiverIsoLift
import KroneckerIteratedArrowFibers

/- Original module: KroneckerAbelianTranslationQuiverAuto -/
section
/-! Full character translations are actual quiver automorphisms, including
their action on arrows, additive composition, and conjugation by lifted maps. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbelianTranslationQuiverAuto
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerAbelianCharacterReindex
open KroneckerAbelianQuiverIsoLift
variable {Q R : TypedQuiver}
attribute [local instance] Classical.decEq Classical.propDecidable

def translation (Q : TypedQuiver) (ξ : Character Q.A) : TypedQuiverIso Q.abelian Q.abelian where
  vertexEquiv := translate ξ
  arrowEquiv := translate ξ
  map_source a := rfl
  map_target a := by
    apply Prod.ext
    · rfl
    · change (a.2 + ξ) + unit a.1 = (a.2 + unit a.1) + ξ
      abel

theorem translation_zero (Q : TypedQuiver) : translation Q 0 = TypedQuiverIso.refl Q.abelian := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    change (x.1,x.2 + 0) = x
    exact Prod.ext rfl (add_zero _)

theorem translation_add (Q : TypedQuiver) (ξ η : Character Q.A) :
    translation Q (ξ + η) = TypedQuiverIso.trans (translation Q ξ) (translation Q η) := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    change (x.1,x.2 + (ξ + η)) = (x.1,(x.2 + ξ) + η)
    exact Prod.ext rfl (add_assoc _ _ _).symm

theorem translation_neg (Q : TypedQuiver) (ξ : Character Q.A) :
    translation Q (-ξ) = (translation Q ξ).symm := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    change (x.1,x.2 + -ξ) = (x.1,x.2 - ξ)
    simp only [sub_eq_add_neg]

theorem translation_lift (f : TypedQuiverIso Q R) (ξ : Character Q.A) :
    TypedQuiverIso.trans (translation Q ξ) (lift f) =
      TypedQuiverIso.trans (lift f) (translation R (reindex f.arrowEquiv ξ)) := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x <;> rfl

end KroneckerAbelianTranslationQuiverAuto
end
end

/- Original module: KroneckerAbelianAffineQuiverLift -/
section
/-! A lifted base isomorphism followed by character translation has the
semidirect composition and inverse laws needed for accumulated deck actions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbelianAffineQuiverLift
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerAbelianCharacterReindex
open KroneckerAbelianQuiverIsoLift KroneckerAbelianTranslationQuiverAuto
variable {Q R T : TypedQuiver}
attribute [local instance] Classical.decEq Classical.propDecidable

def affineLift (f : TypedQuiverIso Q R) (ξ : Character R.A) : TypedQuiverIso Q.abelian R.abelian :=
  TypedQuiverIso.trans (lift f) (translation R ξ)

theorem affine_vertex (f : TypedQuiverIso Q R) (ξ : Character R.A) (x : Q.abelian.V) :
    (affineLift f ξ).vertexEquiv x = (f.vertexEquiv x.1,reindex f.arrowEquiv x.2 + ξ) := rfl

theorem affine_arrow (f : TypedQuiverIso Q R) (ξ : Character R.A) (x : Q.abelian.A) :
    (affineLift f ξ).arrowEquiv x = (f.arrowEquiv x.1,reindex f.arrowEquiv x.2 + ξ) := rfl

theorem affine_identity (Q : TypedQuiver) :
    affineLift (TypedQuiverIso.refl Q) 0 = TypedQuiverIso.refl Q.abelian := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    change (x.1,x.2 + 0) = x
    exact Prod.ext rfl (add_zero _)

theorem affine_composition (f : TypedQuiverIso Q R) (g : TypedQuiverIso R T)
    (ξ : Character R.A) (η : Character T.A) :
    TypedQuiverIso.trans (affineLift f ξ) (affineLift g η) =
      affineLift (TypedQuiverIso.trans f g) (reindex g.arrowEquiv ξ + η) := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    apply Prod.ext
    · rfl
    · change reindex g.arrowEquiv (reindex f.arrowEquiv x.2 + ξ) + η =
        reindex g.arrowEquiv (reindex f.arrowEquiv x.2) + (reindex g.arrowEquiv ξ + η)
      rw [map_add,add_assoc]

theorem affine_inverse (f : TypedQuiverIso Q R) (ξ : Character R.A) :
    (affineLift f ξ).symm = affineLift f.symm (-reindex f.arrowEquiv.symm ξ) := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    apply Prod.ext
    · rfl
    · change reindex f.arrowEquiv.symm (x.2 - ξ) =
        reindex f.arrowEquiv.symm x.2 + -reindex f.arrowEquiv.symm ξ
      rw [map_sub,sub_eq_add_neg]

end KroneckerAbelianAffineQuiverLift
end
end

/- Original module: KroneckerAccumulatedCoverDeckActions -/
section
/-! Accumulated deck maps include transformations from every earlier abelian
stage, lifted through the remaining stages. They form a composition- and
inverse-closed class of actual quiver automorphisms, not only final translations. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedCoverDeckActions
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerAbelianCharacterReindex
open KroneckerAbelianAffineQuiverLift
attribute [local instance] Classical.decEq Classical.propDecidable

def Accumulated (Q : TypedQuiver) :
    (n : ℕ) → TypedQuiverIso (Q.iterate n) (Q.iterate n) → Prop
  | 0,f => f = TypedQuiverIso.refl Q
  | n+1,f => ∃ (g : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (ξ : Character (Q.iterate n).A),
      Accumulated Q n g ∧ f = affineLift g ξ

theorem accumulated_refl (Q : TypedQuiver) (n : ℕ) :
    Accumulated Q n (TypedQuiverIso.refl (Q.iterate n)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨_,0,ih,(affine_identity (Q.iterate n)).symm⟩

theorem accumulated_trans (Q : TypedQuiver) (n : ℕ)
    (f g : TypedQuiverIso (Q.iterate n) (Q.iterate n))
    (hf : Accumulated Q n f) (hg : Accumulated Q n g) :
    Accumulated Q n (TypedQuiverIso.trans f g) := by
  induction n with
  | zero =>
    change f = TypedQuiverIso.refl Q at hf
    change g = TypedQuiverIso.refl Q at hg
    subst f; subst g
    rfl
  | succ n ih =>
    obtain ⟨f',ξ,hf',rfl⟩ := hf
    obtain ⟨g',η,hg',rfl⟩ := hg
    exact ⟨_,_,ih f' g' hf' hg',affine_composition f' g' ξ η⟩

theorem accumulated_symm (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (hf : Accumulated Q n f) :
    Accumulated Q n f.symm := by
  induction n with
  | zero =>
    change f = TypedQuiverIso.refl Q at hf
    subst f
    rfl
  | succ n ih =>
    obtain ⟨g,ξ,hg,rfl⟩ := hf
    exact ⟨g.symm,_,ih g hg,affine_inverse g ξ⟩

abbrev Deck (Q : TypedQuiver) (n : ℕ) :=
  {f : TypedQuiverIso (Q.iterate n) (Q.iterate n) // Accumulated Q n f}

def identity (Q : TypedQuiver) (n : ℕ) : Deck Q n := ⟨_,accumulated_refl Q n⟩
def compose {Q : TypedQuiver} {n : ℕ} (f g : Deck Q n) : Deck Q n :=
  ⟨TypedQuiverIso.trans f.val g.val,accumulated_trans Q n f.val g.val f.property g.property⟩
def inverse {Q : TypedQuiver} {n : ℕ} (f : Deck Q n) : Deck Q n :=
  ⟨f.val.symm,accumulated_symm Q n f.val f.property⟩

end KroneckerAccumulatedCoverDeckActions
end
end

/- Original module: KroneckerIteratedQuiverBaseProjection -/
section
/-! The accumulated base projections respect actual arrow endpoints, and
projecting an entire walk is exactly mapping every signed arrow label. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerIteratedQuiverBaseProjection
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver LabeledWalk
attribute [local instance] Classical.decEq Classical.propDecidable

theorem base_source (Q : TypedQuiver) (n : ℕ) (a : (Q.iterate n).A) :
    baseVertex Q n ((Q.iterate n).source a) = Q.source (baseArrow Q n a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih a.1

theorem base_target (Q : TypedQuiver) (n : ℕ) (a : (Q.iterate n).A) :
    baseVertex Q n ((Q.iterate n).target a) = Q.target (baseArrow Q n a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih a.1

set_option backward.isDefEq.respectTransparency false in
theorem base_labels (Q : TypedQuiver) (n : ℕ) {u v : (Q.iterate n).V}
    (p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v) :
    labels (baseWalk Q n p) = (labels p).map (fun x => (baseArrow Q n x.1,x.2)) := by
  induction n with
  | zero =>
    change p.labels = p.labels.map (fun x => x)
    exact (List.map_id _).symm
  | succ n ih =>
    change labels (baseWalk Q n (project p)) = _
    rw [ih,labels_project,List.map_map]
    rfl

end KroneckerIteratedQuiverBaseProjection
end
end

/- Original module: KroneckerAccumulatedDeckBaseLabels -/
section
/-! Accumulated deck transformations preserve every original vertex and arrow
label through all stages, not merely the final cover projection. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDeckBaseLabels
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerAccumulatedCoverDeckActions KroneckerAbelianAffineQuiverLift
attribute [local instance] Classical.decEq Classical.propDecidable

theorem vertex_base_invariant (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (hf : Accumulated Q n f)
    (v : (Q.iterate n).V) : baseVertex Q n (f.vertexEquiv v) = baseVertex Q n v := by
  induction n with
  | zero =>
    change f = TypedQuiverIso.refl Q at hf
    subst f
    rfl
  | succ n ih =>
    obtain ⟨g,ξ,hg,rfl⟩ := hf
    exact ih g hg v.1

theorem arrow_base_invariant (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (hf : Accumulated Q n f)
    (a : (Q.iterate n).A) : baseArrow Q n (f.arrowEquiv a) = baseArrow Q n a := by
  induction n with
  | zero =>
    change f = TypedQuiverIso.refl Q at hf
    subst f
    rfl
  | succ n ih =>
    obtain ⟨g,ξ,hg,rfl⟩ := hf
    exact ih g hg a.1

theorem vertex_weight_invariant (Q : TypedQuiver) (n : ℕ) (f : Deck Q n)
    (θ : Q.V → ℤ) (v : (Q.iterate n).V) :
    θ (baseVertex Q n (f.val.vertexEquiv v)) = θ (baseVertex Q n v) := by
  rw [vertex_base_invariant Q n f.val f.property]

end KroneckerAccumulatedDeckBaseLabels
end
end
