import KroneckerAccumulatedConnectedMapRigidity
import KroneckerEmbeddedStabilityEquivalence
import KroneckerAccumulatedDimensionClasses

section

/- Original module: KroneckerDirectSumCharacterNaturality -/
section
/-! Extension of direct-sum characters along arrow maps is natural under a
commuting square of arrow equivalences. The equality is on every product
coordinate, including coordinates outside an embedded arrow image. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumCharacterNaturality
open KroneckerAbelianCover KroneckerAbelianCharacterReindex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A B C D : Type}

theorem domCongr_eq_mapDomain (e : A ≃ B) (χ : A →₀ ℤ) :
    Finsupp.domCongr e χ = χ.mapDomain e := Finsupp.equivMapDomain_eq_mapDomain e χ

theorem coe_domCongr (e : A ≃ B) (χ : A →₀ ℤ) :
    ((Finsupp.domCongr e χ : B →₀ ℤ) : B → ℤ) = reindex e (χ : A → ℤ) := rfl

theorem push_naturality (i : A → B) (j : C → D) (e : A ≃ C) (f : B ≃ D)
    (h : ∀ a, f (i a) = j (e a)) (χ : A →₀ ℤ) :
    Finsupp.domCongr f (χ.mapDomain i) = (Finsupp.domCongr e χ).mapDomain j := by
  rw [domCongr_eq_mapDomain,domCongr_eq_mapDomain,← Finsupp.mapDomain_comp,← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro a _
  exact h a

theorem product_push_naturality (i : A → B) (j : C → D) (e : A ≃ C) (f : B ≃ D)
    (h : ∀ a, f (i a) = j (e a)) (χ : A →₀ ℤ) :
    reindex f ((χ.mapDomain i : B →₀ ℤ) : B → ℤ) =
      (((Finsupp.domCongr e χ).mapDomain j : D →₀ ℤ) : D → ℤ) := by
  rw [← coe_domCongr,push_naturality i j e f h χ]

theorem inverse_square (i : A → B) (j : C → D) (e : A ≃ C) (f : B ≃ D)
    (h : ∀ a, f (i a) = j (e a)) (c : C) :
    f.symm (j c) = i (e.symm c) := by
  apply f.injective
  rw [Equiv.apply_symm_apply,h,Equiv.apply_symm_apply]

end KroneckerDirectSumCharacterNaturality
end
end

/- Original module: KroneckerDirectSumQuiverIsoLift -/
section
/-! Quiver isomorphisms lift functorially to the genuine direct-sum abelian
cover by reindexing finite integer characters. The unit displacement and both
arrow endpoints are preserved, including for infinite arrow types. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumQuiverIsoLift
open KroneckerAbelianCover KroneckerDirectSumAbelianCover
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q R : TypedQuiver}

def lift (f : TypedQuiverIso P Q) : TypedQuiverIso (directCover P) (directCover Q) where
  vertexEquiv := Equiv.prodCongr f.vertexEquiv (Finsupp.domCongr f.arrowEquiv).toEquiv
  arrowEquiv := Equiv.prodCongr f.arrowEquiv (Finsupp.domCongr f.arrowEquiv).toEquiv
  map_source a := by
    apply Prod.ext
    · exact f.map_source a.1
    · rfl
  map_target a := by
    apply Prod.ext
    · exact f.map_target a.1
    · change Finsupp.domCongr f.arrowEquiv a.2 + Finsupp.single (f.arrowEquiv a.1) 1 =
        Finsupp.domCongr f.arrowEquiv (a.2 + Finsupp.single a.1 1)
      rw [map_add]
      exact congrArg (fun χ => Finsupp.domCongr f.arrowEquiv a.2 + χ)
        (Finsupp.equivMapDomain_single f.arrowEquiv a.1 (1:ℤ)).symm

theorem lift_refl (Q : TypedQuiver) : lift (TypedQuiverIso.refl Q) = TypedQuiverIso.refl (directCover Q) := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    apply Prod.ext
    · rfl
    · apply Finsupp.ext
      intro a
      rfl

theorem lift_trans (f : TypedQuiverIso P Q) (g : TypedQuiverIso Q R) :
    lift (TypedQuiverIso.trans f g) = TypedQuiverIso.trans (lift f) (lift g) := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    apply Prod.ext
    · rfl
    · apply Finsupp.ext
      intro a
      rfl

theorem lift_symm (f : TypedQuiverIso P Q) : lift f.symm = (lift f).symm := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    apply Prod.ext
    · rfl
    · apply Finsupp.ext
      intro a
      rfl

end KroneckerDirectSumQuiverIsoLift
end
end

/- Original module: KroneckerDirectSumAffineDeckLift -/
section
/-! Finite-character translations and affine lifts in the direct-sum cover,
with checked semidirect composition and inverse laws on actual quiver maps. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumAffineDeckLift
open KroneckerAbelianCover KroneckerDirectSumAbelianCover KroneckerDirectSumQuiverIsoLift
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q R : TypedQuiver}

def translate {X A : Type} (ξ : A →₀ ℤ) : (X × (A →₀ ℤ)) ≃ (X × (A →₀ ℤ)) where
  toFun x := (x.1,x.2+ξ)
  invFun x := (x.1,x.2-ξ)
  left_inv x := by apply Prod.ext <;> simp
  right_inv x := by apply Prod.ext <;> simp

def translation (Q : TypedQuiver) (ξ : Q.A →₀ ℤ) : TypedQuiverIso (directCover Q) (directCover Q) where
  vertexEquiv := translate ξ
  arrowEquiv := translate ξ
  map_source _ := rfl
  map_target a := by
    apply Prod.ext
    · rfl
    · change (a.2+ξ)+Finsupp.single a.1 1 = (a.2+Finsupp.single a.1 1)+ξ
      abel

def affineLift (f : TypedQuiverIso P Q) (ξ : Q.A →₀ ℤ) : TypedQuiverIso (directCover P) (directCover Q) :=
  TypedQuiverIso.trans (lift f) (translation Q ξ)

theorem affine_vertex (f : TypedQuiverIso P Q) (ξ : Q.A →₀ ℤ) (x : (directCover P).V) :
    (affineLift f ξ).vertexEquiv x = (f.vertexEquiv x.1,Finsupp.domCongr f.arrowEquiv x.2+ξ) := rfl

theorem affine_arrow (f : TypedQuiverIso P Q) (ξ : Q.A →₀ ℤ) (x : (directCover P).A) :
    (affineLift f ξ).arrowEquiv x = (f.arrowEquiv x.1,Finsupp.domCongr f.arrowEquiv x.2+ξ) := rfl

theorem affine_identity (Q : TypedQuiver) :
    affineLift (TypedQuiverIso.refl Q) 0 = TypedQuiverIso.refl (directCover Q) := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    apply Prod.ext
    · rfl
    · change Finsupp.domCongr (Equiv.refl Q.A) x.2 + 0 = x.2
      rw [Finsupp.domCongr_refl,AddEquiv.refl_apply,add_zero]

theorem affine_composition (f : TypedQuiverIso P Q) (g : TypedQuiverIso Q R)
    (ξ : Q.A →₀ ℤ) (η : R.A →₀ ℤ) :
    TypedQuiverIso.trans (affineLift f ξ) (affineLift g η) =
      affineLift (TypedQuiverIso.trans f g) (Finsupp.domCongr g.arrowEquiv ξ+η) := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    apply Prod.ext
    · rfl
    · change Finsupp.domCongr g.arrowEquiv (Finsupp.domCongr f.arrowEquiv x.2+ξ)+η =
        Finsupp.domCongr (f.arrowEquiv.trans g.arrowEquiv) x.2+(Finsupp.domCongr g.arrowEquiv ξ+η)
      rw [map_add]
      rw [show Finsupp.domCongr (f.arrowEquiv.trans g.arrowEquiv) x.2 =
        Finsupp.domCongr g.arrowEquiv (Finsupp.domCongr f.arrowEquiv x.2) from
          Finsupp.equivMapDomain_trans _ _ _]
      exact add_assoc _ _ _

theorem affine_inverse (f : TypedQuiverIso P Q) (ξ : Q.A →₀ ℤ) :
    (affineLift f ξ).symm = affineLift f.symm (-Finsupp.domCongr f.arrowEquiv.symm ξ) := by
  apply quiverIso_ext <;> apply Equiv.ext <;> intro x
  all_goals
    apply Prod.ext
    · rfl
    · change Finsupp.domCongr f.arrowEquiv.symm (x.2-ξ) =
        Finsupp.domCongr f.arrowEquiv.symm x.2 + -Finsupp.domCongr f.arrowEquiv.symm ξ
      rw [map_sub,sub_eq_add_neg]

end KroneckerDirectSumAffineDeckLift
end
end

/- Original module: KroneckerDirectSumAccumulatedActions -/
section
/-! The recursively accumulated deck maps of the precise direct-sum iterates.
Translations are finitely supported on the preceding-stage actual arrows, and
identity, composition and inverse stay within this exact class. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumAccumulatedActions
open KroneckerAbelianCover KroneckerDirectSumIteratedGirth
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerDirectSumAffineDeckLift
attribute [local instance] Classical.decEq Classical.propDecidable

def Accumulated (Q : TypedQuiver) : (n : ℕ) → TypedQuiverIso (iterate Q n) (iterate Q n) → Prop
  | 0,f => f = TypedQuiverIso.refl Q
  | n+1,f => ∃ (g : TypedQuiverIso (iterate Q n) (iterate Q n)) (ξ : (iterate Q n).A →₀ ℤ),
      Accumulated Q n g ∧ f = affineLift g ξ

theorem accumulated_refl (Q : TypedQuiver) (n : ℕ) :
    Accumulated Q n (TypedQuiverIso.refl (iterate Q n)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨_,0,ih,(affine_identity (iterate Q n)).symm⟩

theorem accumulated_trans (Q : TypedQuiver) (n : ℕ)
    (f g : TypedQuiverIso (iterate Q n) (iterate Q n))
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
    (f : TypedQuiverIso (iterate Q n) (iterate Q n)) (hf : Accumulated Q n f) :
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
  {f : TypedQuiverIso (iterate Q n) (iterate Q n) // Accumulated Q n f}

def identity (Q : TypedQuiver) (n : ℕ) : Deck Q n := ⟨_,accumulated_refl Q n⟩
def compose {Q : TypedQuiver} {n : ℕ} (f g : Deck Q n) : Deck Q n :=
  ⟨TypedQuiverIso.trans f.val g.val,accumulated_trans Q n f.val g.val f.property g.property⟩
def inverse {Q : TypedQuiver} {n : ℕ} (f : Deck Q n) : Deck Q n :=
  ⟨f.val.symm,accumulated_symm Q n f.val f.property⟩

end KroneckerDirectSumAccumulatedActions
end
end

/- Original module: KroneckerDirectSumDeckCompatibility -/
section
/-! Exact compatibility of direct-sum and product-cover automorphisms means
commutation on all vertices AND arrows. Affine lifts preserve compatibility
when their translation is pushed along the actual preceding arrow embedding. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumDeckCompatibility
open KroneckerAbelianCover KroneckerDirectSumIteratedEmbedding
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerDirectSumCoverEmbeddingLift KroneckerDirectSumCharacterNaturality
attribute [local instance] Classical.decEq Classical.propDecidable

def Compatible (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) : Prop :=
  (∀ v, F.vertexEquiv ((embedding Q n).vertex v) = (embedding Q n).vertex (f.vertexEquiv v)) ∧
  (∀ a, F.arrowEquiv ((embedding Q n).arrow a) = (embedding Q n).arrow (f.arrowEquiv a))

theorem compatible_identity (Q : TypedQuiver) (n : ℕ) :
    Compatible Q n (TypedQuiverIso.refl _) (TypedQuiverIso.refl _) := ⟨fun _ => rfl,fun _ => rfl⟩

theorem compatible_affine (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (h : Compatible Q n f F)
    (ξ : (KroneckerDirectSumIteratedGirth.iterate Q n).A →₀ ℤ) :
    Compatible Q (n+1) (KroneckerDirectSumAffineDeckLift.affineLift f ξ)
      (KroneckerAbelianAffineQuiverLift.affineLift F (pushCharacter (embedding Q n) ξ)) := by
  constructor <;> intro x
  all_goals
    apply Prod.ext
    · first | exact h.1 x.1 | exact h.2 x.1
    · change KroneckerAbelianCharacterReindex.reindex F.arrowEquiv
        (pushCharacter (embedding Q n) x.2) + pushCharacter (embedding Q n) ξ =
          pushCharacter (embedding Q n) (Finsupp.domCongr f.arrowEquiv x.2+ξ)
      rw [pushCharacter_add]
      exact congrArg (fun χ => χ + pushCharacter (embedding Q n) ξ)
        (product_push_naturality _ _ f.arrowEquiv F.arrowEquiv h.2 x.2)

theorem compatible_direct_unique (Q : TypedQuiver) (n : ℕ)
    (f g : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n))
    (hf : Compatible Q n f F) (hg : Compatible Q n g F) : f = g := by
  apply quiverIso_ext
  · ext v
    exact (embedding_injective Q n).1 ((hf.1 v).symm.trans (hg.1 v))
  · ext a
    exact (embedding_injective Q n).2 ((hf.2 a).symm.trans (hg.2 a))

end KroneckerDirectSumDeckCompatibility
end
end
end

section

/-! Every accumulated direct-sum deck map extends to an accumulated product
map with both vertex and arrow compatibility. The extension is faithful and,
when a direct-sum root is specified, unique as an accumulated product map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumDeckExtension
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumCoverEmbeddingLift
open KroneckerDirectSumDeckCompatibility
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_extension (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (hf : KroneckerDirectSumAccumulatedActions.Accumulated Q n f) :
    ∃ F : KroneckerAccumulatedCoverDeckActions.Deck Q n, Compatible Q n f F.val := by
  induction n with
  | zero =>
    change f = KroneckerQuiverPullbackComposition.TypedQuiverIso.refl Q at hf
    subst f
    exact ⟨KroneckerAccumulatedCoverDeckActions.identity Q 0,compatible_identity Q 0⟩
  | succ n ih =>
    obtain ⟨g,ξ,hg,rfl⟩ := hf
    obtain ⟨G,hG⟩ := ih g hg
    refine ⟨⟨KroneckerAbelianAffineQuiverLift.affineLift G.val (pushCharacter (embedding Q n) ξ),
      ⟨G.val,_,G.property,rfl⟩⟩,compatible_affine Q n g G.val hG ξ⟩

def extension {Q : TypedQuiver} {n : ℕ} (f : KroneckerDirectSumAccumulatedActions.Deck Q n) :
    KroneckerAccumulatedCoverDeckActions.Deck Q n := Classical.choose (exists_extension Q n f.val f.property)

theorem extension_compatible {Q : TypedQuiver} {n : ℕ} (f : KroneckerDirectSumAccumulatedActions.Deck Q n) :
    Compatible Q n f.val (extension f).val := Classical.choose_spec (exists_extension Q n f.val f.property)

theorem extension_injective (Q : TypedQuiver) (n : ℕ) :
    Function.Injective (extension (Q:=Q) (n:=n)) := by
  intro f g h
  apply Subtype.ext
  exact compatible_direct_unique Q n f.val g.val (extension f).val
    (extension_compatible f) (h ▸ extension_compatible g)

theorem compatible_product_unique (Q : TypedQuiver) (n : ℕ)
    (u : (KroneckerDirectSumIteratedGirth.iterate Q n).V)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F G : KroneckerAccumulatedCoverDeckActions.Deck Q n)
    (hF : Compatible Q n f F.val) (hG : Compatible Q n f G.val) : F = G :=
  KroneckerAccumulatedDeckFreeAction.deck_ext_at Q n F G ((embedding Q n).vertex u)
    ((hF.1 u).trans (hG.1 u).symm)

end KroneckerDirectSumDeckExtension
end
end

section

/- Original module: KroneckerDirectSumForcedTranslation -/
section
/-! Once the preceding map is compatible, taking one direct-sum root to another
forces the final product-character translation to be the pushforward of an
explicit finite character. All coordinates outside the preceding arrow image
therefore vanish. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumForcedTranslation
open KroneckerAbelianCover KroneckerTypedQuiverMaps
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumCoverEmbeddingLift
open KroneckerDirectSumDeckCompatibility KroneckerDirectSumCharacterNaturality
open KroneckerFiniteSupportDeckRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable

theorem pushCharacter_sub {P Q : TypedQuiver} (f : QuiverMap P Q) (χ ψ : P.A →₀ ℤ) :
    pushCharacter f (χ-ψ) = pushCharacter f χ - pushCharacter f ψ := by
  unfold pushCharacter
  rw [show (χ-ψ).mapDomain f.arrow = χ.mapDomain f.arrow - ψ.mapDomain f.arrow from
    map_sub (Finsupp.mapDomain.addMonoidHom f.arrow) χ ψ]
  rfl

theorem forced_translation (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (hc : Compatible Q n f F)
    (ξ : Character (Q.iterate n).A)
    (u v : (KroneckerDirectSumIteratedGirth.iterate Q (n+1)).V)
    (h : (KroneckerAbelianAffineQuiverLift.affineLift F ξ).vertexEquiv ((embedding Q (n+1)).vertex u) =
      (embedding Q (n+1)).vertex v) :
    ξ = pushCharacter (embedding Q n) (v.2-Finsupp.domCongr f.arrowEquiv u.2) := by
  have hh := congrArg (fun x : (Q.iterate (n+1)).V => x.2) h
  change KroneckerAbelianCharacterReindex.reindex F.arrowEquiv
    (pushCharacter (embedding Q n) u.2)+ξ = pushCharacter (embedding Q n) v.2 at hh
  have hn : KroneckerAbelianCharacterReindex.reindex F.arrowEquiv
      (pushCharacter (embedding Q n) u.2) =
      pushCharacter (embedding Q n) (Finsupp.domCongr f.arrowEquiv u.2) :=
    product_push_naturality _ _ f.arrowEquiv F.arrowEquiv hc.2 u.2
  rw [hn] at hh
  rw [pushCharacter_sub]
  apply add_left_cancel (a:=pushCharacter (embedding Q n) (Finsupp.domCongr f.arrowEquiv u.2))
  calc
    _ = pushCharacter (embedding Q n) v.2 := hh
    _ = _ := by abel


end KroneckerDirectSumForcedTranslation
end
end

/- Original module: KroneckerDirectSumAccumulatedRestriction -/
section
/-! An accumulated product-cover map sending just one embedded direct-sum root
to another comes from a unique accumulated DIRECT-SUM map on every vertex and
arrow. The finite translation is forced at each recursive stage. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumAccumulatedRestriction
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumDeckCompatibility
open KroneckerDirectSumForcedTranslation KroneckerDirectSumCoverEmbeddingLift
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_restriction (Q : TypedQuiver) (n : ℕ)
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n))
    (hF : KroneckerAccumulatedCoverDeckActions.Accumulated Q n F)
    (u v : (KroneckerDirectSumIteratedGirth.iterate Q n).V)
    (h : F.vertexEquiv ((embedding Q n).vertex u) = (embedding Q n).vertex v) :
    ∃ f : KroneckerDirectSumAccumulatedActions.Deck Q n, Compatible Q n f.val F := by
  induction n with
  | zero =>
    change F = KroneckerQuiverPullbackComposition.TypedQuiverIso.refl Q at hF
    subst F
    exact ⟨KroneckerDirectSumAccumulatedActions.identity Q 0,compatible_identity Q 0⟩
  | succ n ih =>
    obtain ⟨G,ξ,hG,rfl⟩ := hF
    have hbase : G.vertexEquiv ((embedding Q n).vertex u.1) = (embedding Q n).vertex v.1 :=
      congrArg (fun x : (Q.iterate (n+1)).V => x.1) h
    obtain ⟨g,hg⟩ := ih G hG u.1 v.1 hbase
    have hξ := forced_translation Q n g.val G hg ξ u v h
    let ζ := v.2-Finsupp.domCongr g.val.arrowEquiv u.2
    refine ⟨⟨KroneckerDirectSumAffineDeckLift.affineLift g.val ζ,⟨g.val,ζ,g.property,rfl⟩⟩,?_⟩
    rw [hξ]
    exact compatible_affine Q n g.val G hg ζ


end KroneckerDirectSumAccumulatedRestriction
end
end
end

section

/-! Compatibility is stable under composition and inverses. Compatible maps
preserve the entire direct-sum image in both directions, on vertices and on
actual arrows; extension therefore respects the accumulated action laws. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumCompatibilityFunctor
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerDirectSumIteratedEmbedding
open KroneckerDirectSumDeckCompatibility KroneckerDirectSumDeckExtension
attribute [local instance] Classical.decEq Classical.propDecidable


theorem compatible_symm (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (h : Compatible Q n f F) :
    Compatible Q n f.symm F.symm := by
  constructor
  · intro v
    apply F.vertexEquiv.injective
    change F.vertexEquiv (F.vertexEquiv.symm ((embedding Q n).vertex v)) =
      F.vertexEquiv ((embedding Q n).vertex (f.vertexEquiv.symm v))
    rw [Equiv.apply_symm_apply,h.1,Equiv.apply_symm_apply]
  · intro a
    apply F.arrowEquiv.injective
    change F.arrowEquiv (F.arrowEquiv.symm ((embedding Q n).arrow a)) =
      F.arrowEquiv ((embedding Q n).arrow (f.arrowEquiv.symm a))
    rw [Equiv.apply_symm_apply,h.2,Equiv.apply_symm_apply]

theorem image_vertex_iff (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (h : Compatible Q n f F) (v : (Q.iterate n).V) :
    v ∈ Set.range (embedding Q n).vertex ↔ F.vertexEquiv v ∈ Set.range (embedding Q n).vertex := by
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨f.vertexEquiv u,(h.1 u).symm⟩
  · rintro ⟨u,hu⟩
    refine ⟨f.vertexEquiv.symm u,?_⟩
    apply F.vertexEquiv.injective
    rw [h.1,Equiv.apply_symm_apply]
    exact hu




end KroneckerDirectSumCompatibilityFunctor
end
end

section

/- Original module: KroneckerDirectSumRootImageEquivalence -/
section
/-! Accumulated direct-sum maps are exactly the accumulated product maps that
send one specified embedded root into the direct-sum image. Restriction and
extension are inverse; the root-image condition is independent of the chosen
direct-sum root and preserves the full vertex and arrow images. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumRootImageEquivalence
open KroneckerAbelianCover KroneckerDirectSumIteratedEmbedding
open KroneckerDirectSumDeckCompatibility KroneckerDirectSumDeckExtension
open KroneckerDirectSumAccumulatedRestriction KroneckerDirectSumCompatibilityFunctor
attribute [local instance] Classical.decEq Classical.propDecidable

def RootImageDeck (Q : TypedQuiver) (n : ℕ) (u : (KroneckerDirectSumIteratedGirth.iterate Q n).V) :=
  {F : KroneckerAccumulatedCoverDeckActions.Deck Q n //
    F.val.vertexEquiv ((embedding Q n).vertex u) ∈ Set.range (embedding Q n).vertex}

theorem root_image_exists_restriction (Q : TypedQuiver) (n : ℕ)
    (u : (KroneckerDirectSumIteratedGirth.iterate Q n).V) (F : RootImageDeck Q n u) :
    ∃ f : KroneckerDirectSumAccumulatedActions.Deck Q n, Compatible Q n f.val F.val.val := by
  obtain ⟨v,hv⟩ := F.property
  exact exists_restriction Q n F.val.val F.val.property u v hv.symm

def restriction {Q : TypedQuiver} {n : ℕ} {u : (KroneckerDirectSumIteratedGirth.iterate Q n).V}
    (F : RootImageDeck Q n u) : KroneckerDirectSumAccumulatedActions.Deck Q n :=
  Classical.choose (root_image_exists_restriction Q n u F)

theorem restriction_compatible {Q : TypedQuiver} {n : ℕ} {u : (KroneckerDirectSumIteratedGirth.iterate Q n).V}
    (F : RootImageDeck Q n u) : Compatible Q n (restriction F).val F.val.val :=
  Classical.choose_spec (root_image_exists_restriction Q n u F)

def rootImageEquiv (Q : TypedQuiver) (n : ℕ) (u : (KroneckerDirectSumIteratedGirth.iterate Q n).V) :
    KroneckerDirectSumAccumulatedActions.Deck Q n ≃ RootImageDeck Q n u where
  toFun f := ⟨extension f,⟨f.val.vertexEquiv u,((extension_compatible f).1 u).symm⟩⟩
  invFun := restriction
  left_inv f := Subtype.ext (compatible_direct_unique Q n _ f.val (extension f).val
    (restriction_compatible _) (extension_compatible f))
  right_inv F := Subtype.ext (compatible_product_unique Q n u (restriction F).val _ F.val
    (extension_compatible _) (restriction_compatible F))



end KroneckerDirectSumRootImageEquivalence
end
end

/- Original module: KroneckerDirectSumDeckRootTorsor -/
section
/-! The genuine direct-sum accumulated deck action is free and transitive on
each original-vertex fiber. Both base labels are preserved and a unique actual
quiver map moves any chosen root to any other root over the same base vertex. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumDeckRootTorsor
open KroneckerAbelianCover KroneckerDirectSumIteratedEmbedding
open KroneckerDirectSumDeckCompatibility KroneckerDirectSumDeckExtension
open KroneckerDirectSumAccumulatedRestriction
attribute [local instance] Classical.decEq Classical.propDecidable

theorem vertex_base_invariant (Q : TypedQuiver) (n : ℕ)
    (f : KroneckerDirectSumAccumulatedActions.Deck Q n) (v : (KroneckerDirectSumIteratedGirth.iterate Q n).V) :
    baseVertex Q n (f.val.vertexEquiv v) = baseVertex Q n v := by
  calc
    _ = TypedQuiver.baseVertex Q n ((embedding Q n).vertex (f.val.vertexEquiv v)) := (embedding_base_vertex Q n _).symm
    _ = TypedQuiver.baseVertex Q n ((extension f).val.vertexEquiv ((embedding Q n).vertex v)) :=
      congrArg (TypedQuiver.baseVertex Q n) ((extension_compatible f).1 v).symm
    _ = TypedQuiver.baseVertex Q n ((embedding Q n).vertex v) :=
      KroneckerAccumulatedDeckBaseLabels.vertex_base_invariant Q n _ (extension f).property _
    _ = _ := embedding_base_vertex Q n v

theorem arrow_base_invariant (Q : TypedQuiver) (n : ℕ)
    (f : KroneckerDirectSumAccumulatedActions.Deck Q n) (a : (KroneckerDirectSumIteratedGirth.iterate Q n).A) :
    baseArrow Q n (f.val.arrowEquiv a) = baseArrow Q n a := by
  calc
    _ = TypedQuiver.baseArrow Q n ((embedding Q n).arrow (f.val.arrowEquiv a)) := (embedding_base_arrow Q n _).symm
    _ = TypedQuiver.baseArrow Q n ((extension f).val.arrowEquiv ((embedding Q n).arrow a)) :=
      congrArg (TypedQuiver.baseArrow Q n) ((extension_compatible f).2 a).symm
    _ = TypedQuiver.baseArrow Q n ((embedding Q n).arrow a) :=
      KroneckerAccumulatedDeckBaseLabels.arrow_base_invariant Q n _ (extension f).property _
    _ = _ := embedding_base_arrow Q n a

theorem deck_ext_at (Q : TypedQuiver) (n : ℕ) (f g : KroneckerDirectSumAccumulatedActions.Deck Q n)
    (u : (KroneckerDirectSumIteratedGirth.iterate Q n).V)
    (h : f.val.vertexEquiv u = g.val.vertexEquiv u) : f = g := by
  apply extension_injective Q n
  apply KroneckerAccumulatedDeckFreeAction.deck_ext_at Q n _ _ ((embedding Q n).vertex u)
  rw [(extension_compatible f).1,(extension_compatible g).1,h]

theorem exists_deck (Q : TypedQuiver) (n : ℕ)
    (u v : (KroneckerDirectSumIteratedGirth.iterate Q n).V) (h : baseVertex Q n u = baseVertex Q n v) :
    ∃! f : KroneckerDirectSumAccumulatedActions.Deck Q n, f.val.vertexEquiv u = v := by
  obtain ⟨F,hF⟩ := KroneckerAccumulatedDeckRootTransitivity.exists_deck_to_root Q n
    ((embedding Q n).vertex u) ((embedding Q n).vertex v) (by simpa only [embedding_base_vertex] using h)
  obtain ⟨f,hf⟩ := exists_restriction Q n F.val F.property u v hF
  have hv : f.val.vertexEquiv u = v := (embedding_injective Q n).1 ((hf.1 u).symm.trans hF)
  exact ⟨f,hv,fun g hg => deck_ext_at Q n g f u (hg.trans hv.symm)⟩

def fiberEquiv (Q : TypedQuiver) (n : ℕ) (u : (KroneckerDirectSumIteratedGirth.iterate Q n).V) :
    KroneckerDirectSumAccumulatedActions.Deck Q n ≃
      {v : (KroneckerDirectSumIteratedGirth.iterate Q n).V // baseVertex Q n v = baseVertex Q n u} :=
  Equiv.ofBijective (fun f => ⟨f.val.vertexEquiv u,vertex_base_invariant Q n f u⟩)
    ⟨fun f g h => deck_ext_at Q n f g u (congrArg Subtype.val h),by
      intro v
      obtain ⟨f,hf,_⟩ := exists_deck Q n u v.val v.property.symm
      exact ⟨f,Subtype.ext hf⟩⟩

end KroneckerDirectSumDeckRootTorsor
end
end
end

section

/-! Pushforward of actual finite dimension vectors intertwines compatible
quiver pullbacks exactly, including off-image zero coordinates. Descent is the
inverse on image-supported dimensions, and the image condition is preserved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumDimensionNaturality
open KroneckerAbelianCover KroneckerDirectSumIteratedEmbedding
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerAccumulatedDeckBaseDimensions
open KroneckerDirectSumDeckCompatibility KroneckerDirectSumCompatibilityFunctor
open KroneckerEmbeddedFiniteDimensions
attribute [local instance] Classical.decEq Classical.propDecidable

def pushDimension (Q : TypedQuiver) (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) : (Q.iterate n).V →₀ ℕ :=
  d.mapDomain (embedding Q n).vertex

theorem pushDimension_injective (Q : TypedQuiver) (n : ℕ) : Function.Injective (pushDimension Q n) :=
  Finsupp.mapDomain_injective (embedding_injective Q n).1

theorem pushDimension_apply (Q : TypedQuiver) (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ)
    (v : (KroneckerDirectSumIteratedGirth.iterate Q n).V) :
    pushDimension Q n d ((embedding Q n).vertex v) = d v :=
  Finsupp.mapDomain_apply_of_injective (embedding_injective Q n).1 d v

theorem pushDimension_in_image (Q : TypedQuiver) (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    InImage (embedding Q n).vertex (pushDimension Q n d) :=
  (dimensionEquiv (embedding Q n).vertex (embedding_injective Q n).1 d).property

theorem push_pull (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (h : Compatible Q n f F)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    pushDimension Q n (pullDimension f d) = pullDimension F (pushDimension Q n d) := by
  unfold pushDimension
  rw [pullDimension_eq_mapDomain,pullDimension_eq_mapDomain,← Finsupp.mapDomain_comp,← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro v _
  exact ((compatible_symm Q n f F h).1 v).symm

theorem image_pull (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (h : Compatible Q n f F)
    (d : (Q.iterate n).V →₀ ℕ) (hd : InImage (embedding Q n).vertex d) :
    InImage (embedding Q n).vertex (pullDimension F d) := by
  intro v hv
  apply (image_vertex_iff Q n f F h v).mpr
  apply hd
  change F.vertexEquiv v ∈ d.support
  change v ∈ (pullDimension F d).support at hv
  simpa only [Finsupp.mem_support_iff,pullDimension_apply] using hv

theorem descend_pull (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (h : Compatible Q n f F)
    (d : (Q.iterate n).V →₀ ℕ) :
    descend (embedding Q n).vertex (embedding_injective Q n).1 (pullDimension F d) =
      pullDimension f (descend (embedding Q n).vertex (embedding_injective Q n).1 d) := by
  ext v
  rw [descend_apply,pullDimension_apply,pullDimension_apply,descend_apply,h.1]

end KroneckerDirectSumDimensionNaturality
end
end

section

/-! Original-vertex dimensions and all finite King dimension statistics agree
under the direct-sum embedding. Base dimensions are invariant under genuine
finite-character accumulated actions, even when the original vertex set is infinite. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumBaseDimensions
open KroneckerAbelianCover KroneckerDirectSumIteratedEmbedding
open KroneckerDirectSumDimensionNaturality KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerDirectSumAccumulatedActions KroneckerDirectSumDeckRootTorsor
open KroneckerEmbeddedFiniteDimensions KroneckerFiniteSupportStability
attribute [local instance] Classical.decEq Classical.propDecidable

def baseDimension (Q : TypedQuiver) (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) : Q.V →₀ ℕ :=
  d.mapDomain (baseVertex Q n)

theorem baseDimension_push (Q : TypedQuiver) (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    KroneckerAccumulatedDeckBaseDimensions.baseDimension Q n (pushDimension Q n d) = baseDimension Q n d := by
  unfold KroneckerAccumulatedDeckBaseDimensions.baseDimension pushDimension baseDimension
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro v _
  exact embedding_base_vertex Q n v

theorem baseDimension_pull (Q : TypedQuiver) (n : ℕ) (f : Deck Q n)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    baseDimension Q n (pullDimension f.val d) = baseDimension Q n d := by
  unfold baseDimension
  rw [KroneckerAccumulatedDeckBaseDimensions.pullDimension_eq_mapDomain,← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro v _
  exact vertex_base_invariant Q n (inverse f) v



end KroneckerDirectSumBaseDimensions
end
end

section

/-! The direct-sum accumulated dimension relation is EXACTLY the product-model
relation on pushed dimensions. A nonzero target support supplies the one image
root needed for restriction; the zero case is handled separately. Therefore
the direct-sum dimension quotient embeds faithfully in the product quotient. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumDimensionClasses
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerDirectSumAccumulatedActions
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumDeckExtension
open KroneckerDirectSumDimensionNaturality KroneckerDirectSumAccumulatedRestriction
attribute [local instance] Classical.decEq Classical.propDecidable

def Related (Q : TypedQuiver) (n : ℕ)
    (d e : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) : Prop :=
  ∃ f : Deck Q n, pullDimension f.val d = e

def dimensionSetoid (Q : TypedQuiver) (n : ℕ) :
    Setoid ((KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) where
  r := Related Q n
  iseqv := ⟨fun d => ⟨identity Q n,pullDimension_refl _ d⟩,by
    rintro d e ⟨f,rfl⟩
    refine ⟨inverse f,?_⟩
    change pullDimension f.val.symm (pullDimension f.val d) = d
    rw [← pullDimension_trans,quiverIso_symm_trans,pullDimension_refl],by
    rintro d e k ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨compose g f,pullDimension_trans g.val f.val d⟩⟩

abbrev DimensionClass (Q : TypedQuiver) (n : ℕ) := Quotient (dimensionSetoid Q n)

theorem related_iff_product (Q : TypedQuiver) (n : ℕ)
    (d e : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    Related Q n d e ↔ KroneckerAccumulatedDimensionClasses.Related Q n (pushDimension Q n d) (pushDimension Q n e) := by
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨extension f,(push_pull Q n f.val (extension f).val (extension_compatible f) d).symm.trans
      (congrArg (pushDimension Q n) hf)⟩
  · rintro ⟨F,hF⟩
    by_cases he : e = 0
    · subst e
      have hd : d = 0 := by
        ext v
        have h := congrArg (fun δ => δ (F.val.vertexEquiv.symm ((embedding Q n).vertex v))) hF
        rw [pullDimension_apply,Equiv.apply_symm_apply,pushDimension_apply] at h
        simpa only [pushDimension,Finsupp.mapDomain_zero,Finsupp.zero_apply] using h
      subst d
      exact ⟨identity Q n,pullDimension_refl _ 0⟩
    · obtain ⟨v,hv⟩ := Finsupp.support_nonempty_iff.mpr he
      have hpos : pushDimension Q n d (F.val.vertexEquiv ((embedding Q n).vertex v)) ≠ 0 := by
        have h := congrArg (fun δ => δ ((embedding Q n).vertex v)) hF
        rw [pullDimension_apply,pushDimension_apply] at h
        rw [h]
        exact Finsupp.mem_support_iff.mp hv
      obtain ⟨w,hw⟩ := pushDimension_in_image Q n d (Finsupp.mem_support_iff.mpr hpos)
      obtain ⟨f,hf⟩ := exists_restriction Q n F.val F.property v w hw.symm
      refine ⟨f,pushDimension_injective Q n ?_⟩
      rw [push_pull Q n f.val F.val hf,hF]

def productClass (Q : TypedQuiver) (n : ℕ) :
    DimensionClass Q n → KroneckerAccumulatedDimensionClasses.DimensionClass Q n :=
  Quotient.lift (fun d => Quotient.mk (KroneckerAccumulatedDimensionClasses.dimensionSetoid Q n) (pushDimension Q n d))
    (fun d e h => Quotient.sound ((related_iff_product Q n d e).mp h))

theorem productClass_injective (Q : TypedQuiver) (n : ℕ) : Function.Injective (productClass Q n) := by
  intro x y
  induction x using Quotient.inductionOn with | h d =>
    induction y using Quotient.inductionOn with | h e =>
      intro h
      exact Quotient.sound ((related_iff_product Q n d e).mpr (Quotient.exact h))

end KroneckerDirectSumDimensionClasses
end
end

