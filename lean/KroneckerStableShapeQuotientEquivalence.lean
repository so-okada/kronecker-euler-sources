import Mathlib.Data.Quot
import KroneckerStableColoredRepresentatives

/- Original module: KroneckerTwoSidedQuotientBridge -/
section
/-! A total cross-relation with uniqueness modulo each side's equivalence
relation induces a genuine quotient equivalence. Both inverse laws and its
value on every related pair are proved, so later realization choices cannot
silently alter the induced class map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTwoSidedQuotientBridge
variable {A B : Type} (sa : Setoid A) (sb : Setoid B)

structure Bridge where
  rel : A → B → Prop
  left_total : ∀ a, ∃ b, rel a b
  right_total : ∀ b, ∃ a, rel a b
  left_unique : ∀ {a a' b b'}, rel a b → rel a' b' → sb b b' → sa a a'
  right_unique : ∀ {a a' b b'}, rel a b → rel a' b' → sa a a' → sb b b'

variable {sa sb} (J : Bridge sa sb)

def forwardChoice (a : A) : B := Classical.choose (J.left_total a)
def reverseChoice (b : B) : A := Classical.choose (J.right_total b)

theorem forward_related (a : A) : J.rel a (forwardChoice J a) := Classical.choose_spec (J.left_total a)
theorem reverse_related (b : B) : J.rel (reverseChoice J b) b := Classical.choose_spec (J.right_total b)

def forward : Quotient sa → Quotient sb :=
  Quotient.lift (fun a => Quotient.mk sb (forwardChoice J a))
    (fun _ _ h => Quotient.sound (J.right_unique (forward_related J _) (forward_related J _) h))

def reverse : Quotient sb → Quotient sa :=
  Quotient.lift (fun b => Quotient.mk sa (reverseChoice J b))
    (fun _ _ h => Quotient.sound (J.left_unique (reverse_related J _) (reverse_related J _) h))

theorem reverse_forward (x : Quotient sa) : reverse J (forward J x) = x := by
  induction x using Quotient.inductionOn with | h a =>
    exact Quotient.sound (J.left_unique (reverse_related J _) (forward_related J a) (sb.refl _))

theorem forward_reverse (y : Quotient sb) : forward J (reverse J y) = y := by
  induction y using Quotient.inductionOn with | h b =>
    exact Quotient.sound (J.right_unique (forward_related J _) (reverse_related J b) (sa.refl _))

def quotientEquiv : Quotient sa ≃ Quotient sb :=
  ⟨forward J,reverse J,reverse_forward J,forward_reverse J⟩

theorem quotientEquiv_related {a : A} {b : B} (h : J.rel a b) :
    quotientEquiv J (Quotient.mk sa a) = Quotient.mk sb b :=
  Quotient.sound (J.right_unique (forward_related J a) h (sa.refl a))

end KroneckerTwoSidedQuotientBridge
end
end

/- Original module: KroneckerStableShapeQuotientEquivalence -/
section
/-! The two stable realization constructions induce a genuine bijection of
stable DIMENSION quotients. Weighted colored support composition proves
choice independence and reflection in both directions; the abstract bridge
supplies explicit inverse laws, not merely mutual existence of realizations. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableShapeQuotientEquivalence
open KroneckerWeightedColoredSupportIso KroneckerStableColoredRepresentatives
open KroneckerDirectSumUniversalSupportEmbedding KroneckerTwoSidedQuotientBridge
attribute [local instance] Classical.decEq Classical.propDecidable

def ShapeRelated (B : ℕ) (θ : Fin 2 → ℤ) (S : DirectStable B θ) (T : WordStable B θ) : Prop :=
  Nonempty (ColoredIso (KroneckerDirectSumBaseColoring.coloring (depth B))
    KroneckerUniversalWordBaseProjection.coloring S.val.1 T.val.1)

def stableBridge (B : ℕ) (θ : Fin 2 → ℤ) : Bridge (directSetoid B θ) (wordSetoid B θ) where
  rel := ShapeRelated B θ
  left_total S := by
    obtain ⟨T,hn,hB,hs,hj⟩ := KroneckerUniversalColoredRealization.exists_colored_realization B S.val
      S.property.1 S.property.2.1 θ S.property.2.2
    exact ⟨⟨T,hn,hB,hs⟩,hj⟩
  right_total T := by
    obtain ⟨S,hn,hB,hs,⟨j⟩⟩ := KroneckerDirectColoredRealization.exists_colored_realization B T.val
      T.property.1 T.property.2.1 θ T.property.2.2
    exact ⟨⟨S,hn,hB,hs⟩,⟨j.symm⟩⟩
  left_unique := by
    intro S S' T T' h h' he
    obtain ⟨j⟩ := h
    obtain ⟨j'⟩ := h'
    obtain ⟨k⟩ := (word_related_iff_colored B θ T T').mp he
    exact (direct_related_iff_colored B θ S S').mpr ⟨(j.trans k).trans j'.symm⟩
  right_unique := by
    intro S S' T T' h h' he
    obtain ⟨j⟩ := h
    obtain ⟨j'⟩ := h'
    obtain ⟨k⟩ := (direct_related_iff_colored B θ S S').mp he
    exact (word_related_iff_colored B θ T T').mpr ⟨(j.symm.trans k).trans j'⟩

def stableDimensionQuotientEquiv (B : ℕ) (θ : Fin 2 → ℤ) :
    Quotient (directSetoid B θ) ≃ Quotient (wordSetoid B θ) := quotientEquiv (stableBridge B θ)

theorem equiv_on_any_realization (B : ℕ) (θ : Fin 2 → ℤ) {S : DirectStable B θ} {T : WordStable B θ}
    (h : ShapeRelated B θ S T) :
    stableDimensionQuotientEquiv B θ (Quotient.mk (directSetoid B θ) S) = Quotient.mk (wordSetoid B θ) T :=
  quotientEquiv_related (stableBridge B θ) h


end KroneckerStableShapeQuotientEquivalence
end
end
