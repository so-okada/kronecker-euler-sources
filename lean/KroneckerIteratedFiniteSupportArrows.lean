import KroneckerDirectSumIteratedEmbedding

/-! The complete induced arrow set of every finite dimension support is finite
at every cover depth, with an explicit original-arrow times support-size bound.
The result holds in both the product and exact direct-sum models. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerIteratedFiniteSupportArrows
open KroneckerAbelianCover KroneckerFiniteSupportInducedQuiver
open KroneckerDirectSumIteratedEmbedding
attribute [local instance] Classical.decEq Classical.propDecidable

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

def arrowCode (Q : TypedQuiver) (n : ℕ) (d : (Q.iterate n).V →₀ ℕ)
    (a : SupportArrow (Q.iterate n).source (Q.iterate n).target d) : Q.A × SupportVertex d :=
  (TypedQuiver.baseArrow Q n a.val,⟨(Q.iterate n).source a.val,a.property.1⟩)

theorem arrowCode_injective (Q : TypedQuiver) (n : ℕ) (d : (Q.iterate n).V →₀ ℕ) :
    Function.Injective (arrowCode Q n d) := by
  intro a b h
  apply Subtype.ext
  apply TypedQuiver.baseArrow_source_injective Q n
  · exact congrArg Prod.fst h
  · exact congrArg (fun z : Q.A × SupportVertex d => z.2.val) h

theorem supportArrow_finite (Q : TypedQuiver) [Finite Q.A] (n : ℕ) (d : (Q.iterate n).V →₀ ℕ) :
    Finite (SupportArrow (Q.iterate n).source (Q.iterate n).target d) :=
  Finite.of_injective (arrowCode Q n d) (arrowCode_injective Q n d)


theorem direct_base_source_injective (Q : TypedQuiver) (n : ℕ)
    (a b : (KroneckerDirectSumIteratedGirth.iterate Q n).A)
    (hb : baseArrow Q n a = baseArrow Q n b)
    (hs : (KroneckerDirectSumIteratedGirth.iterate Q n).source a =
      (KroneckerDirectSumIteratedGirth.iterate Q n).source b) : a = b := by
  apply (embedding_injective Q n).2
  apply TypedQuiver.baseArrow_source_injective Q n
  · simpa only [embedding_base_arrow] using hb
  · rw [(embedding Q n).source,(embedding Q n).source,hs]

def directArrowCode (Q : TypedQuiver) (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ)
    (a : SupportArrow (KroneckerDirectSumIteratedGirth.iterate Q n).source
      (KroneckerDirectSumIteratedGirth.iterate Q n).target d) : Q.A × SupportVertex d :=
  (baseArrow Q n a.val,⟨(KroneckerDirectSumIteratedGirth.iterate Q n).source a.val,a.property.1⟩)

theorem directArrowCode_injective (Q : TypedQuiver) (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    Function.Injective (directArrowCode Q n d) := by
  intro a b h
  apply Subtype.ext
  exact direct_base_source_injective Q n a.val b.val (congrArg Prod.fst h)
    (congrArg (fun z : Q.A × SupportVertex d => z.2.val) h)

theorem directSupportArrow_finite (Q : TypedQuiver) [Finite Q.A] (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    Finite (SupportArrow (KroneckerDirectSumIteratedGirth.iterate Q n).source
      (KroneckerDirectSumIteratedGirth.iterate Q n).target d) :=
  Finite.of_injective (directArrowCode Q n d) (directArrowCode_injective Q n d)

theorem directSupportArrow_card_le (Q : TypedQuiver) [Fintype Q.A] (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    Nat.card (SupportArrow (KroneckerDirectSumIteratedGirth.iterate Q n).source
      (KroneckerDirectSumIteratedGirth.iterate Q n).target d) ≤ Fintype.card Q.A * d.support.card := by
  have h := Nat.card_le_card_of_injective (directArrowCode Q n d) (directArrowCode_injective Q n d)
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe] using h

end KroneckerIteratedFiniteSupportArrows
