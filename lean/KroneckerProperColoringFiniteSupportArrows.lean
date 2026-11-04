import KroneckerDirectSumBaseColoring
import KroneckerFiniteSupportEulerTransport

/-! Proper outgoing color fibers bound the ACTUAL support-arrow set by
three times the number of supported vertices. This gives finite Euler sums
for every finite dimension on any properly three-colored quiver, without
replacing parallel arrows by a simple graph. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerProperColoringFiniteSupportArrows
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerReducedColorWords
open KroneckerFiniteSupportInducedQuiver
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (d : Q.V →₀ ℕ)

def arrowCode (a : SupportArrow Q.source Q.target d) : Color × SupportVertex d :=
  (C.color a.val,⟨Q.source a.val,a.property.1⟩)

theorem arrowCode_injective : Function.Injective (arrowCode C d) := by
  intro a b h
  apply Subtype.ext
  apply C.source_injective
  · exact congrArg Prod.fst h
  · exact congrArg (fun x : Color × SupportVertex d => x.2.val) h

include C in
theorem support_arrows_finite : Finite (SupportArrow Q.source Q.target d) :=
  Finite.of_injective (arrowCode C d) (arrowCode_injective C d)

include C in
theorem support_arrow_card_le : Nat.card (SupportArrow Q.source Q.target d) ≤ 3*d.support.card := by
  have h := Nat.card_le_card_of_injective (arrowCode C d) (arrowCode_injective C d)
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] using h

end KroneckerProperColoringFiniteSupportArrows
