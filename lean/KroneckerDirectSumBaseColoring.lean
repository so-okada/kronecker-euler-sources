import KroneckerProperBipartiteQuiver
import KroneckerIteratedFiniteSupportArrows

/-! The genuine direct-sum tower of the three-arrow Kronecker quiver carries
an actual proper bipartite coloring by its original arrows. Both source and
target color fibers are injective at every depth, and endpoint sides are
computed by the recursive original-vertex projection. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumBaseColoring
open KroneckerAbelianCover KroneckerDirectSumIteratedEmbedding
open KroneckerProperBipartiteQuiver KroneckerThreeArrowBaseQuiver
attribute [local instance] Classical.decEq Classical.propDecidable

theorem base_source (Q : TypedQuiver) (n : ℕ)
    (a : (KroneckerDirectSumIteratedGirth.iterate Q n).A) :
    baseVertex Q n ((KroneckerDirectSumIteratedGirth.iterate Q n).source a) = Q.source (baseArrow Q n a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih a.1

theorem base_target (Q : TypedQuiver) (n : ℕ)
    (a : (KroneckerDirectSumIteratedGirth.iterate Q n).A) :
    baseVertex Q n ((KroneckerDirectSumIteratedGirth.iterate Q n).target a) = Q.target (baseArrow Q n a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih a.1

theorem direct_base_target_injective (Q : TypedQuiver) (n : ℕ)
    (a b : (KroneckerDirectSumIteratedGirth.iterate Q n).A)
    (hb : baseArrow Q n a = baseArrow Q n b)
    (ht : (KroneckerDirectSumIteratedGirth.iterate Q n).target a =
      (KroneckerDirectSumIteratedGirth.iterate Q n).target b) : a = b := by
  apply (embedding_injective Q n).2
  apply TypedQuiver.baseArrow_target_injective Q n
  · simpa only [embedding_base_arrow] using hb
  · rw [(embedding Q n).target,(embedding Q n).target,ht]

def coloring (n : ℕ) : Coloring (KroneckerDirectSumIteratedGirth.iterate baseQuiver n) where
  side v := (baseVertex baseQuiver n v).val
  side_lt v := (baseVertex baseQuiver n v).isLt
  color := baseArrow baseQuiver n
  source_side a := by rw [base_source]; rfl
  target_side a := by rw [base_target]; rfl
  source_injective := KroneckerIteratedFiniteSupportArrows.direct_base_source_injective baseQuiver n
  target_injective := direct_base_target_injective baseQuiver n

end KroneckerDirectSumBaseColoring

namespace KroneckerBipartiteColorRestriction
open KroneckerAbelianCover KroneckerProperBipartiteQuiver
open KroneckerFiniteSupportInducedQuiver
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver}

def restrictColoring (C : Coloring Q) (d : Q.V →₀ ℕ) : Coloring (supportQuiver Q d) where
  side v := C.side v.val
  side_lt v := C.side_lt v.val
  color a := C.color a.val
  source_side a := C.source_side a.val
  target_side a := C.target_side a.val
  source_injective a b hc hs := Subtype.ext (C.source_injective a.val b.val hc (congrArg Subtype.val hs))
  target_injective a b hc ht := Subtype.ext (C.target_injective a.val b.val hc (congrArg Subtype.val ht))



end KroneckerBipartiteColorRestriction
