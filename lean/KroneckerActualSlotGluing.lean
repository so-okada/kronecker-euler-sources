import KroneckerRetainedVacantSlots
import KroneckerSaturatedBlockData

set_option autoImplicit false
namespace KroneckerActualSlotGluing
open KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport KroneckerProperColoredReflection
open KroneckerRetainedVacantSlots KroneckerGluedProperColoring KroneckerGluedLinearRepresentation
open KroneckerSaturatedBlockData
attribute [local instance] Classical.propDecidable

/-- Attachment data consists of actual vacant vertex-color slots. The two
injectivity conditions are exactly the local conditions for proper gluing. -/
structure SlotAssignment {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (C : ∀ j,ProperColoring (linearSupport (B j))) where
  slot : ∀ i j,R i j → Slot (B j) (C j)
  distinctAtBlock : ∀ j,Function.Injective (fun i : {i // R i j} => slot i.1 j i.2)
  distinctAtConnector : ∀ i,Function.Injective (fun j : {j // R i j} => (slot i j.1 j.2).1.2)

def attachment {I J : Type} {B : J → LinearCoverBlock} {R : I → J → Prop}
    {C : ∀ j,ProperColoring (linearSupport (B j))} (S : SlotAssignment B R C)
    (i : I) (j : J) (h : R i j) : (B j).Sink := (S.slot i j h).1.1

def assignmentColors {I J : Type} {B : J → LinearCoverBlock} {R : I → J → Prop}
    {C : ∀ j,ProperColoring (linearSupport (B j))} (S : SlotAssignment B R C) :
    GluingColors B R (attachment S) C where
  color := fun i j h => (S.slot i j h).1.2
  connectorProper := S.distinctAtConnector
  slotInjective := by intro j u v h; exact S.distinctAtBlock j (Subtype.ext h)
  vacant := by intro i j h s hs he; exact (S.slot i j h).2 ⟨s,hs,he⟩



noncomputable def slotGluedColoring {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop}
    {C : ∀ j,ProperColoring (linearSupport (B j))} (S : SlotAssignment B R C) :
    ProperColoring (linearSupport (gluedBlock B R (attachment S))) :=
  gluedLinearColoring B R (attachment S) C (assignmentColors S)

end KroneckerActualSlotGluing
