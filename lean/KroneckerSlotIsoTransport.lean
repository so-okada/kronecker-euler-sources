import KroneckerColoredIncidenceIso

set_option autoImplicit false
namespace KroneckerSlotIsoTransport
open KroneckerLinearCoverBlocks KroneckerProperColoredReflection KroneckerRetainedBlockSupport
open KroneckerRetainedVacantSlots KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

variable {B B' : LinearCoverBlock} {C : ProperColoring (linearSupport B)}
  {C' : ProperColoring (linearSupport B')}

theorem vacant_transport (e : ColoredIso C C') (i : B.Sink) (d : Fin 3) :
    VacantSlot B' C' (e.sink i) d ↔ VacantSlot B C i d := by
  constructor
  · intro hv
    rintro ⟨s,h,hd⟩
    exact hv ⟨e.source s,(e.incidence s i).mpr h,(e.color s i h).trans hd⟩
  · intro hv
    rintro ⟨s',h',hd⟩
    obtain ⟨s,rfl⟩ := e.source.surjective s'
    have h := (e.incidence s i).mp h'
    exact hv ⟨s,h,(e.color s i h).symm.trans hd⟩

def slotEquiv (e : ColoredIso C C') : Slot B C ≃ Slot B' C' where
  toFun p := ⟨(e.sink p.1.1,p.1.2),(vacant_transport e _ _).mpr p.2⟩
  invFun q := ⟨(e.sink.symm q.1.1,q.1.2),by
    apply (vacant_transport e _ _).mp
    simpa using q.2⟩
  left_inv := by intro p; apply Subtype.ext; simp
  right_inv := by intro q; apply Subtype.ext; simp





end KroneckerSlotIsoTransport
