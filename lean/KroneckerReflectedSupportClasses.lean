import KroneckerReflectionFaithfulness
import KroneckerSaturatedBlockData

set_option autoImplicit false
namespace KroneckerReflectedSupportClasses
open KroneckerLinearCoverBlocks KroneckerProperColoredReflection KroneckerRetainedBlockSupport
open KroneckerColoredIncidenceIso KroneckerSaturatedBlockData KroneckerReflectionFaithfulness
open KroneckerSaturatedTreeDimensions KroneckerRetainedIsoTransport
attribute [local instance] Classical.propDecidable

def identityIso {I J : Type} {R : I → J → Prop} (C : ProperColoring R) : ColoredIso C C where
  source := Equiv.refl I
  sink := Equiv.refl J
  incidence := fun _ _ => Iff.rfl
  color := fun _ _ _ => rfl

structure ColoredBlock where
  block : LinearCoverBlock
  coloring : ProperColoring (linearSupport block)

def originalSetoid : Setoid SaturatedBlockData where
  r T U := Nonempty (ColoredIso T.coloring U.coloring)
  iseqv := ⟨fun T => ⟨identityIso T.coloring⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

def supportSetoid : Setoid ColoredBlock where
  r B D := Nonempty (ColoredIso B.coloring D.coloring)
  iseqv := ⟨fun B => ⟨identityIso B.coloring⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

theorem original_degrees_positive (T : SaturatedBlockData) (j : Fin T.sinks) :
    0<Fintype.card {i // T.incidence i j} := by
  have hn := T.sources_ge_two
  let : Nonempty (Fin T.sources) := ⟨⟨0,by omega⟩⟩
  let : Nonempty (Fin T.sinks) := ⟨j⟩
  exact saturated_sink_degree_positive T.incidence T.tree j

noncomputable def reflectedColoredBlock (T : SaturatedBlockData) : ColoredBlock :=
  ⟨supportedBlock T,supportedColoring T⟩

noncomputable def reflectionOnClasses : Quotient originalSetoid → Quotient supportSetoid :=
  Quotient.map reflectedColoredBlock (by rintro T U ⟨e⟩; exact ⟨retainedIso e⟩)



end KroneckerReflectedSupportClasses
