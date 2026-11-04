import KroneckerAbstractPairIso
import KroneckerFareyWeightIdentity

section

/-! Any pair representation with source and sink coordinate frames yields an actual canonical-dimension pair. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractPairCoordinates
open Module KroneckerAbstractPairHom KroneckerAbstractPairIso
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
open KroneckerReflectionPairModel KroneckerFiniteQuiverHom
def family {a b : ℕ} (R : Rep m V W) (e : Space a ≃ₗ[ℂ] V) (f : Space b ≃ₗ[ℂ] W) : PairRep m a b :=
 fun i => f.symm.toLinearMap.comp ((R i).comp e.toLinearMap)
def iso {a b : ℕ} (R : Rep m V W) (e : Space a ≃ₗ[ℂ] V) (f : Space b ≃ₗ[ℂ] W) : KroneckerAbstractPairIso.Iso (family R e f) R where
 source := e
 sink := f
 commutes i x := f.apply_symm_apply _
end KroneckerAbstractPairCoordinates
end
end

section

/-! Coordinate-free subobjects of actual two-vertex representations. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractPairSubobject
open KroneckerAbstractPairHom
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
structure Subobject (R : Rep m V W) where
 source : Submodule ℂ V
 sink : Submodule ℂ W
 invariant : ∀ i x,x∈source → R i x∈sink
def bot (R : Rep m V W) : Subobject R := ⟨⊥,⊥,by intro i x hx;have h : x=0 := hx;subst x;simp⟩
def top (R : Rep m V W) : Subobject R := ⟨⊤,⊤,by simp⟩
end KroneckerAbstractPairSubobject
end
end

section

/-! All invariant subobjects satisfy the actual source and sink dimension bounds. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairSubobjectDimensionBounds
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
theorem bounds {R : Rep m V W} (U : Subobject R) :
 finrank ℂ U.source≤finrank ℂ V ∧ finrank ℂ U.sink≤finrank ℂ W :=
 ⟨U.source.finrank_le,U.sink.finrank_le⟩
end KroneckerPairSubobjectDimensionBounds
end
end

section

/- Original module: KroneckerPairSubobjectFull -/
section
/-! Full total subobject dimension is equivalent to both endpoint subspaces being full. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairSubobjectFull
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
theorem criterion {R : Rep m V W} (U : Subobject R) :
 finrank ℂ U.source+finrank ℂ U.sink=finrank ℂ V+finrank ℂ W ↔ U.source=⊤ ∧ U.sink=⊤ := by
 constructor
 · intro h
   have hb := KroneckerPairSubobjectDimensionBounds.bounds U
   exact ⟨Submodule.eq_top_of_finrank_eq (by omega),Submodule.eq_top_of_finrank_eq (by omega)⟩
 · rintro ⟨h,g⟩;rw [h,g];simp
end KroneckerPairSubobjectFull
end
end

/- Original module: KroneckerPairSubobjectZero -/
section
/-! Zero total subobject dimension is equivalent to both endpoint subspaces being zero. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairSubobjectZero
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
theorem criterion {R : Rep m V W} (U : Subobject R) :
 finrank ℂ U.source+finrank ℂ U.sink=0 ↔ U.source=⊥ ∧ U.sink=⊥ := by
 rw [Nat.add_eq_zero_iff,Submodule.finrank_eq_zero,Submodule.finrank_eq_zero]
end KroneckerPairSubobjectZero
end
end

/- Original module: KroneckerAbstractPairStability -/
section
/-! Stability on arbitrary finite-dimensional pair spaces, using every invariant subobject. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractPairStability
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerFareyWeightIdentity
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
def Stable (R : Rep m V W) : Prop := ∀ U : Subobject R,
 0<finrank ℂ U.source+finrank ℂ U.sink →
 finrank ℂ U.source+finrank ℂ U.sink<finrank ℂ V+finrank ℂ W →
 weight (finrank ℂ V) (finrank ℂ W) (finrank ℂ U.source) (finrank ℂ U.sink)<0
theorem coordinate_iff {a b : ℕ} (R : KroneckerReflectionPairModel.PairRep m a b) :
 Stable R ↔ KroneckerReflectionPairModel.PairStable R := by
 simp only [Stable,KroneckerReflectionPairModel.PairStable,KroneckerFiniteQuiverHom.Space,
  Module.finrank_pi,Fintype.card_fin]
 constructor
 · intro h U W hi;exact h ⟨U,W,hi⟩
 · intro h U;exact h U.source U.sink U.invariant
end KroneckerAbstractPairStability
end
end
end

section

/- Original module: KroneckerAbstractSubobjectTransport -/
section
/-! Pair isomorphisms transport all invariant subobjects between arbitrary vector spaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractSubobjectTransport
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractPairIso
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
def transport {R : Rep m V W} {S : Rep m X Y} (e : Iso R S) (U : Subobject R) : Subobject S where
 source := U.source.map e.source.toLinearMap
 sink := U.sink.map e.sink.toLinearMap
 invariant i x hx := by
  obtain ⟨v,hv,rfl⟩ := hx
  exact ⟨R i v,U.invariant i v hv,e.commutes i v⟩
end KroneckerAbstractSubobjectTransport
end
end

/- Original module: KroneckerAbstractSubobjectTransportDimensions -/
section
/-! Transport preserves both dimensions of every invariant subobject. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractSubobjectTransportDimensions
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractPairIso
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
theorem dimensions {R : Rep m V W} {S : Rep m X Y} (e : Iso R S) (U : Subobject R) :
 finrank ℂ (KroneckerAbstractSubobjectTransport.transport e U).source=finrank ℂ U.source ∧
 finrank ℂ (KroneckerAbstractSubobjectTransport.transport e U).sink=finrank ℂ U.sink :=
 ⟨LinearEquiv.finrank_map_eq e.source U.source,LinearEquiv.finrank_map_eq e.sink U.sink⟩
end KroneckerAbstractSubobjectTransportDimensions
end
end

/- Original module: KroneckerAbstractStabilityIso -/
section
/-! Stability is invariant under arbitrary finite-dimensional pair isomorphisms. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractStabilityIso
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractPairIso
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
open KroneckerAbstractPairStability
theorem forward {R : Rep m V W} {S : Rep m X Y} (e : Iso R S) (hs : Stable S) : Stable R := by
 intro U hp hproper
 have h := hs (KroneckerAbstractSubobjectTransport.transport e U)
 have hd := KroneckerAbstractSubobjectTransportDimensions.dimensions e U
 rw [hd.1,hd.2,← e.source.finrank_eq,← e.sink.finrank_eq] at h
 exact h hp hproper
theorem iff {R : Rep m V W} {S : Rep m X Y} (e : Iso R S) : Stable R ↔ Stable S :=
 ⟨forward (symm e),forward e⟩
end KroneckerAbstractStabilityIso
end
end

/- Original module: KroneckerAbstractCoordinatesStable -/
section
/-! Arbitrary coordinate frames preserve stability and realize it in the fixed pair model. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractCoordinatesStable
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractPairIso
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
open KroneckerReflectionPairModel KroneckerFiniteQuiverHom KroneckerAbstractPairCoordinates
theorem stable {a b : ℕ} (R : Rep m V W) (e : Space a ≃ₗ[ℂ] V) (f : Space b ≃ₗ[ℂ] W)
 (h : KroneckerAbstractPairStability.Stable R) : PairStable (family R e f) :=
 (KroneckerAbstractPairStability.coordinate_iff _).mp (KroneckerAbstractStabilityIso.forward (iso R e f) h)
end KroneckerAbstractCoordinatesStable
end
end
end

