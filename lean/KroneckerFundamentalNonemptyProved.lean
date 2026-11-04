import KroneckerPairExtensionDimensions
import KroneckerProductTransverseGraph
import KroneckerProductSubspaceExtreme
import KroneckerFareySubobjectLeftCases
import KroneckerFareySubobjectRightCases
import KroneckerOneSourceCoordinateStable
import KroneckerNegativeTitsSymmetry

/- Original module: KroneckerCentralStripNonsplit -/
section
/-! Every pair of representations with ordered positive central-strip dimensions admits an actual nonsplit extension. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCentralStripNonsplit
open KroneckerReflectionPairModel KroneckerFiniteQuiverHom KroneckerPairExtensionSplit
theorem exists_extension {m a b c d : ℕ} (R : PairRep m a b) (S : PairRep m c d)
 (hm : 3≤m) (ha : 0<a) (hc : 0<c) (hab : a≤b) (hcd : c≤d)
 (hbd : b*c≤d*a) (hupper : d≤(m-1)*c) :
 ∃ z : Fin m → Space a →ₗ[ℂ] Space d,¬Split R S z :=
 KroneckerPairExtensionDimensions.exists_nonsplit R S
  (KroneckerCentralStripIntegerEuler.surplus m a b c d hm ha hc hab hcd hbd hupper)
end KroneckerCentralStripNonsplit
end
end

/- Original module: KroneckerExtensionCoordinateFrames -/
section
/-! Product endpoint spaces have coordinate frames in the sum dimensions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExtensionCoordinateFrames
open Module KroneckerFiniteQuiverHom
def frame (a c : ℕ) : Space (a+c) ≃ₗ[ℂ] (Space c×Space a) :=
 (Module.finBasisOfFinrankEq ℂ (Space c×Space a) (by simp [Space,Module.finrank_prod,add_comm] : finrank ℂ (Space c×Space a)=a+c)).equivFun.symm
end KroneckerExtensionCoordinateFrames
end
end

/- Original module: KroneckerExtensionSubobjectIntersection -/
section
/-! An arbitrary extension subobject intersects the upper endpoint in an invariant subobject. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExtensionSubobjectIntersection
open KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractExtensionPair KroneckerProductSubspaceParts
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
def intersection (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y)
 (U : Subobject (extension R S z)) : Subobject S where
 source := leftPart U.source
 sink := leftPart U.sink
 invariant i x hx := by
  have h := U.invariant i (x,0) hx
  simpa [extension,KroneckerTriangularLinearAlgebra.triangular,leftPart] using h
end KroneckerExtensionSubobjectIntersection
end
end

/- Original module: KroneckerExtensionSubobjectImage -/
section
/-! An arbitrary extension subobject projects to an invariant subobject of the lower endpoint. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExtensionSubobjectImage
open KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractExtensionPair KroneckerProductSubspaceParts
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
def image (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y)
 (U : Subobject (extension R S z)) : Subobject R where
 source := rightPart U.source
 sink := rightPart U.sink
 invariant i v hv := by
  obtain ⟨x,hx⟩ := (mem_right U.source v).mp hv
  apply (mem_right U.sink (R i v)).mpr
  exact ⟨S i x+z i v,U.invariant i (x,v) hx⟩
end KroneckerExtensionSubobjectImage
end
end

/- Original module: KroneckerExtensionTransverseSplits -/
section
/-! The exceptional subobject forces an actual extension splitting, ruling out the only destabilizing case. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExtensionTransverseSplits
open KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractExtensionPair KroneckerProductSubspaceParts
open KroneckerProductTransverseGraph KroneckerPairExtensionSplit
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
theorem split (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y)
 (U : Subobject (extension R S z)) (hs : leftPart U.source=⊥) (ht : leftPart U.sink=⊥)
 (hps : rightPart U.source=⊤) (hpt : rightPart U.sink=⊤) : Split R S z := by
 refine ⟨graphMap U.source hs hps,graphMap U.sink ht hpt,?_⟩
 intro i v
 have h := U.invariant i _ (graph_mem U.source hs hps v)
 exact (unique U.sink ht hpt _ _ h).symm
end KroneckerExtensionTransverseSplits
end
end

/- Original module: KroneckerExtensionNonsplitObstruction -/
section
/-! A nonsplit extension excludes every invariant complement, on both vertices simultaneously. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExtensionNonsplitObstruction
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractExtensionPair KroneckerProductSubspaceParts
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
theorem excludes (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y)
 (hn : ¬KroneckerPairExtensionSplit.Split R S z) (U : Subobject (extension R S z)) :
 ¬(leftPart U.source=⊥ ∧ leftPart U.sink=⊥ ∧ rightPart U.source=⊤ ∧ rightPart U.sink=⊤) := by
 rintro ⟨h,g,k,l⟩
 exact hn (KroneckerExtensionTransverseSplits.split R S z U h g k l)
end KroneckerExtensionNonsplitObstruction
end
end

/- Original module: KroneckerExtensionSubobjectDimensions -/
section
/-! Source and sink dimensions of arbitrary invariant extension subobjects split additively. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExtensionSubobjectDimensions
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractExtensionPair KroneckerProductSubspaceParts
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
theorem dimensions (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y)
 (U : Subobject (extension R S z)) :
 finrank ℂ U.source=finrank ℂ (leftPart U.source)+finrank ℂ (rightPart U.source) ∧
 finrank ℂ U.sink=finrank ℂ (leftPart U.sink)+finrank ℂ (rightPart U.sink) :=
 ⟨KroneckerProductSubspaceDimension.dimension U.source,KroneckerProductSubspaceDimension.dimension U.sink⟩
end KroneckerExtensionSubobjectDimensions
end
end

/- Original module: KroneckerExtensionSubobjectFullDetection -/
section
/-! Both full endpoint parts force the entire invariant extension subobject to be full. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExtensionSubobjectFullDetection
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractExtensionPair KroneckerProductSubspaceParts
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
theorem full (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y)
 (U : Subobject (extension R S z))
 (hls : leftPart U.source=⊤) (hlt : leftPart U.sink=⊤)
 (hrs : rightPart U.source=⊤) (hrt : rightPart U.sink=⊤) :
 U.source=⊤ ∧ U.sink=⊤ :=
 ⟨KroneckerProductSubspaceExtreme.top U.source hls hrs,KroneckerProductSubspaceExtreme.top U.sink hlt hrt⟩
end KroneckerExtensionSubobjectFullDetection
end
end

/- Original module: KroneckerFareyWeightAdditivity -/
section
/-! Character is additive under the intersection-image dimension decomposition of extensions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyWeightAdditivity
open KroneckerFareyWeightIdentity
theorem additive (a b u v w z : ℤ) : weight a b (u+v) (w+z)=weight a b u w+weight a b v z := by
 dsimp [weight];ring
theorem zero (a b : ℤ) : weight a b 0 0=0 := by simp [weight]
end KroneckerFareyWeightAdditivity
end
end

/- Original module: KroneckerExtensionSubobjectWeight -/
section
/-! The total character of an arbitrary extension subobject is the sum of its endpoint-part characters. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExtensionSubobjectWeight
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractExtensionPair KroneckerProductSubspaceParts
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
open KroneckerFareyWeightIdentity
theorem weight_add (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y)
 (U : Subobject (extension R S z)) (a b : ℤ) :
 weight a b (finrank ℂ U.source) (finrank ℂ U.sink)=
 weight a b (finrank ℂ (leftPart U.source)) (finrank ℂ (leftPart U.sink))+
 weight a b (finrank ℂ (rightPart U.source)) (finrank ℂ (rightPart U.sink)) := by
 rw [(KroneckerExtensionSubobjectDimensions.dimensions R S z U).1,
  (KroneckerExtensionSubobjectDimensions.dimensions R S z U).2,Nat.cast_add,Nat.cast_add]
 exact KroneckerFareyWeightAdditivity.additive _ _ _ _ _ _
end KroneckerExtensionSubobjectWeight
end
end

/- Original module: KroneckerExtensionSubobjectZeroDetection -/
section
/-! Both zero endpoint parts force the entire invariant extension subobject to vanish. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExtensionSubobjectZeroDetection
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractExtensionPair KroneckerProductSubspaceParts
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
theorem zero (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y)
 (U : Subobject (extension R S z))
 (hls : leftPart U.source=⊥) (hlt : leftPart U.sink=⊥)
 (hrs : rightPart U.source=⊥) (hrt : rightPart U.sink=⊥) :
 U.source=⊥ ∧ U.sink=⊥ :=
 ⟨KroneckerProductSubspaceExtreme.bot U.source hls hrs,KroneckerProductSubspaceExtreme.bot U.sink hlt hrt⟩
end KroneckerExtensionSubobjectZeroDetection
end
end

/- Original module: KroneckerFareyNonsplitStable -/
section
/-! Every nonsplit extension of stable determinant-one endpoints is stable for the total dimension character. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyNonsplitStable
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractExtensionPair KroneckerProductSubspaceParts
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
open KroneckerAbstractPairStability KroneckerFareyWeightIdentity
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem stable (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y)
 (hR : Stable R) (hS : Stable S) (ha : 0<finrank ℂ V) (hc : 0<finrank ℂ X)
 (hdet : (finrank ℂ V:ℤ)*finrank ℂ Y-(finrank ℂ X:ℤ)*finrank ℂ W=1)
 (hn : ¬KroneckerPairExtensionSplit.Split R S z) : Stable (extension R S z) := by
 intro U hpos hproper
 let I := KroneckerExtensionSubobjectIntersection.intersection R S z U
 let P := KroneckerExtensionSubobjectImage.image R S z U
 have hL := KroneckerFareySubobjectLeftCases.cases hR P (finrank ℂ X) (finrank ℂ Y) ha hc hdet
 have hH := KroneckerFareySubobjectRightCases.cases hS I (finrank ℂ V) (finrank ℂ W) ha hc hdet
 have hw := KroneckerExtensionSubobjectWeight.weight_add R S z U
  ((finrank ℂ V:ℤ)+finrank ℂ X) ((finrank ℂ W:ℤ)+finrank ℂ Y)
 dsimp [P,KroneckerExtensionSubobjectImage.image] at hL
 dsimp [I,KroneckerExtensionSubobjectIntersection.intersection] at hH
 rw [Module.finrank_prod,Module.finrank_prod,Nat.cast_add,Nat.cast_add]
 rw [add_comm (finrank ℂ X:ℤ),add_comm (finrank ℂ Y:ℤ),hw]
 rcases hL with ⟨hL,hLs,hLt⟩|hL|⟨hL,hLs,hLt⟩ <;>
  rcases hH with ⟨hH,hHs,hHt⟩|hH|⟨hH,hHs,hHt⟩
 · have hzero := KroneckerExtensionSubobjectZeroDetection.zero R S z U hHs hHt hLs hLt
   rw [hzero.1,hzero.2] at hpos;simp at hpos
 · omega
 · omega
 · omega
 · omega
 · omega
 · exact False.elim (hn (KroneckerExtensionTransverseSplits.split R S z U hHs hHt hLs hLt))
 · omega
 · have hfull := KroneckerExtensionSubobjectFullDetection.full R S z U hHs hHt hLs hLt
   rw [hfull.1,hfull.2] at hproper;simp at hproper
end KroneckerFareyNonsplitStable
end
end

/- Original module: KroneckerFareyStableCoordinateExtension -/
section
/-! A nonsplit determinant-one extension gives an actual stable coordinate representation at the sum dimension. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyStableCoordinateExtension
open KroneckerReflectionPairModel KroneckerFiniteQuiverHom KroneckerPairExtensionSplit
open KroneckerAbstractExtensionPair KroneckerAbstractPairCoordinates
theorem exists_stable {m a b c d : ℕ} (R : PairRep m a b) (S : PairRep m c d)
 (hR : PairStable R) (hS : PairStable S) (ha : 0<a) (hc : 0<c)
 (hd : (a:ℤ)*d-(c:ℤ)*b=1) (z : Fin m → Space a →ₗ[ℂ] Space d) (hn : ¬Split R S z) :
 ∃ E : PairRep m (a+c) (b+d),PairStable E := by
 have hs := KroneckerFareyNonsplitStable.stable R S z
  ((KroneckerAbstractPairStability.coordinate_iff R).mpr hR)
  ((KroneckerAbstractPairStability.coordinate_iff S).mpr hS)
  (by simpa [Space] using ha) (by simpa [Space] using hc) (by simpa [Space] using hd) hn
 exact ⟨family (extension R S z) (KroneckerExtensionCoordinateFrames.frame a c)
  (KroneckerExtensionCoordinateFrames.frame b d),KroneckerAbstractCoordinatesStable.stable _ _ _ hs⟩
end KroneckerFareyStableCoordinateExtension
end
end

/- Original module: KroneckerCentralFareyStableSum -/
section
/-! Stable determinant-one central-strip parents always produce a stable sum representation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCentralFareyStableSum
open KroneckerReflectionPairModel
theorem exists_stable {m a b c d : ℕ} (R : PairRep m a b) (S : PairRep m c d)
 (hR : PairStable R) (hS : PairStable S) (hm : 3≤m) (ha : 0<a) (hc : 0<c)
 (hab : a≤b) (hcd : c≤d) (hup : d≤(m-1)*c) (hd : (a:ℤ)*d-(c:ℤ)*b=1) :
 ∃ E : PairRep m (a+c) (b+d),PairStable E := by
 have ho : b*c≤d*a := by
  have : (b:ℤ)*c≤d*a := by nlinarith
  exact_mod_cast this
 obtain ⟨z,hz⟩ := KroneckerCentralStripNonsplit.exists_extension R S hm ha hc hab hcd ho hup
 exact KroneckerFareyStableCoordinateExtension.exists_stable R S hR hS ha hc hd z hz
end KroneckerCentralFareyStableSum
end
end

/- Original module: KroneckerFareyBoundedInverse -/
section
/-! Every nonintegral primitive slope has a modular inverse strictly between zero and its denominator. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyBoundedInverse
theorem exists_inverse (a b : ℕ) (ha : 1<a) (h : Nat.Coprime a b) :
 ∃ x : ℕ,0<x ∧ x<a ∧ b*x%a=1 := by
 obtain ⟨x,_,hx⟩ := Nat.exists_mul_mod_eq_one_of_coprime h.symm ha
 refine ⟨x%a,?_,Nat.mod_lt _ (by omega),?_⟩
 · by_contra hn
   have hz : x%a=0 := by omega
   have he : b*x%a=0 := by rw [Nat.mul_mod,hz];simp
   omega
 · simpa only [Nat.mul_mod,Nat.mod_mod] using hx
end KroneckerFareyBoundedInverse
end
end

/- Original module: KroneckerFareyDivisionParents -/
section
/-! Euclidean division produces the exact determinant-one lower-parent equation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyDivisionParents
theorem division (a b x : ℕ) (h : b*x%a=1) : (x:ℤ)*b-(a:ℤ)*(b*x/a)=1 := by
 have hh := Nat.mod_add_div (b*x) a
 rw [h] at hh
 have hr : (1:ℤ)+(a:ℤ)*(b*x/a)=(b:ℤ)*x := by exact_mod_cast hh
 nlinarith
end KroneckerFareyDivisionParents
end
end

/- Original module: KroneckerFareyParentSinkBounds -/
section
/-! The Euclidean lower-parent sink dimension lies strictly below the target sink dimension. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyParentSinkBounds
theorem bounds (a b x u : ℕ) (ha : 0<a) (hb : 0<b) (hx : x<a)
 (h : (x:ℤ)*b-(a:ℤ)*u=1) : u<b := by
 have hxb : (x:ℤ)*(b:ℤ)<a*b := mul_lt_mul_of_pos_right (by exact_mod_cast hx) (by exact_mod_cast hb)
 have haI : (0:ℤ)<a := by exact_mod_cast ha
 by_contra hn
 have hu : (b:ℤ)≤u := by exact_mod_cast (show b≤u by omega)
 have hp := mul_le_mul_of_nonneg_left hu (le_of_lt haI)
 nlinarith
end KroneckerFareyParentSinkBounds
end
end

/- Original module: KroneckerFareyParentDeterminant -/
section
/-! Subtracting a Euclidean parent from the target gives a positive-source determinant-one pair. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyParentDeterminant
theorem determinant (a b x u : ℕ) (hx : x≤a) (hu : u≤b)
 (h : (x:ℤ)*b-(a:ℤ)*u=1) : (x:ℤ)*(b-u:ℕ)-(a-x:ℕ)*(u:ℤ)=1 := by
 rw [Nat.cast_sub hu,Nat.cast_sub hx];nlinarith
end KroneckerFareyParentDeterminant
end
end

/- Original module: KroneckerFareyParentLowerStrip -/
section
/-! Integer lower slope bounds descend from a primitive mediant to its Euclidean lower parent. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyParentLowerStrip
theorem lower (a b x u k : ℕ) (ha : 1<a) (h : (x:ℤ)*b-(a:ℤ)*u=1)
 (hl : k*a≤b) : k*x≤u := by
 have hlI : (k:ℤ)*a≤b := by exact_mod_cast hl
 have hp := mul_le_mul_of_nonneg_left hlI (Int.natCast_nonneg x)
 have haI : (1:ℤ)<a := by exact_mod_cast ha
 by_contra hn
 have hu : (u:ℤ)+1≤k*x := by exact_mod_cast (show u+1≤k*x by omega)
 have hh := mul_le_mul_of_nonneg_left hu (show (0:ℤ)≤a by positivity)
 nlinarith
end KroneckerFareyParentLowerStrip
end
end

/- Original module: KroneckerFareyParentUpperStrip -/
section
/-! Integer upper slope bounds descend from a primitive mediant to its complementary upper parent. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyParentUpperStrip
theorem upper (a b x u k : ℕ) (ha : 1<a) (hx : x≤a) (hu : u≤b)
 (h : (x:ℤ)*b-(a:ℤ)*u=1) (hl : b≤k*a) : b-u≤k*(a-x) := by
 have hlI : (b:ℤ)≤k*a := by exact_mod_cast hl
 have hp := mul_le_mul_of_nonneg_left hlI (show (0:ℤ)≤(a:ℤ)-x by exact sub_nonneg.mpr (by exact_mod_cast hx))
 have haI : (1:ℤ)<a := by exact_mod_cast ha
 by_contra hn
 have hhN : k*(a-x)+1≤b-u := by omega
 have hh : (k:ℤ)*((a:ℤ)-x)+1≤(b:ℤ)-u := by
  have := (show ((k*(a-x)+1:ℕ):ℤ)≤(b-u:ℕ) by exact_mod_cast hhN)
  push_cast at this
  simpa only [Nat.cast_sub hx,Nat.cast_sub hu] using this
 have hmul := mul_le_mul_of_nonneg_left hh (show (0:ℤ)≤a by positivity)
 nlinarith
end KroneckerFareyParentUpperStrip
end
end

/- Original module: KroneckerFareyParentStripInheritance -/
section
/-! Both determinant-one parents of a nonintegral primitive target stay within every integer slope strip containing the target. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyParentStripInheritance
theorem strip (a b c d l k : ℕ) (ha : 0<a) (hc : 0<c)
 (hd : (a:ℤ)*d-(c:ℤ)*b=1) (hl : l*(a+c)≤b+d) (hu : b+d≤k*(a+c)) :
 l*a≤b ∧ b≤k*a ∧ l*c≤d ∧ d≤k*c := by
 have htotal : (a:ℤ)*(b+d)-(a+c:ℕ)*(b:ℤ)=1 := by push_cast;nlinarith
 have hlow := KroneckerFareyParentLowerStrip.lower (a+c) (b+d) a b l (by omega) htotal hl
 have hupp := KroneckerFareyParentUpperStrip.upper (a+c) (b+d) a b k (by omega) (by omega) (by omega) htotal hu
 simp only [Nat.add_sub_cancel_left] at hupp
 have hdI : (a:ℤ)*d=(c:ℤ)*b+1 := by omega
 have haI : (0:ℤ)<a := by exact_mod_cast ha
 have hcI : (0:ℤ)<c := by exact_mod_cast hc
 have hloI : (l:ℤ)*a≤b := by exact_mod_cast hlow
 have hupI : (d:ℤ)≤k*c := by exact_mod_cast hupp
 have hp := mul_le_mul_of_nonneg_left hloI (le_of_lt hcI)
 have hq := mul_le_mul_of_nonneg_left hupI (le_of_lt haI)
 refine ⟨hlow,?_,?_,hupp⟩
 · by_contra hn
   have hnI : (k:ℤ)*a<b := by exact_mod_cast (show k*a<b by omega)
   have hh := mul_lt_mul_of_pos_left hnI hcI
   nlinarith
 · by_contra hn
   have hnI : (d:ℤ)<l*c := by exact_mod_cast (show d<l*c by omega)
   have hh := mul_lt_mul_of_pos_left hnI haI
   nlinarith
end KroneckerFareyParentStripInheritance
end
end

/- Original module: KroneckerFareyPositiveParents -/
section
/-! Positive central-strip targets yield positive lower-parent dimensions and a positive complementary source. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyPositiveParents
theorem positive (a b x u : ℕ) (ha : 1<a) (hx : 0<x) (hxa : x<a)
 (h : (x:ℤ)*b-(a:ℤ)*u=1) (hl : a≤b) : 0<u ∧ 0<a-x := by
 have hu := KroneckerFareyParentLowerStrip.lower a b x u 1 ha h (by simpa using hl)
 simp only [one_mul] at hu
 omega
end KroneckerFareyPositiveParents
end
end

/- Original module: KroneckerFareyParentsExist -/
section
/-! Every positive primitive nonintegral target admits smaller positive determinant-one parents with exact dimension sum. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyParentsExist
theorem parents (a b : ℕ) (ha : 1<a) (hb : a≤b) (hc : Nat.Coprime a b) :
 ∃ x u y v : ℕ,0<x ∧ 0<u ∧ 0<y ∧ 0<v ∧ x<a ∧ y<a ∧ x+y=a ∧ u+v=b ∧
 (x:ℤ)*v-(y:ℤ)*u=1 := by
 obtain ⟨x,hx,hxa,hi⟩ := KroneckerFareyBoundedInverse.exists_inverse a b ha hc
 let u := b*x/a
 have hd := KroneckerFareyDivisionParents.division a b x hi
 have hu := KroneckerFareyParentSinkBounds.bounds a b x u (by omega) (by omega) hxa hd
 have hpos := KroneckerFareyPositiveParents.positive a b x u ha hx hxa hd hb
 refine ⟨x,u,a-x,b-u,hx,hpos.1,hpos.2,by omega,hxa,by omega,by omega,by omega,?_⟩
 exact KroneckerFareyParentDeterminant.determinant a b x u (by omega) (by omega) hd
end KroneckerFareyParentsExist
end
end

/- Original module: KroneckerFareyPrimitiveEndpoints -/
section
/-! Determinant-one parents are primitive at both endpoints. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyPrimitiveEndpoints
theorem primitive (a b c d : ℕ) (h : (a:ℤ)*d-c*b=1) : Nat.Coprime a b ∧ Nat.Coprime c d := by
 constructor
 · apply Nat.isCoprime_iff_coprime.mp;refine ⟨(d:ℤ),-(c:ℤ),?_⟩;nlinarith
 · apply Nat.isCoprime_iff_coprime.mp;refine ⟨-(b:ℤ),(a:ℤ),?_⟩;nlinarith
end KroneckerFareyPrimitiveEndpoints
end
end

/- Original module: KroneckerCentralStripFareyParents -/
section
/-! Every primitive central-strip target above source height one has smaller primitive parents in the same strip. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCentralStripFareyParents
theorem parents (m a b : ℕ) (ha : 1<a) (hl : a≤b) (hu : b≤(m-1)*a) (hp : Nat.Coprime a b) :
 ∃ x u y v : ℕ,0<x ∧ 0<y ∧ x<a ∧ y<a ∧ x+y=a ∧ u+v=b ∧
 x≤u ∧ u≤(m-1)*x ∧ y≤v ∧ v≤(m-1)*y ∧
 Nat.Coprime x u ∧ Nat.Coprime y v ∧ (x:ℤ)*v-(y:ℤ)*u=1 := by
 obtain ⟨x,u,y,v,hx,_,hy,_,hxa,hya,he,hf,hd⟩ := KroneckerFareyParentsExist.parents a b ha hl hp
 have hs := KroneckerFareyParentStripInheritance.strip x u y v 1 (m-1) hx hy hd
  (by simpa [he,hf] using hl) (by simpa [he,hf] using hu)
 simp only [one_mul] at hs
 have hc := KroneckerFareyPrimitiveEndpoints.primitive x u y v hd
 exact ⟨x,u,y,v,hx,hy,hxa,hya,he,hf,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hc.1,hc.2,hd⟩
end KroneckerCentralStripFareyParents
end
end

/- Original module: KroneckerCentralStripStableInduction -/
section
/-! Strong induction constructs stable representations for every primitive dimension in the central strip. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCentralStripStableInduction
open KroneckerReflectionPairModel
theorem exists_stable (m : ℕ) (hm : 3≤m) (a b : ℕ) (ha : 0<a) (hl : a≤b)
 (hu : b≤(m-1)*a) (hp : Nat.Coprime a b) : ∃ R : PairRep m a b,PairStable R := by
 induction a using Nat.strong_induction_on generalizing b with
 | h a ih =>
  by_cases h1 : a=1
  · subst a
    exact KroneckerOneSourceCoordinateStable.exists_stable m b (by omega)
  obtain ⟨x,u,y,v,hx,hy,hxa,hya,he,hf,hxu,hux,hyv,hvy,hcp,hcq,hd⟩ :=
   KroneckerCentralStripFareyParents.parents m a b (by omega) hl hu hp
  obtain ⟨R,hR⟩ := ih x hxa u hx hxu hux hcp
  obtain ⟨S,hS⟩ := ih y hya v hy hyv hvy hcq
  have hE := KroneckerCentralFareyStableSum.exists_stable R S hR hS hm hx hy hxu hyv hvy hd
  subst a;subst b;exact hE
end KroneckerCentralStripStableInduction
end
end

/- Original module: KroneckerCentralStripNonempty -/
section
/-! Actual canonical orbit spaces are nonempty at every positive primitive central-strip dimension. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCentralStripNonempty
open KroneckerReflectionPairModel KroneckerCanonicalKroneckerModuli
theorem nonempty (m : ℕ) (hm : 3≤m) (a b : ℕ) (ha : 0<a) (hl : a≤b)
 (hu : b≤(m-1)*a) (hp : Nat.Coprime a b) : Nonempty (space m a b) := by
 obtain ⟨R,hR⟩ := KroneckerCentralStripStableInduction.exists_stable m hm a b ha hl hu hp
 exact (space_nonempty_iff m a b).mpr ⟨toRepresentation R,(KroneckerReflectionPairStability.stable_iff R).mpr hR⟩
end KroneckerCentralStripNonempty
end
end

/- Original module: KroneckerFundamentalNonemptyProved -/
section
/-! The fundamental-region nonemptiness premise is discharged constructively, without Euler or homology assumptions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFundamentalNonemptyProved
open KroneckerCanonicalKroneckerModuli KroneckerNegativeTitsSymmetry
theorem nonempty (m : ℕ) (hm : 3≤m) (a b : ℕ) (ha : 0<a) (hl : a≤b)
 (hu : 2*b≤m*a) (hp : Nat.Coprime a b) : Nonempty (space m a b) := by
 apply KroneckerCentralStripNonempty.nonempty m hm a b ha hl _ hp
 have he : m-1+1=m := by omega
 have hmul := congrArg (fun k : ℕ => k*a) he
 have hm2 : 2*a≤m*a := Nat.mul_le_mul_right a (by omega)
 nlinarith [Nat.mul_le_mul_right a (show 1≤m-1 by omega)]
end KroneckerFundamentalNonemptyProved
end
end
