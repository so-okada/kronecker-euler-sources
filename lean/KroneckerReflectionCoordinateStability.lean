import KroneckerReflectionOutgoingMap

section

/-! The sink reflection uses the actual sum of incoming arrow maps. Its
restriction to one coordinate is exactly that arrow, and its image is the sum
of the arrow images. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionIncomingMap
open KroneckerReflectionPairModel KroneckerFiniteQuiverHom
open scoped BigOperators
variable {m a b : ℕ} (R : PairRep m a b)

def incoming : (Fin m → Space a) →ₗ[ℂ] Space b where
  toFun x := ∑ i,R i (x i)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]

theorem incoming_single (i : Fin m) (x : Space a) : incoming R (Pi.single i x)=R i x := by
  simp [incoming,Pi.single_apply,apply_ite]

theorem arrow_range_le (i : Fin m) : LinearMap.range (R i)≤LinearMap.range (incoming R) := by
  rintro y ⟨x,rfl⟩
  exact ⟨Pi.single i x,incoming_single R i x⟩

theorem range_eq : LinearMap.range (incoming R)=⨆ i,LinearMap.range (R i) := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    change (∑ i,R i (x i)) ∈ _
    exact Submodule.sum_mem _ (fun i _ => (le_iSup (fun j => LinearMap.range (R j)) i) ⟨x i,rfl⟩)
  · exact iSup_le (arrow_range_le R)
end KroneckerReflectionIncomingMap
end
end

section

/-! Stability forces the sum of incoming arrows to be surjective whenever
the source dimension is positive. This is the first BGP reflection gate. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionStableSurjectivity
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel KroneckerReflectionIncomingMap
variable {m a b : ℕ} (R : PairRep m a b)

theorem incoming_surjective (ha : 0<a) (hR : PairStable R) : Function.Surjective (incoming R) := by
  apply LinearMap.range_eq_top.mp
  by_contra hnot
  let W := LinearMap.range (incoming R)
  have hwle : finrank ℂ W≤b := by simpa [Space] using W.finrank_le
  have hwne : finrank ℂ W≠b := by
    intro h
    apply hnot
    exact Submodule.eq_top_of_finrank_eq (by simpa [Space] using h)
  have hw : finrank ℂ W<b := by omega
  have hs : PairInvariant R ⊤ W := by
    intro i x _
    exact arrow_range_le R i ⟨x,rfl⟩
  have ht : finrank ℂ (⊤ : Submodule ℂ (Space a))=a := by simp [Space]
  have hn : 0<finrank ℂ (⊤ : Submodule ℂ (Space a))+finrank ℂ W := by omega
  have hp : finrank ℂ (⊤ : Submodule ℂ (Space a))+finrank ℂ W<a+b := by omega
  have H := hR ⊤ W hs hn hp
  rw [ht] at H
  have hwa : (finrank ℂ W : ℤ)<b := by exact_mod_cast hw
  have ha' : (0 : ℤ)<a := by exact_mod_cast ha
  nlinarith
end KroneckerReflectionStableSurjectivity
end
end

section

/-! Rank-nullity gives the exact dimension of the reflection kernel and both
basic m-Kronecker dimension inequalities from actual stability. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionKernelDimension
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel KroneckerReflectionIncomingMap
variable {m a b : ℕ} (R : PairRep m a b)

theorem sink_bound (ha : 0<a) (hs : PairStable R) : b≤m*a := by
  have H := (incoming R).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (KroneckerReflectionStableSurjectivity.incoming_surjective R ha hs)] at H
  have HH : b+finrank ℂ (LinearMap.ker (incoming R))=m*a := by
    simpa [Space,Module.finrank_pi_fintype] using H
  omega

theorem source_bound (hb : 0<b) (hs : PairStable R) : a≤m*b := by
  have H := LinearMap.finrank_le_finrank_of_injective
    (KroneckerReflectionOutgoingMap.outgoing_injective R hb hs)
  simpa [Space,Module.finrank_pi_fintype] using H

theorem kernel_dimension (h : Function.Surjective (incoming R)) :
    finrank ℂ (LinearMap.ker (incoming R))=m*a-b := by
  have H := (incoming R).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr h] at H
  have HH : b+finrank ℂ (LinearMap.ker (incoming R))=m*a := by
    simpa [Space,Module.finrank_pi_fintype] using H
  omega
end KroneckerReflectionKernelDimension
end
end

section

/- Original module: KroneckerReflectionKernelArrows -/
section
/-! Actual reflected arrows are the coordinate projections from the incoming
kernel. Subrepresentations use arbitrary subspaces of this actual kernel. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionKernelArrows
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel KroneckerReflectionIncomingMap
variable {m a b : ℕ} (R : PairRep m a b)
abbrev Kernel := LinearMap.ker (incoming R)

def arrow (i : Fin m) : Kernel R →ₗ[ℂ] Space a := (LinearMap.proj i).comp (Kernel R).subtype

def Invariant (U : Submodule ℂ (Kernel R)) (V : Submodule ℂ (Space a)) : Prop :=
  ∀ i x,x∈U → arrow R i x∈V

def Stable : Prop :=
  ∀ (U : Submodule ℂ (Kernel R)) (V : Submodule ℂ (Space a)),
    Invariant R U V → 0<finrank ℂ U+finrank ℂ V →
    finrank ℂ U+finrank ℂ V<finrank ℂ (Kernel R)+a →
      (a : ℤ)*(finrank ℂ U : ℤ)-(finrank ℂ (Kernel R) : ℤ)*(finrank ℂ V : ℤ)<0

end KroneckerReflectionKernelArrows
end
end

/- Original module: KroneckerReflectionRestrictedIncoming -/
section
/-! An arbitrary reflected sink subspace V determines the genuine original
subrepresentation (V,sum_i R_i(V)), with exact restricted rank-nullity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionRestrictedIncoming
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel KroneckerReflectionIncomingMap
open scoped BigOperators
variable {m a b : ℕ} (R : PairRep m a b) (V : Submodule ℂ (Space a))

def restricted : (Fin m → V) →ₗ[ℂ] Space b :=
  (incoming R).comp (LinearMap.pi (fun i => V.subtype.comp (LinearMap.proj i)))

theorem restricted_single (i : Fin m) (x : V) : restricted R V (Pi.single i x)=R i x := by
  simp [restricted,incoming,Pi.single_apply,apply_ite]

theorem original_invariant : PairInvariant R V (LinearMap.range (restricted R V)) := by
  intro i x hx
  exact ⟨Pi.single i ⟨x,hx⟩,restricted_single R V i ⟨x,hx⟩⟩

theorem rank_nullity : finrank ℂ (LinearMap.range (restricted R V))+
    finrank ℂ (LinearMap.ker (restricted R V))=m*finrank ℂ V := by
  simpa [Module.finrank_pi_fintype] using (restricted R V).finrank_range_add_finrank_ker
end KroneckerReflectionRestrictedIncoming
end
end

/- Original module: KroneckerReflectionSubspaceCapacity -/
section
/-! Every actual reflected source subspace injects into the kernel of the
incoming map restricted to its sink subspace. This is the load-bearing rank
inequality for preservation of stability under global reflection. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionSubspaceCapacity
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel KroneckerReflectionIncomingMap
open KroneckerReflectionKernelArrows KroneckerReflectionRestrictedIncoming
variable {m a b : ℕ} (R : PairRep m a b)
  (U : Submodule ℂ (Kernel R)) (V : Submodule ℂ (Space a)) (h : Invariant R U V)

def kernelEmbedding : U →ₗ[ℂ] LinearMap.ker (restricted R V) where
  toFun x := ⟨fun i => ⟨x.val.val i,h i x.val x.property⟩,x.val.property⟩
  map_add' x y := rfl
  map_smul' c x := rfl

theorem kernelEmbedding_injective : Function.Injective (kernelEmbedding R U V h) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact congrArg (fun z : LinearMap.ker (restricted R V) => (z.val i).val) he

include h in
theorem capacity : finrank ℂ U+finrank ℂ (LinearMap.range (restricted R V))≤m*finrank ℂ V := by
  have H := LinearMap.finrank_le_finrank_of_injective (kernelEmbedding_injective R U V h)
  have hn := rank_nullity R V
  omega
end KroneckerReflectionSubspaceCapacity
end
end

/- Original module: KroneckerReflectionKernelStability -/
section
/-! Global sink reflection preserves actual stability on its kernel model.
The proof treats every reflected subrepresentation and uses the original
stable inequality plus the proved restricted-kernel capacity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionKernelStability
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel KroneckerReflectionIncomingMap
open KroneckerReflectionKernelArrows KroneckerReflectionRestrictedIncoming
variable {m a b : ℕ} (R : PairRep m a b)

theorem stable (ha : 0<a) (hs : PairStable R) : KroneckerReflectionKernelArrows.Stable R := by
  intro U V hUV hn hp
  let W := LinearMap.range (restricted R V)
  have hcap := KroneckerReflectionSubspaceCapacity.capacity R U V hUV
  have hvle : finrank ℂ V≤a := by simpa [Space] using V.finrank_le
  have hwle : finrank ℂ W≤b := by simpa [Space] using W.finrank_le
  have hdim := KroneckerReflectionKernelDimension.kernel_dimension R
    (KroneckerReflectionStableSurjectivity.incoming_surjective R ha hs)
  have hbound := KroneckerReflectionKernelDimension.sink_bound R ha hs
  have hdim' : (finrank ℂ (Kernel R) : ℤ)=(m : ℤ)*a-b := by
    rw [hdim,Nat.cast_sub hbound,Nat.cast_mul]
  have hvpos : 0<finrank ℂ V := by
    by_contra h
    have hz : finrank ℂ V=0 := by omega
    rw [hz] at hcap
    have hu0 : finrank ℂ U=0 := by
      have hc : finrank ℂ U+finrank ℂ W≤0 := by simpa using hcap
      omega
    omega
  by_cases hproper : finrank ℂ V+finrank ℂ W<a+b
  · have H := hs V W (original_invariant R V) (by omega) hproper
    have hc : (finrank ℂ U : ℤ)+finrank ℂ W≤(m : ℤ)*finrank ℂ V := by exact_mod_cast hcap
    have ha' : (0 : ℤ)<a := by exact_mod_cast ha
    rw [hdim']
    nlinarith
  · have hv : finrank ℂ V=a := by omega
    have hu : finrank ℂ U<finrank ℂ (Kernel R) := by omega
    rw [hv]
    have ha' : (0 : ℤ)<a := by exact_mod_cast ha
    have hu' : (finrank ℂ U : ℤ)<finrank ℂ (Kernel R) := by exact_mod_cast hu
    nlinarith
end KroneckerReflectionKernelStability
end
end

/- Original module: KroneckerReflectionKernelCoordinates -/
section
/-! Coordinate realization of the actual reflection kernel, with a linear
isomorphism fixing its dimension and actual reflected arrow maps. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionKernelCoordinates
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel KroneckerReflectionIncomingMap
open KroneckerReflectionKernelArrows
variable {m a b : ℕ} (R : PairRep m a b) (h : Function.Surjective (incoming R))

def coordinates : Kernel R ≃ₗ[ℂ] Space (m*a-b) :=
  (Module.finBasisOfFinrankEq ℂ (Kernel R) (KroneckerReflectionKernelDimension.kernel_dimension R h)).equivFun

def reflected : PairRep m (m*a-b) a := fun i =>
  (arrow R i).comp (coordinates R h).symm.toLinearMap

theorem reflected_arrow (i : Fin m) (x : Kernel R) :
    reflected R h i (coordinates R h x)=x.val i := by
  simp [reflected,LinearMap.comp_apply,arrow]

def subspaceEquiv (U : Submodule ℂ (Space (m*a-b))) :
    U.comap (coordinates R h).toLinearMap ≃ₗ[ℂ] U where
  toFun x := ⟨coordinates R h x,x.property⟩
  invFun y := ⟨(coordinates R h).symm y,by simpa using y.property⟩
  left_inv x := Subtype.ext ((coordinates R h).symm_apply_apply x)
  right_inv y := Subtype.ext ((coordinates R h).apply_symm_apply y)
  map_add' x y := Subtype.ext ((coordinates R h).map_add x y)
  map_smul' c x := Subtype.ext ((coordinates R h).map_smul c x)
end KroneckerReflectionKernelCoordinates
end
end
end

section

/-! The coordinated reflected representation is stable in exactly the same
all-subspace sense as the actual m-Kronecker source model. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionCoordinateStability
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel KroneckerReflectionIncomingMap
open KroneckerReflectionKernelArrows KroneckerReflectionKernelCoordinates
variable {m a b : ℕ} (R : PairRep m a b)

theorem reflected_stable (ha : 0<a) (hs : PairStable R)
    (h : Function.Surjective (incoming R)) : PairStable (reflected R h) := by
  intro U V hUV hn hp
  let U' := U.comap (coordinates R h).toLinearMap
  have hd : finrank ℂ U'=finrank ℂ U := (subspaceEquiv R h U).finrank_eq
  have hi : Invariant R U' V := by
    intro i x hx
    have H := hUV i (coordinates R h x) hx
    rwa [reflected_arrow] at H
  have hk := KroneckerReflectionKernelDimension.kernel_dimension R h
  have H := KroneckerReflectionKernelStability.stable R ha hs U' V hi
  rw [hd,hk] at H
  exact H hn hp
end KroneckerReflectionCoordinateStability
end
end

