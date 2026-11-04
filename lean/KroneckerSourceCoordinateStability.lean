import KroneckerCokernelDimension
import KroneckerReflectionExactImage
import KroneckerCokernelReflectionIso

section

/- Original module: KroneckerSourceReflectionSubspaces -/
section
/-! For a sink subspace, its inverse image under all original arrows forms
an actual original subrepresentation. The coordinate-restricted quotient map
is the rank comparison underlying source-reflection stability. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceReflectionSubspaces
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel
open KroneckerAbstractOutgoingNaturality KroneckerAbstractCokernelReflection
variable {m a b : ℕ} (R : PairRep m a b)

def preimage (U : Submodule ℂ (Space b)) : Submodule ℂ (Space a) :=
  (Submodule.pi Set.univ (fun _ : Fin m => U)).comap (outgoing R)

theorem mem_preimage (U : Submodule ℂ (Space b)) (x : Space a) :
    x∈preimage R U ↔ ∀ i,R i x∈U := by simp [preimage,outgoing,Submodule.mem_pi]

theorem invariant (U : Submodule ℂ (Space b)) : PairInvariant R (preimage R U) U := by
  intro i x hx
  exact (mem_preimage R U x).mp hx i

def inclusion (U : Submodule ℂ (Space b)) : (Fin m → U) →ₗ[ℂ] (Fin m → Space b) :=
  LinearMap.pi (fun i => U.subtype.comp (LinearMap.proj i))

def restricted (U : Submodule ℂ (Space b)) : (Fin m → U) →ₗ[ℂ] Cokernel R :=
  (quotient R).comp (inclusion U)
end KroneckerSourceReflectionSubspaces
end
end

/- Original module: KroneckerSourceRestrictedKernel -/
section
/-! The kernel of the restricted quotient is exactly the original preimage
subspace, via the outgoing map. The isomorphism uses actual injectivity, not dimensions alone. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceRestrictedKernel
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel
open KroneckerAbstractOutgoingNaturality KroneckerAbstractCokernelReflection
open KroneckerSourceReflectionSubspaces
variable {m a b : ℕ} (R : PairRep m a b) (U : Submodule ℂ (Space b))

def embed : preimage R U →ₗ[ℂ] LinearMap.ker (restricted R U) where
  toFun x := ⟨fun i => ⟨R i x.val,(mem_preimage R U x.val).mp x.property i⟩,by
    change quotient R (outgoing R x.val)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x.val,rfl⟩⟩
  map_add' x y := by apply Subtype.ext;funext i;apply Subtype.ext;exact (R i).map_add _ _
  map_smul' c x := by apply Subtype.ext;funext i;apply Subtype.ext;exact (R i).map_smul _ _

theorem bijective (h : Function.Injective (outgoing R)) : Function.Bijective (embed R U) := by
  constructor
  · intro x y he
    apply Subtype.ext
    apply h
    funext i
    exact congrArg (fun z : LinearMap.ker (restricted R U) => (z.val i).val) he
  · intro z
    have hz : quotient R (inclusion U z.val)=0 := z.property
    obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    have hp : x∈preimage R U := by
      apply (mem_preimage R U x).mpr
      intro i
      have hi : R i x=(z.val i).val := congrFun hx i
      rw [hi]
      exact (z.val i).property
    refine ⟨⟨x,hp⟩,?_⟩
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun hx i

def equiv (h : Function.Injective (outgoing R)) : preimage R U ≃ₗ[ℂ] LinearMap.ker (restricted R U) :=
  LinearEquiv.ofBijective (embed R U) (bijective R U h)
end KroneckerSourceRestrictedKernel
end
end

/- Original module: KroneckerSourceReflectionCapacity -/
section
/-! Every source-reflected invariant pair satisfies the quotient rank
capacity inequality m*dim(U) ≤ dim(V)+dim(original preimage). -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceReflectionCapacity
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel
open KroneckerAbstractOutgoingNaturality KroneckerAbstractCokernelReflection
open KroneckerSourceReflectionSubspaces
variable {m a b : ℕ} (R : PairRep m a b)

def Invariant (U : Submodule ℂ (Space b)) (V : Submodule ℂ (Cokernel R)) : Prop :=
  ∀ i x,x∈U → reflection R i x∈V

theorem range_le (U : Submodule ℂ (Space b)) (V : Submodule ℂ (Cokernel R)) (h : Invariant R U V) :
    LinearMap.range (restricted R U)≤V := by
  rintro _ ⟨x,rfl⟩
  change quotient R (inclusion U x)∈V
  rw [←KroneckerReflectionExactImage.cokernel_incoming]
  change (∑ i : Fin m,reflection R i (x i).val)∈V
  exact V.sum_mem (fun i _ => h i (x i).val (x i).property)

theorem capacity (hR : Function.Injective (outgoing R)) (U : Submodule ℂ (Space b))
    (V : Submodule ℂ (Cokernel R)) (h : Invariant R U V) :
    m*finrank ℂ U≤finrank ℂ V+finrank ℂ (preimage R U) := by
  have hr := Submodule.finrank_mono (range_le R U V h)
  have he := (restricted R U).finrank_range_add_finrank_ker
  rw [←(KroneckerSourceRestrictedKernel.equiv R U hR).finrank_eq] at he
  have hp : finrank ℂ (Fin m → U)=m*finrank ℂ U := by simp [Module.finrank_pi_fintype]
  rw [hp] at he
  omega
end KroneckerSourceReflectionCapacity
end
end

/- Original module: KroneckerSourceReflectionStability -/
section
/-! Source-cokernel reflection preserves stability on the actual quotient
space. The proof checks all invariant subspaces using the proved rank capacity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceReflectionStability
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel
open KroneckerAbstractOutgoingNaturality KroneckerAbstractCokernelReflection
open KroneckerSourceReflectionSubspaces KroneckerSourceReflectionCapacity
variable {m a b : ℕ} (R : PairRep m a b)

def Stable : Prop := ∀ (U : Submodule ℂ (Space b)) (V : Submodule ℂ (Cokernel R)),
  Invariant R U V → 0<finrank ℂ U+finrank ℂ V →
  finrank ℂ U+finrank ℂ V<b+finrank ℂ (Cokernel R) →
  (finrank ℂ (Cokernel R) : ℤ)*(finrank ℂ U : ℤ)-(b : ℤ)*(finrank ℂ V : ℤ)<0

theorem stable (hb : 0<b) (hs : PairStable R) : Stable R := by
  intro U V hUV hn hp
  have hR : Function.Injective (outgoing R) := KroneckerReflectionOutgoingMap.outgoing_injective R hb hs
  have hc := capacity R hR U V hUV
  have hxle : finrank ℂ (preimage R U)≤a := by simpa [Space] using (preimage R U).finrank_le
  have hule : finrank ℂ U≤b := by simpa [Space] using U.finrank_le
  have hvle : finrank ℂ V≤finrank ℂ (Cokernel R) := V.finrank_le
  have hdim := KroneckerCokernelDimension.dimension R hR
  have hbound := KroneckerCokernelDimension.bound R hR
  have hk : (finrank ℂ (Cokernel R) : ℤ)=(m : ℤ)*b-a := by
    rw [hdim,Nat.cast_sub hbound,Nat.cast_mul]
  have hb' : (0 : ℤ)<b := by exact_mod_cast hb
  by_cases hu : finrank ℂ U=0
  · have hv : (0 : ℤ)<finrank ℂ V := by exact_mod_cast (show 0<finrank ℂ V by omega)
    rw [hu]
    norm_num
    exact mul_pos hb' hv
  · have hpos : 0<finrank ℂ (preimage R U)+finrank ℂ U := by omega
    have hproper : finrank ℂ (preimage R U)+finrank ℂ U<a+b := by
      by_contra hh
      have hx : finrank ℂ (preimage R U)=a := by omega
      have hu' : finrank ℂ U=b := by omega
      rw [hx,hu'] at hc
      omega
    have horig := hs (preimage R U) U (invariant R U) hpos hproper
    have hcap : (m : ℤ)*finrank ℂ U≤finrank ℂ V+finrank ℂ (preimage R U) := by exact_mod_cast hc
    rw [hk]
    nlinarith
end KroneckerSourceReflectionStability
end
end

/- Original module: KroneckerSourceReflectionCoordinates -/
section
/-! Realize the actual source-reflection quotient in canonical finite
coordinates, retaining an explicit representation isomorphism to the quotient model. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceReflectionCoordinates
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel
open KroneckerAbstractOutgoingNaturality KroneckerAbstractCokernelReflection
variable {m a b : ℕ} (R : PairRep m a b) (h : Function.Injective (outgoing R))

def coordinates : Cokernel R ≃ₗ[ℂ] Space (m*b-a) :=
  (Module.finBasisOfFinrankEq ℂ (Cokernel R) (KroneckerCokernelDimension.dimension R h)).equivFun

def reflected : PairRep m b (m*b-a) := fun i => (coordinates R h).toLinearMap.comp (reflection R i)

def coordinateIso : KroneckerAbstractPairIso.Iso (reflection R) (reflected R h) :=
  ⟨LinearEquiv.refl ℂ _,coordinates R h,fun _ _ => rfl⟩

def subspaceEquiv (V : Submodule ℂ (Space (m*b-a))) :
    V.comap (coordinates R h).toLinearMap ≃ₗ[ℂ] V where
  toFun x := ⟨coordinates R h x,x.property⟩
  invFun y := ⟨(coordinates R h).symm y,by simpa using y.property⟩
  left_inv x := Subtype.ext ((coordinates R h).symm_apply_apply x)
  right_inv y := Subtype.ext ((coordinates R h).apply_symm_apply y)
  map_add' x y := Subtype.ext ((coordinates R h).map_add x y)
  map_smul' c x := Subtype.ext ((coordinates R h).map_smul c x)
end KroneckerSourceReflectionCoordinates
end
end
end

section

/-! The coordinated inverse reflection is stable for the actual canonical
character, by transport of every sink subspace through the quotient coordinates. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceCoordinateStability
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel
open KroneckerAbstractOutgoingNaturality KroneckerAbstractCokernelReflection
open KroneckerSourceReflectionCoordinates
variable {m a b : ℕ} (R : PairRep m a b)

theorem stable (hb : 0<b) (hs : PairStable R) (h : Function.Injective (outgoing R)) :
    PairStable (reflected R h) := by
  intro U V hUV hn hp
  let V' := V.comap (coordinates R h).toLinearMap
  have hd : finrank ℂ V'=finrank ℂ V := (subspaceEquiv R h V).finrank_eq
  have hi : KroneckerSourceReflectionCapacity.Invariant R U V' := by
    intro i x hx
    exact hUV i x hx
  have H := KroneckerSourceReflectionStability.stable R hb hs U V' hi
  rw [hd,KroneckerCokernelDimension.dimension R h] at H
  exact H hn hp
end KroneckerSourceCoordinateStability
end
end

