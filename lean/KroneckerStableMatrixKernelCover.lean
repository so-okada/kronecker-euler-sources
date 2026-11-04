import KroneckerPairMatrixOutgoing
import KroneckerMatrixKernelEquivalence

section

noncomputable section
set_option autoImplicit false
namespace KroneckerFiniteQuiverHom
open Module
variable {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
  {R S : Representation s t d}

/-- Pull back every vertex subspace, retaining all subrepresentations. -/
def Iso.pullSubrep (e : Iso R S) (U : Subrep S) : Subrep R where
  space v := (U.space v).comap (e.map v).toLinearMap
  invariant a x hx := by
    change e.map (t a) (R.arrow a x) ∈ U.space (t a)
    rw [e.commutes]
    exact U.invariant a (e.map (s a) x) hx

def Iso.pullSpaceEquiv (e : Iso R S) (U : Subrep S) (v : V) :
    (e.pullSubrep U).space v ≃ₗ[ℂ] U.space v where
  toFun x := ⟨e.map v x, x.property⟩
  invFun y := ⟨(e.map v).symm y, by
    change e.map v ((e.map v).symm y) ∈ U.space v
    simpa using y.property⟩
  left_inv x := Subtype.ext ((e.map v).symm_apply_apply x)
  right_inv y := Subtype.ext ((e.map v).apply_symm_apply y)
  map_add' x y := Subtype.ext ((e.map v).map_add x y)
  map_smul' r x := Subtype.ext ((e.map v).map_smul r x)

theorem Iso.pullSubrep_size (e : Iso R S) (U : Subrep S) :
    size (e.pullSubrep U) = size U := by
  unfold size
  exact Finset.sum_congr rfl fun v _ => (e.pullSpaceEquiv U v).finrank_eq

theorem Iso.pullSubrep_weight (e : Iso R S) (U : Subrep S) (θ : V → ℤ) :
    weight θ (e.pullSubrep U) = weight θ U := by
  unfold weight
  simp_rw [(e.pullSpaceEquiv U _).finrank_eq]

/-- King stability is invariant under the actual vertexwise isomorphism. -/
theorem Iso.stable_iff (e : Iso R S) (θ : V → ℤ) : Stable θ R ↔ Stable θ S := by
  have transport : ∀ {R S : Representation s t d}, Iso R S → Stable θ R → Stable θ S := by
    intro R S e h
    refine ⟨h.1, ?_⟩
    intro U hn hp
    have hn' : 0 < size (e.pullSubrep U) := by rw [e.pullSubrep_size]; exact hn
    have hp' : size (e.pullSubrep U) < ∑ v, d v := by rw [e.pullSubrep_size]; exact hp
    simpa only [e.pullSubrep_weight] using h.2 (e.pullSubrep U) hn' hp'
  exact ⟨transport e, transport e.symm⟩
end KroneckerFiniteQuiverHom
end
end

section

/-! Stable rectangular arrow matrices carry precisely the canonical stable
family topology, with an explicit homeomorphism rather than a set-only bridge. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableRectangularMatrices
open KroneckerPairMatrixCoordinates KroneckerReflectionPairModel
open KroneckerStablePairFamilyEquivalence KroneckerCanonicalKroneckerModuli
abbrev Stable (m a b : ℕ) := {M : Matrices m a b // PairStable (pair M)}
def canonical (m a b : ℕ) : Stable m a b ≃ₜ StableMatrix m a b where
  toFun M := ⟨M.val,(KroneckerReflectionPairStability.stable_iff (pair M.val)).mpr M.property⟩
  invFun M := ⟨M.val,(KroneckerReflectionPairStability.stable_iff (pair M.val)).mp M.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _
end KroneckerStableRectangularMatrices
end
end

section

/- Original module: KroneckerSurjectiveLinearSplitting -/
section
/-! A chosen right inverse splits a surjective linear map into its actual
kernel and target. This fixed coordinate system is the base of moving-kernel charts. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSurjectiveLinearSplitting
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable (p : V →ₗ[ℂ] W) (s : W →ₗ[ℂ] V) (hs : ∀ w,p (s w)=w)

def kernelProjection : V →ₗ[ℂ] LinearMap.ker p where
  toFun x := ⟨x-s (p x),by simp only [LinearMap.mem_ker,map_sub,hs,sub_self]⟩
  map_add' x y := by apply Subtype.ext;simp [map_add];abel
  map_smul' c x := by apply Subtype.ext;simp [map_smul,smul_sub]

def split : V ≃ₗ[ℂ] (LinearMap.ker p × W) where
  toFun x := (kernelProjection p s hs x,p x)
  invFun z := z.1.val+s z.2
  left_inv x := sub_add_cancel _ _
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change z.1.val+s z.2-s (p (z.1.val+s z.2))=z.1.val
      rw [map_add,show p z.1.val=0 from z.1.property,hs,zero_add]
      abel
    · change p (z.1.val+s z.2)=z.2
      rw [map_add,show p z.1.val=0 from z.1.property,hs,zero_add]
  map_add' x y := Prod.ext ((kernelProjection p s hs).map_add x y) (p.map_add x y)
  map_smul' c x := Prod.ext ((kernelProjection p s hs).map_smul c x) (p.map_smul c x)

theorem section_exists (hp : Function.Surjective p) : ∃ s : W →ₗ[ℂ] V,∀ w,p (s w)=w := by
  obtain ⟨s,hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  exact ⟨s,fun w => congrArg (fun f : W →ₗ[ℂ] W => f w) hs⟩
end KroneckerSurjectiveLinearSplitting
end
end

/- Original module: KroneckerMatrixKernelChartCover -/
section
/-! Every surjective matrix belongs to a fixed-section open chart. This
proves chart coverage without assuming a global continuous choice of section. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixKernelChartCover
open KroneckerMatrixKernelChart
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v] [DecidableEq w]
theorem exists_section (P : Matrix w v ℂ) (hP : Function.Surjective (Matrix.toLin' P)) :
    ∃ S : Matrix v w ℂ, P * S = 1 := by
  obtain ⟨s,hs⟩ := KroneckerSurjectiveLinearSplitting.section_exists (Matrix.toLin' P) hP
  refine ⟨LinearMap.toMatrix' s,?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
  apply LinearMap.ext
  intro x
  exact hs x
theorem covered (P : Matrix w v ℂ) (hP : Function.Surjective (Matrix.toLin' P)) :
    ∃ S : Matrix v w ℂ, P ∈ Domain S := by
  obtain ⟨S,hS⟩ := exists_section P hP
  refine ⟨S,?_⟩
  change (P*S).det ≠ 0
  rw [hS,Matrix.det_one]
  exact one_ne_zero
end KroneckerMatrixKernelChartCover
end
end

/- Original module: KroneckerStableMatrixIncomingSurjective -/
section
/-! Positive-source stable matrix families have surjective incoming block
matrices, supplying the precise chart-cover hypothesis for sink reflection. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableMatrixIncomingSurjective
open KroneckerPairMatrixCoordinates KroneckerPairMatrixIncoming KroneckerStableRectangularMatrices
variable {m a b : ℕ}
theorem surjective (ha : 0<a) (M : Stable m a b) :
    Function.Surjective (Matrix.toLin' (incoming M.val)) := by
  have h := KroneckerReflectionStableSurjectivity.incoming_surjective (pair M.val) ha M.property
  intro y
  obtain ⟨x,hx⟩ := h y
  exact ⟨flatten x,by rw [evaluate];exact hx⟩
end KroneckerStableMatrixIncomingSurjective
end
end

/- Original module: KroneckerStableMatrixKernelCover -/
section
/-! The incoming fixed-section charts pull back to an open cover of the
actual stable matrix space, without requiring the stable locus itself to be open. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableMatrixKernelCover
open KroneckerPairMatrixIncoming KroneckerStableRectangularMatrices
variable {m a b : ℕ}
def chart (S : Matrix (Fin m × Fin a) (Fin b) ℂ) : Set (Stable m a b) :=
  {M | incoming M.val ∈ KroneckerMatrixKernelChart.Domain S}
theorem chart_open (S : Matrix (Fin m × Fin a) (Fin b) ℂ) : IsOpen (chart S) :=
  (KroneckerMatrixKernelChart.isOpen_domain S).preimage
    (continuous_incoming.comp continuous_subtype_val)
theorem cover (ha : 0<a) (M : Stable m a b) :
    ∃ S : Matrix (Fin m × Fin a) (Fin b) ℂ,M ∈ chart S :=
  KroneckerMatrixKernelChartCover.covered _ (KroneckerStableMatrixIncomingSurjective.surjective ha M)
def parameter (S : Matrix (Fin m × Fin a) (Fin b) ℂ) (M : chart S) :
    KroneckerMatrixKernelChart.Domain S := ⟨incoming M.val.val,M.property⟩
theorem continuous_parameter (S : Matrix (Fin m × Fin a) (Fin b) ℂ) : Continuous (parameter S) :=
  (continuous_incoming.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
end KroneckerStableMatrixKernelCover
end
end
end

section

/- Original module: KroneckerGaugeFamilyHomeomorphism -/
section
/-! Every fixed complex product-GL gauge transformation is a homeomorphism of
the actual product topology on arrow matrices. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerGaugeFamilyHomeomorphism
open KroneckerRingQuiverFamilies
variable {V A : Type} [Fintype V] [Fintype A]
  (s t : A → V) (d : V → ℕ)

theorem continuous_gauge (g : Gauge d ℂ) : Continuous (gauge s t d g) := by
  apply continuous_pi
  intro a
  exact (continuous_const.matrix_mul (continuous_apply a)).matrix_mul continuous_const

def homeomorph (g : Gauge d ℂ) : Family s t d ℂ ≃ₜ Family s t d ℂ where
  toFun := gauge s t d g
  invFun := gauge s t d g⁻¹
  left_inv M := by rw [←gauge_mul];simp
  right_inv M := by rw [←gauge_mul];simp
  continuous_toFun := continuous_gauge s t d g
  continuous_invFun := continuous_gauge s t d g⁻¹
end KroneckerGaugeFamilyHomeomorphism
end
end

/- Original module: KroneckerGaugeStableHomeomorphism -/
section
/-! Gauge transformations restrict to homeomorphisms of the genuine stable
locus, with stability preserved by the actual representation isomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerGaugeStableHomeomorphism
open KroneckerRingQuiverFamilies KroneckerStableOrbitEuler KroneckerFiniteQuiverHom
variable {V A : Type} [Fintype V] [Fintype A]
  (s t : A → V) (d : V → ℕ) (θ : V → ℤ)

def homeomorph (g : Gauge d ℂ) : StableFamily s t d θ ≃ₜ StableFamily s t d θ :=
  (KroneckerGaugeFamilyHomeomorphism.homeomorph s t d g).subtype
    (fun M => (gaugeIso s t d g M).stable_iff θ)

end KroneckerGaugeStableHomeomorphism
end
end

/- Original module: KroneckerStableOrbitOpenProjection -/
section
/-! The canonical stable matrix quotient is an open quotient map. Saturations
are unions of gauge translates of open subsets, proved for the actual action. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableOrbitOpenProjection
open KroneckerRingQuiverFamilies KroneckerStableOrbitEuler KroneckerCanonicalStableOrbit
variable {V A : Type} [Fintype V] [Fintype A]
  (s t : A → V) (d : V → ℕ) (θ : V → ℤ)


end KroneckerStableOrbitOpenProjection
end
end

/- Original module: KroneckerStableMatrixProjection -/
section
/-! Stable rectangular matrices project onto the canonical moduli space by
an open quotient map, with exactly the actual pair-isomorphism fibers. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableMatrixProjection
open KroneckerStableRectangularMatrices KroneckerCanonicalKroneckerModuli
variable (m a b : ℕ)
def project : Stable m a b → space m a b :=
  KroneckerCanonicalStableOrbit.project (source m) (target m) (dimension a b) (character a b) ∘ canonical m a b
theorem continuous_project : Continuous (project m a b) :=
  (KroneckerCanonicalStableOrbit.project_continuous _ _ _ _).comp (canonical m a b).continuous
theorem quotient_project : Topology.IsQuotientMap (project m a b) :=
  isQuotientMap_quotient_mk'.comp (canonical m a b).isQuotientMap
theorem pair_project (M : Stable m a b) :
    project m a b M=KroneckerStablePairProjection.project m a b ⟨KroneckerPairMatrixCoordinates.pair M.val,M.property⟩ := by
  exact (KroneckerStablePairProjection.fromMatrix_project m a b (canonical m a b M)).symm
end KroneckerStableMatrixProjection
end
end
end

