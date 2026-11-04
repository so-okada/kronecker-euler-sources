import KroneckerCoverTitsForm
import KroneckerStableSupportTypedConnectivity

/- Original module: KroneckerFiniteQuiverCoordinates -/
section
/- Included in the Lean 4.35 migration checkpoint.
   Saved compiler provenance: audit/lean435-migration-20261031/VERIFICATION.md. -/
set_option autoImplicit false
namespace KroneckerFiniteQuiverHom
open Module
open scoped BigOperators

structure RepresentationOn {V A : Type} (s t : A → V) (E : V → Type)
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)] where
  arrow : ∀ a, E (s a) →ₗ[ℂ] E (t a)

structure SubrepOn {V A : Type} {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)]
    (R : RepresentationOn s t E) where
  space : ∀ v, Submodule ℂ (E v)
  invariant : ∀ a x, x ∈ space (s a) → R.arrow a x ∈ space (t a)

noncomputable def inCoordinates {V A : Type} {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)] {d : V → ℕ}
    (e : ∀ v, E v ≃ₗ[ℂ] Space (d v)) (R : RepresentationOn s t E) : Representation s t d where
  arrow a := (e (t a)).toLinearMap.comp ((R.arrow a).comp (e (s a)).symm.toLinearMap)

noncomputable def toCoordinates {V A : Type} {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)] {d : V → ℕ}
    (e : ∀ v, E v ≃ₗ[ℂ] Space (d v)) {R : RepresentationOn s t E}
    (U : SubrepOn R) : Subrep (inCoordinates e R) where
  space v := (U.space v).map (e v).toLinearMap
  invariant := by
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    apply Submodule.mem_map.mpr
    refine ⟨R.arrow a y, U.invariant a y hy, ?_⟩
    simp [inCoordinates, LinearMap.comp_apply]

noncomputable def fromCoordinates {V A : Type} {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)] {d : V → ℕ}
    (e : ∀ v, E v ≃ₗ[ℂ] Space (d v)) {R : RepresentationOn s t E}
    (U : Subrep (inCoordinates e R)) : SubrepOn R where
  space v := (U.space v).comap (e v).toLinearMap
  invariant := by
    intro a x hx
    change e (t a) (R.arrow a x) ∈ U.space (t a)
    have h := U.invariant a (e (s a) x) hx
    simpa [inCoordinates, LinearMap.comp_apply] using h

theorem subrepOn_ext {V A : Type} {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)]
    {R : RepresentationOn s t E} {U W : SubrepOn R} (h : U.space = W.space) : U = W := by
  cases U
  cases W
  cases h
  rfl

theorem subrep_ext {V A : Type} {s t : A → V} {d : V → ℕ}
    {R : Representation s t d} {U W : Subrep R} (h : U.space = W.space) : U = W := by
  cases U
  cases W
  cases h
  rfl

/-- Coordinates identify ALL invariant vertex-submodule families. -/
noncomputable def coordinateSubrepEquiv {V A : Type} {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)] {d : V → ℕ}
    (e : ∀ v, E v ≃ₗ[ℂ] Space (d v)) (R : RepresentationOn s t E) :
    SubrepOn R ≃ Subrep (inCoordinates e R) where
  toFun := toCoordinates e
  invFun := fromCoordinates e
  left_inv := by
    intro U
    apply subrepOn_ext
    funext v
    exact Submodule.comap_map_eq_of_injective (e v).injective (U.space v)
  right_inv := by
    intro U
    apply subrep_ext
    funext v
    exact Submodule.map_comap_eq_of_surjective (e v).surjective (U.space v)

theorem coordinate_subspace_dimension {V A : Type} {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)] {d : V → ℕ}
    (e : ∀ v, E v ≃ₗ[ℂ] Space (d v)) {R : RepresentationOn s t E}
    (U : SubrepOn R) (v : V) :
    finrank ℂ ((toCoordinates e U).space v) = finrank ℂ (U.space v) :=
  (e v).finrank_map_eq (U.space v)

noncomputable def sizeOn {V A : Type} [Fintype V] {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)]
    {R : RepresentationOn s t E} (U : SubrepOn R) : ℕ := ∑ v, finrank ℂ (U.space v)

noncomputable def weightOn {V A : Type} [Fintype V] {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)]
    {R : RepresentationOn s t E} (θ : V → ℤ) (U : SubrepOn R) : ℤ :=
  ∑ v, θ v * (finrank ℂ (U.space v) : ℤ)

theorem coordinates_preserve_size_weight {V A : Type} [Fintype V] {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)] {d : V → ℕ}
    (e : ∀ v, E v ≃ₗ[ℂ] Space (d v)) {R : RepresentationOn s t E}
    (θ : V → ℤ) (U : SubrepOn R) :
    size (toCoordinates e U) = sizeOn U ∧ weight θ (toCoordinates e U) = weightOn θ U := by
  constructor
  · simp only [size, sizeOn, coordinate_subspace_dimension]
  · simp only [weight, weightOn, coordinate_subspace_dimension]

def StableOn {V A : Type} [Fintype V] {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)]
    (θ : V → ℤ) (R : RepresentationOn s t E) : Prop :=
  (∑ v, θ v * (finrank ℂ (E v) : ℤ)) = 0 ∧
    ∀ U : SubrepOn R, 0 < sizeOn U → sizeOn U < ∑ v, finrank ℂ (E v) → weightOn θ U < 0

theorem coordinate_stability_iff {V A : Type} [Fintype V] {s t : A → V} {E : V → Type}
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)]
    (e : ∀ v, E v ≃ₗ[ℂ] Space (finrank ℂ (E v))) (θ : V → ℤ) (R : RepresentationOn s t E) :
    Stable θ (inCoordinates e R) ↔ StableOn θ R := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro U hn hp
    have hd := coordinates_preserve_size_weight e θ U
    have hw := h.2 (toCoordinates e U) (by simpa only [hd.1] using hn)
      (by simpa only [hd.1] using hp)
    simpa only [hd.2] using hw
  · intro h
    refine ⟨h.1, ?_⟩
    intro U hn hp
    obtain ⟨W, rfl⟩ := (coordinateSubrepEquiv e R).surjective U
    change 0 < size (toCoordinates e W) at hn
    change size (toCoordinates e W) < _ at hp
    change weight θ (toCoordinates e W) < 0
    have hd := coordinates_preserve_size_weight e θ W
    rw [hd.2]
    apply h.2 W
    · simpa only [hd.1] using hn
    · simpa only [hd.1] using hp

/-- Every finite-dimensional family has a concrete coordinate choice. -/
noncomputable def chooseCoordinates {V : Type} (E : V → Type)
    [∀ v, AddCommGroup (E v)] [∀ v, Module ℂ (E v)] [∀ v, FiniteDimensional ℂ (E v)] :
    ∀ v, E v ≃ₗ[ℂ] Space (finrank ℂ (E v)) :=
  fun v => (Module.finBasis ℂ (E v)).equivFun

end KroneckerFiniteQuiverHom
end

/- Original module: KroneckerSparseBlockQuiver -/
section
set_option autoImplicit false
namespace KroneckerSparseBlockQuiver
open Module KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedSubrepEquivalence KroneckerFiniteQuiverHom
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Vertex (B : LinearCoverBlock) := B.Source ⊕ B.Sink
abbrev Arrow (B : LinearCoverBlock) := Σ s, {t // linearSupport B s t}
def source (B : LinearCoverBlock) (a : Arrow B) : Vertex B := .inl a.1
def target (B : LinearCoverBlock) (a : Arrow B) : Vertex B := .inr a.2.1

def vertexSpace (B : LinearCoverBlock) : Vertex B → Type
  | .inl s => B.Space s
  | .inr _ => ℂ

instance vertexSpaceGroup (B : LinearCoverBlock) (v : Vertex B) :
    AddCommGroup (vertexSpace B v) := by
  cases v with
  | inl s => exact inferInstanceAs (AddCommGroup (B.Space s))
  | inr t => exact inferInstanceAs (AddCommGroup ℂ)

instance vertexSpaceModule (B : LinearCoverBlock) (v : Vertex B) :
    Module ℂ (vertexSpace B v) := by
  cases v with
  | inl s => exact inferInstanceAs (Module ℂ (B.Space s))
  | inr t => exact inferInstanceAs (Module ℂ ℂ)

instance vertexSpaceFinite (B : LinearCoverBlock) (v : Vertex B) :
    FiniteDimensional ℂ (vertexSpace B v) := by
  cases v with
  | inl s => exact inferInstanceAs (FiniteDimensional ℂ (B.Space s))
  | inr t => exact inferInstanceAs (FiniteDimensional ℂ ℂ)

/-- The fixed quiver contains exactly the support arrows of the base block B.
Competing representations on this quiver may assign zero maps to these arrows. -/
def representation (B : LinearCoverBlock) :
    RepresentationOn (source B) (target B) (vertexSpace B) where
  arrow a := B.arrow a.1 a.2.1

def toSparse {B : LinearCoverBlock} (U : BlockSubrep B) : SubrepOn (representation B) where
  space v := match v with
    | .inl s => U.source s
    | .inr t => U.sink t
  invariant a x hx := U.invariant a.1 a.2.1 x hx

def fromSparse {B : LinearCoverBlock} (U : SubrepOn (representation B)) : BlockSubrep B where
  source s := U.space (.inl s)
  sink t := U.space (.inr t)
  invariant := by
    intro s t x hx
    by_cases h : linearSupport B s t
    · exact U.invariant ⟨s, ⟨t, h⟩⟩ x hx
    · have hz : B.arrow s t = 0 := by simpa [linearSupport] using h
      rw [hz]
      exact Submodule.zero_mem _

/-- Non-support arrows are zero, so no subrepresentation condition is lost. -/
def blockSubrepEquiv (B : LinearCoverBlock) : BlockSubrep B ≃ SubrepOn (representation B) where
  toFun := toSparse
  invFun := fromSparse
  left_inv U := block_subrep_ext rfl rfl
  right_inv := by
    intro U
    apply subrepOn_ext
    funext v
    cases v <;> rfl

noncomputable def kingWeight (B : LinearCoverBlock) : Vertex B → ℤ
  | .inl _ => Fintype.card B.Sink
  | .inr _ => -(sourceDimension B : ℤ)

theorem sparse_size {B : LinearCoverBlock} (U : BlockSubrep B) :
    sizeOn (toSparse U) = sourceSize U + sinkSize U := by
  simp [sizeOn, toSparse, sourceSize, sinkSize, Fintype.sum_sum_type]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sparse_total_dimension (B : LinearCoverBlock) :
    (∑ v, finrank ℂ (vertexSpace B v)) = sourceDimension B + Fintype.card B.Sink := by
  simp [vertexSpace, Fintype.sum_sum_type, sourceDimension, Module.finrank_self]

theorem sparse_weight {B : LinearCoverBlock} (U : BlockSubrep B) :
    weightOn (kingWeight B) (toSparse U) =
      (Fintype.card B.Sink : ℤ) * sourceSize U - (sourceDimension B : ℤ) * sinkSize U := by
  simp [weightOn, toSparse, kingWeight, Fintype.sum_sum_type, sourceSize, sinkSize,
    Nat.cast_sum, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sparse_full_weight_zero (B : LinearCoverBlock) :
    (∑ v, kingWeight B v * (finrank ℂ (vertexSpace B v) : ℤ)) = 0 := by
  have hf : (∑ v, kingWeight B v * (finrank ℂ (vertexSpace B v) : ℤ)) =
      weightOn (kingWeight B) (toSparse (fullBlock B)) := by
    simp [weightOn, toSparse, fullBlock, vertexSpace, Fintype.sum_sum_type,
      Module.finrank_self, finrank_top]
  rw [hf, sparse_weight, (full_block_dimensions B).1, (full_block_dimensions B).2]
  ring

theorem sparse_stability_iff (B : LinearCoverBlock) :
    StableOn (kingWeight B) (representation B) ↔ BlockKingStable B := by
  constructor
  · intro h U hn hp
    have hw := h.2 (toSparse U) (by simpa only [sparse_size] using hn)
      (by simpa only [sparse_size, sparse_total_dimension] using hp)
    rw [sparse_weight, sub_lt_zero] at hw
    exact_mod_cast hw
  · intro h
    refine ⟨sparse_full_weight_zero B, ?_⟩
    intro U hn hp
    obtain ⟨W, rfl⟩ := (blockSubrepEquiv B).surjective U
    change 0 < sizeOn (toSparse W) at hn
    change sizeOn (toSparse W) < _ at hp
    change weightOn (kingWeight B) (toSparse W) < 0
    rw [sparse_weight, sub_lt_zero]
    have hw := h W (by simpa only [sparse_size] using hn)
      (by simpa only [sparse_size, sparse_total_dimension] using hp)
    exact_mod_cast hw

end KroneckerSparseBlockQuiver
end

/- Original module: KroneckerSparseBlockEuler -/
section
set_option autoImplicit false
namespace KroneckerSparseBlockQuiver
open Module KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedSubrepEquivalence KroneckerFiniteQuiverHom KroneckerCoverTitsForm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This is the same sparse arrow index as the actual block adapter, not the
complete bipartite quiver. Its self Euler form is exactly the certified Tits form. -/
theorem sparse_euler_form (B : LinearCoverBlock) :
    (∑ v : Vertex B, (finrank ℂ (vertexSpace B v) : ℤ)^2) -
      (∑ a : Arrow B, (finrank ℂ (vertexSpace B (source B a)) : ℤ) *
        (finrank ℂ (vertexSpace B (target B a)) : ℤ)) = titsForm B := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  change (∑ s : B.Source, (finrank ℂ (B.Space s) : ℤ)^2) +
    (∑ _ : B.Sink, (finrank ℂ ℂ : ℤ)^2) -
    (∑ s : B.Source, ∑ _ : {t // linearSupport B s t},
      (finrank ℂ (B.Space s) : ℤ) * (finrank ℂ ℂ : ℤ)) = titsForm B
  simp [titsForm, Module.finrank_self]
  ring

theorem positive_tits_dimension_inequality (B : LinearCoverBlock) (hB : 0 < titsForm B) :
    (∑ a : Arrow B, finrank ℂ (vertexSpace B (source B a)) *
      finrank ℂ (vertexSpace B (target B a))) <
      ∑ v : Vertex B, finrank ℂ (vertexSpace B v) * finrank ℂ (vertexSpace B v) := by
  have he := sparse_euler_form B
  have hc : ((∑ v : Vertex B, finrank ℂ (vertexSpace B v) * finrank ℂ (vertexSpace B v) : ℕ) : ℤ) -
      ((∑ a : Arrow B, finrank ℂ (vertexSpace B (source B a)) *
        finrank ℂ (vertexSpace B (target B a)) : ℕ) : ℤ) = titsForm B := by
    simpa only [Nat.cast_sum, Nat.cast_mul, pow_two] using he
  have hi : ((∑ a : Arrow B, finrank ℂ (vertexSpace B (source B a)) *
      finrank ℂ (vertexSpace B (target B a)) : ℕ) : ℤ) <
      ((∑ v : Vertex B, finrank ℂ (vertexSpace B v) * finrank ℂ (vertexSpace B v) : ℕ) : ℤ) := by
    omega
  exact_mod_cast hi

noncomputable def coordinateRepresentation (B : LinearCoverBlock) :
    Representation (source B) (target B) (fun v => finrank ℂ (vertexSpace B v)) :=
  inCoordinates (chooseCoordinates (vertexSpace B)) (representation B)

/-- The original BlockKingStable predicate transports to the actual sparse
quiver coordinate representation. All subrepresentations were included. -/
theorem coordinateRepresentation_stable_iff (B : LinearCoverBlock) :
    Stable (kingWeight B) (coordinateRepresentation B) ↔ BlockKingStable B := by
  rw [coordinateRepresentation, coordinate_stability_iff, sparse_stability_iff]

/-- An actual stable block of positive Tits form is the unique stable coordinate
representation class on its fixed sparse support quiver and dimension vector.
Geometric moduli and Euler-characteristic claims are deliberately absent. -/
theorem stable_block_unique_on_support (B : LinearCoverBlock) (hB : BlockKingStable B)
    (hq : 0 < titsForm B)
    (S : Representation (source B) (target B) (fun v => finrank ℂ (vertexSpace B v)))
    (hS : Stable (kingWeight B) S) : Nonempty (Iso (coordinateRepresentation B) S) := by
  exact positive_euler_stable_iso _ S ((coordinateRepresentation_stable_iff B).mpr hB) hS
    (positive_tits_dimension_inequality B hq)

end KroneckerSparseBlockQuiver
end

/- Original module: KroneckerStablePositiveSupportConnected -/
section
set_option autoImplicit false
namespace KroneckerFiniteQuiverHom
open scoped BigOperators

/-- On the positive-dimensional vertex set, King stability forces connectivity.
The incidence hypothesis merely says nonzero arrows join vertices in the same
component of the specified underlying graph. -/
theorem stable_positive_support_preconnected {V A : Type} [Fintype V]
    {s t : A → V} {d : V → ℕ} (R : Representation s t d) (θ : V → ℤ)
    (hR : Stable θ R) (hpos : ∀ v, 0 < d v) (G : SimpleGraph V)
    (hinc : ∀ a, R.arrow a ≠ 0 → G.Reachable (s a) (t a)) : G.Preconnected := by
  classical
  intro u v
  by_contra huv
  let P : V → Prop := G.Reachable u
  have hcut : ∀ a, P (s a) → ¬ P (t a) → R.arrow a = 0 := by
    intro a hs ht
    by_contra hn
    exact ht (hs.trans (hinc a hn))
  have hback : ∀ a, ¬ P (s a) → P (t a) → R.arrow a = 0 := by
    intro a hs ht
    by_contra hn
    exact hs (ht.trans (hinc a hn).symm)
  have hp : 0 < ∑ w, if P w then d w else 0 := by
    have hsingle : (if P u then d u else 0) ≤ ∑ w, if P w then d w else 0 :=
      Finset.single_le_sum (fun w _ => Nat.zero_le (if P w then d w else 0))
        (Finset.mem_univ u)
    have hpu : P u := SimpleGraph.Reachable.refl u
    rw [ite_eq_left hpu] at hsingle
    exact lt_of_lt_of_le (hpos u) hsingle
  have hn : 0 < ∑ w, if P w then 0 else d w := by
    have hsingle : (if P v then 0 else d v) ≤ ∑ w, if P w then 0 else d w :=
      Finset.single_le_sum (fun w _ => Nat.zero_le (if P w then 0 else d w))
        (Finset.mem_univ v)
    rw [ite_eq_right huv] at hsingle
    exact lt_of_lt_of_le (hpos v) hsingle
  exact stable_no_disconnected_cut R θ hR P hcut hback hp hn

theorem stable_positive_support_connected {V A : Type} [Fintype V] [Nonempty V]
    {s t : A → V} {d : V → ℕ} (R : Representation s t d) (θ : V → ℤ)
    (hR : Stable θ R) (hpos : ∀ v, 0 < d v) (G : SimpleGraph V)
    (hinc : ∀ a, R.arrow a ≠ 0 → G.Reachable (s a) (t a)) : G.Connected :=
  ⟨stable_positive_support_preconnected R θ hR hpos G hinc⟩

end KroneckerFiniteQuiverHom

namespace KroneckerSparseBlockQuiver
open Module KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedSubrepEquivalence KroneckerFiniteQuiverHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Applied to the actual block support, with no assumed graph connectivity. -/
theorem stable_block_support_connected (B : LinearCoverBlock) [Nonempty (Vertex B)]
    (hB : BlockKingStable B) (hpos : ∀ s, 0 < finrank ℂ (B.Space s)) :
    (supportGraph B).Connected := by
  classical
  apply stable_positive_support_connected (coordinateRepresentation B) (kingWeight B)
    ((coordinateRepresentation_stable_iff B).mpr hB)
  · intro v
    cases v with
    | inl s => exact hpos s
    | inr t => simp [vertexSpace, Module.finrank_self]
  · intro a _
    have ha : (supportGraph B).Adj (source B a) (target B a) := a.2.2
    exact ha.reachable

end KroneckerSparseBlockQuiver
end
