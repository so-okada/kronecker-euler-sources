import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import KroneckerAlignedOrbitError

/- Original module: KroneckerCompactIndexBound -/
section
set_option autoImplicit false
namespace KroneckerCompactIndexBound
open Set

theorem compact_index_bound {X : Type*} [TopologicalSpace X] (K : Set X)
    (hK : IsCompact K) (U : ℕ → Set X) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x ∈ K, ∃ j, x ∈ U j) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ x ∈ K, ∃ j < Q, x ∈ U j := by
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU (by
    intro x hx
    obtain ⟨j, hj⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨j, hj⟩)
  refine ⟨t.sup id + 1, Nat.succ_pos _, ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨hjt, hxj⟩ := mem_iUnion.mp hj
  exact ⟨j, Nat.lt_succ_of_le (Finset.le_sup (f := id) hjt), hxj⟩

end KroneckerCompactIndexBound
end

/- Original module: KroneckerIrrationalOrbitDensity -/
section
/-! Natural, forward irrational rotations are dense in the unit circle. -/
set_option autoImplicit false
namespace KroneckerIrrationalOrbitDensity

theorem irrational_orbit_dense (r : ℝ) (hr : Irrational r) :
    DenseRange (fun n : ℕ => n • (r : AddCircle (1 : ℝ))) := by
  apply denseRange_zsmul_iff_nsmul.mp
  exact AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hr)

end KroneckerIrrationalOrbitDensity
end

/- Original module: KroneckerTranslatedOrbitDensity -/
section
set_option autoImplicit false
namespace KroneckerTranslatedOrbitDensity
open KroneckerIrrationalOrbitDensity

theorem translated_orbit_dense (r v : ℝ) (hr : Irrational r) :
    DenseRange (fun n : ℕ => ((v + (n : ℝ) * r : ℝ) : AddCircle (1 : ℝ))) := by
  have hd := (Homeomorph.addLeft (v : AddCircle (1 : ℝ))).surjective.denseRange.comp
    (irrational_orbit_dense r hr) (Homeomorph.addLeft (v : AddCircle (1 : ℝ))).continuous
  change DenseRange (fun n : ℕ => (v : AddCircle (1 : ℝ)) + n • (r : AddCircle (1 : ℝ))) at hd
  simpa only [Function.comp_def, ← AddCircle.coe_nsmul,
    nsmul_eq_mul, ← AddCircle.coe_add] using hd

end KroneckerTranslatedOrbitDensity
end

/- Original module: KroneckerOrbitIntervalHit -/
section
set_option autoImplicit false
namespace KroneckerOrbitIntervalHit
open Set KroneckerTranslatedOrbitDensity

theorem orbit_interval_hit (r v a b : ℝ) (hr : Irrational r)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    ∃ j : ℕ, a < Int.fract (v + (j : ℝ) * r) ∧
      Int.fract (v + (j : ℝ) * r) < b := by
  let f : ℝ → AddCircle (1 : ℝ) := fun x => x
  have ho : IsOpen (f '' Ioo a b) := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hn : (f '' Ioo a b).Nonempty := (nonempty_Ioo.mpr hab).image f
  obtain ⟨j, x, hx, hxeq⟩ := (translated_orbit_dense r v hr).exists_mem_open ho hn
  have heq : (x : AddCircle (1 : ℝ)) =
      ((Int.fract (v + (j : ℝ) * r) : ℝ) : AddCircle (1 : ℝ)) := by
    simpa only [AddCircle.coe_fract] using hxeq
  have he : x = Int.fract (v + (j : ℝ) * r) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show x ∈ Ico (0 : ℝ) (0 + 1) by constructor <;> linarith [hx.1, hx.2])
      (show Int.fract (v + (j : ℝ) * r) ∈ Ico (0 : ℝ) (0 + 1) by
        constructor
        · exact Int.fract_nonneg _
        · simpa using Int.fract_lt_one (v + (j : ℝ) * r))).mp heq
  exact ⟨j, he ▸ hx⟩

end KroneckerOrbitIntervalHit
end

/- Original module: KroneckerInteriorPhaseHit -/
section
set_option autoImplicit false
namespace KroneckerInteriorPhaseHit
open KroneckerOrbitIntervalHit

theorem interior_phase_hit (r u v ε : ℝ) (hr : Irrational r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hε : 0 < ε) :
    ∃ j : ℕ, ∃ z : ℤ, 0 < v + (j : ℝ) * r - z ∧
      v + (j : ℝ) * r - z < 1 ∧ |v + (j : ℝ) * r - z - u| < ε := by
  have hab : max 0 (u - ε) < min 1 (u + ε) := by
    apply max_lt <;> apply lt_min <;> linarith
  obtain ⟨j, ha, hb⟩ := orbit_interval_hit r v (max 0 (u - ε))
    (min 1 (u + ε)) hr (le_max_left _ _) (min_le_left _ _) hab
  refine ⟨j, ⌊v + (j : ℝ) * r⌋, ?_, ?_, ?_⟩
  · change 0 < Int.fract (v + (j : ℝ) * r)
    exact lt_of_le_of_lt (le_max_left _ _) ha
  · change Int.fract (v + (j : ℝ) * r) < 1
    exact lt_of_lt_of_le hb (min_le_left _ _)
  · change |Int.fract (v + (j : ℝ) * r) - u| < ε
    have h1 := lt_of_le_of_lt (le_max_right 0 (u - ε)) ha
    have h2 := lt_of_lt_of_le hb (min_le_right 1 (u + ε))
    rw [abs_lt]
    constructor <;> linarith

end KroneckerInteriorPhaseHit
end

/- Original module: KroneckerPhaseWindows -/
section
set_option autoImplicit false
namespace KroneckerPhaseWindows
open Set

def phaseWindow (ε : ℝ) (j : ℕ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | ∃ z : ℤ, 0 < p.2.2 + (j : ℝ) * p.1 - z ∧
    p.2.2 + (j : ℝ) * p.1 - z < 1 ∧
    |p.2.2 + (j : ℝ) * p.1 - z - p.2.1| < ε}

theorem phaseWindow_open (ε : ℝ) (j : ℕ) : IsOpen (phaseWindow ε j) := by
  unfold phaseWindow
  simp only [ofPred_exists]
  apply isOpen_iUnion
  intro z
  have hf : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2 + (j : ℝ) * p.1 - z) := by
    fun_prop
  have hg : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      |p.2.2 + (j : ℝ) * p.1 - z - p.2.1|) := by fun_prop
  exact (isOpen_lt continuous_const hf).inter
    ((isOpen_lt hf continuous_const).inter (isOpen_lt hg continuous_const))

end KroneckerPhaseWindows
end

/- Original module: KroneckerFinitePhaseCover -/
section
set_option autoImplicit false
namespace KroneckerFinitePhaseCover
open Set KroneckerPhaseWindows KroneckerInteriorPhaseHit KroneckerCompactIndexBound

theorem finite_phase_cover (r ε : ℝ) (hr : Irrational r) (hε : 0 < ε) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      ∃ j < Q, (r, (u, v)) ∈ phaseWindow ε j := by
  let K : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1
  let U : ℕ → Set (ℝ × ℝ) := fun j => (fun p => (r, p)) ⁻¹' phaseWindow ε j
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hU : ∀ j, IsOpen (U j) := fun j =>
    (phaseWindow_open ε j).preimage (by fun_prop)
  have hc : ∀ p ∈ K, ∃ j, p ∈ U j := by
    intro p hp
    obtain ⟨j, hj⟩ := interior_phase_hit r p.1 p.2 ε hr hp.1.1 hp.1.2 hε
    exact ⟨j, hj⟩
  obtain ⟨Q, hQ, h⟩ := compact_index_bound K hK U hU hc
  exact ⟨Q, hQ, fun u hu v hv => h (u, v) ⟨hu, hv⟩⟩

end KroneckerFinitePhaseCover
end

/- Original module: KroneckerLiftFractionalPart -/
section
set_option autoImplicit false
namespace KroneckerLiftFractionalPart

theorem lift_fractional_part (x : ℝ) (z : ℤ) (h0 : 0 ≤ x - z) (h1 : x - z < 1) :
    Int.fract x = x - z := by
  have hfloor : ⌊x⌋ = z := Int.floor_eq_iff.mpr (by constructor <;> linarith)
  simp only [Int.fract, hfloor]

end KroneckerLiftFractionalPart
end

/- Original module: KroneckerRobustPhaseCover -/
section
set_option autoImplicit false
namespace KroneckerRobustPhaseCover
open Set Filter KroneckerPhaseWindows KroneckerFinitePhaseCover
open scoped Topology

theorem robust_phase_cover (r ε : ℝ) (hr : Irrational r) (hε : 0 < ε) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - r| < δ →
      ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        ∃ j < Q, (s, (u, v)) ∈ phaseWindow ε j := by
  obtain ⟨Q, hQ, hc⟩ := finite_phase_cover r ε hr hε
  let U : Set (ℝ × (ℝ × ℝ)) := ⋃ j : Fin Q, phaseWindow ε j.val
  have hU : IsOpen U := isOpen_iUnion fun j => phaseWindow_open ε j.val
  have he : ∀ᶠ s in 𝓝 r, ∀ p ∈ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
      (s, p) ∈ U := by
    apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro p hp
    obtain ⟨j, hj, hjp⟩ := hc p.1 hp.1 p.2 hp.2
    exact hU.mem_nhds (mem_iUnion.mpr ⟨⟨j, hj⟩, hjp⟩)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨Q, hQ, δ, hδ, ?_⟩
  intro s hs u hu v hv
  have hs' : s ∈ Metric.ball r δ := by simpa [Real.dist_eq] using hs
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hd hs' (u, v) ⟨hu, hv⟩)
  exact ⟨j.val, j.isLt, hj⟩

end KroneckerRobustPhaseCover
end

/- Original module: KroneckerTwoSlopeAlignment -/
section
set_option autoImplicit false
namespace KroneckerTwoSlopeAlignment

theorem two_slope_alignment (r s t ε : ℝ) (L n : ℕ)
    (hn : n ≤ L) (hs : |s-r| < ε / (4 * ((L : ℝ)+1)))
    (ht : |t-r| < ε / (4 * ((L : ℝ)+1))) :
    (n : ℝ) * |s-t| < ε / 2 := by
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hn' : (n : ℝ) ≤ L := by exact_mod_cast hn
  have hd : |s-t| ≤ |s-r| + |t-r| := by
    calc
      |s-t| = |(s-r)+(r-t)| := by congr 1; ring
      _ ≤ |s-r|+|r-t| := abs_add_le _ _
      _ = |s-r|+|t-r| := by rw [abs_sub_comm r t]
  have hden : 0 < 4 * ((L : ℝ)+1) := by positivity
  have hs' := (lt_div_iff₀ hden).mp hs
  have ht' := (lt_div_iff₀ hden).mp ht
  have hmul := mul_le_mul_of_nonneg_right hd hden.le
  have hnn := mul_le_mul_of_nonneg_right hn' (abs_nonneg (s-t))
  nlinarith [abs_nonneg (s-t)]

end KroneckerTwoSlopeAlignment
end

/- Original module: KroneckerUniformPhaseMatching -/
section
set_option autoImplicit false
namespace KroneckerUniformPhaseMatching
open KroneckerRobustPhaseCover KroneckerPhaseWindows KroneckerLiftFractionalPart

theorem uniform_phase_matching (r ε : ℝ) (hr : Irrational r) (hε : 0 < ε) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - r| < δ →
      ∀ u v : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
        ∃ j < Q, |Int.fract (v + (j : ℝ) * s) - u| < ε := by
  obtain ⟨Q, hQ, δ, hδ, h⟩ := robust_phase_cover r ε hr hε
  refine ⟨Q, hQ, δ, hδ, ?_⟩
  intro s hs u v hu0 hu1 hv0 hv1
  obtain ⟨j, hj, z, hz0, hz1, hz⟩ := h s hs u ⟨hu0, hu1⟩ v ⟨hv0, hv1⟩
  exact ⟨j, hj, by rwa [lift_fractional_part _ z hz0.le hz1]⟩

end KroneckerUniformPhaseMatching
end

/- Original module: KroneckerUniformBlockAlignment -/
section
set_option autoImplicit false
namespace KroneckerUniformBlockAlignment
open KroneckerUniformPhaseMatching KroneckerTwoSlopeAlignment

theorem uniform_block_alignment (r ε : ℝ) (hr : Irrational r) (hε : 0 < ε) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ s t u v : ℝ,
      |s-r| < δ → |t-r| < δ → (0 ≤ u ∧ u < 1) → (0 ≤ v ∧ v < 1) →
      ∀ n ≤ L, ∃ j < Q, |u-Int.fract (v+(j : ℝ)*t)|+(n : ℝ)*|s-t| < ε := by
  obtain ⟨Q,hQ,d,hd,h⟩ := uniform_phase_matching r (ε/2) hr (by positivity)
  refine ⟨Q,hQ,?_⟩
  intro L
  let δ := min d (ε/(4*((L : ℝ)+1)))
  have hδ : 0 < δ := lt_min hd (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro s t u v hs ht hu hv n hn
  obtain ⟨j,hj,hjphase⟩ := h t (lt_of_lt_of_le ht (min_le_left _ _))
    u v hu.1 hu.2.le hv.1 hv.2.le
  have hst := two_slope_alignment r s t ε L n hn
    (lt_of_lt_of_le hs (min_le_right _ _)) (lt_of_lt_of_le ht (min_le_right _ _))
  refine ⟨j,hj,?_⟩
  rw [abs_sub_comm] at hjphase
  linarith

end KroneckerUniformBlockAlignment
end
