import KroneckerNaturalNodes

/-! Literal compatibility and both shadows from Definition 2.19. First
endpoints are selected by traversal length, including zero-grade edges.
The positive horizontal branch is proved equivalent to the counting core. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths

def E (P : TNEPath) : Set (GeomEdge P) :=
  {e | P.steps.get ((edgeEquiv P).symm e) = true}

def N (P : TNEPath) : Set (GeomEdge P) :=
  {e | P.steps.get ((edgeEquiv P).symm e) = false}

def E_g {P : TNEPath} (g : Grading P) : Set (GeomEdge P) := {e | e ∈ E P ∧ 0 < g e}
def N_g {P : TNEPath} (g : Grading P) : Set (GeomEdge P) := {e | e ∈ N P ∧ 0 < g e}

def HWitness {P : TNEPath} (g : Grading P) (u v t : Edge P) : Prop :=
  edgeEquiv P t ∈ cyclicNE P u v ∧ P.steps.get t = false ∧ t ≠ v ∧
    ((cyclicN P u t).card : ℤ) = ∑ e ∈ cyclicE P u t, (g e : ℤ)

def VWitness {P : TNEPath} (g : Grading P) (u v t : Edge P) : Prop :=
  edgeEquiv P t ∈ cyclicNE P u v ∧ P.steps.get t = true ∧ t ≠ u ∧
    ((cyclicE P t v).card : ℤ) = ∑ e ∈ cyclicN P t v, (g e : ℤ)

def Compatible {P : TNEPath} (g : Grading P) : Prop :=
  ∀ u v : Edge P, P.steps.get u = true → P.steps.get v = false →
    0 < g (edgeEquiv P u) → 0 < g (edgeEquiv P v) →
      ∃ t, HWitness g u v t ∨ VWitness g u v t

@[simp] theorem compatible_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) :
    Compatible (ofBounded g) ↔ KroneckerPaperPathGradings.AmbientCompatible g := Iff.rfl

theorem compatible_iff_core {P : TNEPath} (g : Grading P) :
    Compatible g ↔ KroneckerPaperPathGradings.Compatible (bounded g) :=
  KroneckerPaperPathGradings.ambientCompatible_iff (bounded g)

def HCloses {P : TNEPath} (g : Grading P) (u v : Edge P) : Prop :=
  P.steps.get v = false ∧
    ((cyclicN P u v).card : ℤ) = ∑ e ∈ cyclicE P u v, (g e : ℤ)

def VCloses {P : TNEPath} (g : Grading P) (u v : Edge P) : Prop :=
  P.steps.get u = true ∧
    ((cyclicE P u v).card : ℤ) = ∑ e ∈ cyclicN P u v, (g e : ℤ)

def FirstHShadow {P : TNEPath} (g : Grading P) (u v : Edge P) : Prop :=
  P.steps.get u = true ∧ HCloses g u v ∧
    ∀ w, HCloses g u w → cyclicLength u v ≤ cyclicLength u w

def FirstVShadow {P : TNEPath} (g : Grading P) (u v : Edge P) : Prop :=
  P.steps.get v = false ∧ VCloses g u v ∧
    ∀ w, VCloses g w v → cyclicLength u v ≤ cyclicLength w v

theorem firstH_exists_iff {P : TNEPath} (g : Grading P) (u : Edge P)
    (hu : P.steps.get u = true) : (∃ v, FirstHShadow g u v) ↔ ∃ v, HCloses g u v := by
  constructor
  · rintro ⟨v,hv⟩; exact ⟨v,hv.2.1⟩
  · rintro ⟨v,hv⟩
    have hx : ∃ n, ∃ w, HCloses g u w ∧ cyclicLength u w = n :=
      ⟨cyclicLength u v,v,hv,rfl⟩
    obtain ⟨w,hw,hn⟩ := Nat.find_spec hx
    refine ⟨w,hu,hw,?_⟩
    intro z hz
    rw [hn]
    exact Nat.find_min' hx ⟨z,hz,rfl⟩

theorem firstV_exists_iff {P : TNEPath} (g : Grading P) (v : Edge P)
    (hv : P.steps.get v = false) : (∃ u, FirstVShadow g u v) ↔ ∃ u, VCloses g u v := by
  constructor
  · rintro ⟨u,hu⟩; exact ⟨u,hu.2.1⟩
  · rintro ⟨u,hu⟩
    have hx : ∃ n, ∃ w, VCloses g w v ∧ cyclicLength w v = n :=
      ⟨cyclicLength u v,u,hu,rfl⟩
    obtain ⟨w,hw,hn⟩ := Nat.find_spec hx
    refine ⟨w,hv,hw,?_⟩
    intro z hz
    rw [hn]
    exact Nat.find_min' hx ⟨z,hz,rfl⟩

theorem firstH_unique {P : TNEPath} {g : Grading P} {u v w : Edge P}
    (hv : FirstHShadow g u v) (hw : FirstHShadow g u w) : v = w := by
  have he := Nat.le_antisymm (hv.2.2 w hw.2.1) (hw.2.2 v hv.2.1)
  have hu := u.isLt; have hv' := v.isLt; have hw' := w.isLt
  apply Fin.ext
  unfold cyclicLength at he
  split_ifs at he <;> omega

theorem firstV_unique {P : TNEPath} {g : Grading P} {u w v : Edge P}
    (hu : FirstVShadow g u v) (hw : FirstVShadow g w v) : u = w := by
  have he := Nat.le_antisymm (hu.2.2 w hw.2.1) (hw.2.2 u hu.2.1)
  have hu' := u.isLt; have hv := v.isLt; have hw' := w.isLt
  apply Fin.ext
  unfold cyclicLength at he
  split_ifs at he <;> omega

def t {P : TNEPath} (g : Grading P) (u : Edge P) : Option (Edge P) :=
  if h : ∃ v, FirstHShadow g u v then some h.choose else none

def s {P : TNEPath} (g : Grading P) (v : Edge P) : Option (Edge P) :=
  if h : ∃ u, FirstVShadow g u v then some h.choose else none

theorem t_eq_some {P : TNEPath} {g : Grading P} {u v : Edge P}
    (hv : FirstHShadow g u v) : t g u = some v := by
  have hx : ∃ v, FirstHShadow g u v := ⟨v,hv⟩
  simp only [t, dite_eq_left hx]
  exact congrArg some (firstH_unique hx.choose_spec hv)

theorem s_eq_some {P : TNEPath} {g : Grading P} {u v : Edge P}
    (hu : FirstVShadow g u v) : s g v = some u := by
  have hx : ∃ u, FirstVShadow g u v := ⟨u,hu⟩
  simp only [s, dite_eq_left hx]
  exact congrArg some (firstV_unique hx.choose_spec hu)

def hShadow {P : TNEPath} (g : Grading P) (u : Edge P) : Set (GeomEdge P) :=
  if ∃ v, FirstHShadow g u v then
    {e | ∃ v, FirstHShadow g u v ∧ e ∈ cyclicN P u v}
  else N P

def vShadow {P : TNEPath} (g : Grading P) (v : Edge P) : Set (GeomEdge P) :=
  if ∃ u, FirstVShadow g u v then
    {e | ∃ u, FirstVShadow g u v ∧ e ∈ cyclicE P u v}
  else E P

theorem hShadow_eq_cyclicN {P : TNEPath} {g : Grading P} {u v : Edge P}
    (hv : FirstHShadow g u v) : hShadow g u = (cyclicN P u v : Set (GeomEdge P)) := by
  simp only [hShadow, show (∃ w, FirstHShadow g u w) from ⟨v,hv⟩, ite_true]
  ext e
  constructor
  · rintro ⟨w,hw,he⟩
    rw [firstH_unique hw hv] at he
    exact he
  · intro he; exact ⟨v,hv,he⟩

theorem vShadow_eq_cyclicE {P : TNEPath} {g : Grading P} {u v : Edge P}
    (hu : FirstVShadow g u v) : vShadow g v = (cyclicE P u v : Set (GeomEdge P)) := by
  simp only [vShadow, show (∃ w, FirstVShadow g w v) from ⟨u,hu⟩, ite_true]
  ext e
  constructor
  · rintro ⟨w,hw,he⟩
    rw [firstV_unique hw hu] at he
    exact he
  · intro he; exact ⟨u,hu,he⟩

theorem hShadow_fallback {P : TNEPath} (g : Grading P) (u : Edge P)
    (hx : ¬∃ v, HCloses g u v) : hShadow g u = N P := by
  have hf : ¬∃ v, FirstHShadow g u v := fun ⟨v,hv⟩ => hx ⟨v,hv.2.1⟩
  simp only [hShadow,hf,ite_false]

theorem vShadow_fallback {P : TNEPath} (g : Grading P) (v : Edge P)
    (hx : ¬∃ u, VCloses g u v) : vShadow g v = E P := by
  have hf : ¬∃ u, FirstVShadow g u v := fun ⟨u,hu⟩ => hx ⟨u,hu.2.1⟩
  simp only [vShadow,hf,ite_false]

def Sh {P : TNEPath} (g : Grading P) (e : GeomEdge P) : Set (GeomEdge P) :=
  if e ∈ E P then hShadow g ((edgeEquiv P).symm e)
  else vShadow g ((edgeEquiv P).symm e)

def ShSet {P : TNEPath} (g : Grading P) (C : Set (GeomEdge P)) : Set (GeomEdge P) :=
  {e | ∃ w ∈ C, e ∈ Sh g w}

theorem ShSet_eq_union {P : TNEPath} (g : Grading P) (C : Set (GeomEdge P)) :
    ShSet g C = ⋃ e ∈ C, Sh g e := by
  ext e
  simp only [ShSet, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]

private theorem cyclicIndex_endpoint_prefix {P : TNEPath} (u v w : Edge P)
    (h : cyclicLength u w ≤ cyclicLength u v) :
    cyclicIndex u v ⟨cyclicLength u w-1,by have := cyclicLength_pos u w; omega⟩ = w := by
  apply Fin.ext
  rw [cyclicIndex_val]
  have hu := u.isLt; have hv := v.isLt; have hw := w.isLt
  dsimp only
  unfold cyclicLength
  split_ifs <;> omega

theorem firstH_ofBounded_iff {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) (u v : Edge P)
    (hg : 0 < (g (edgeEquiv P u)).val) :
    FirstHShadow (ofBounded g) u v ↔ KroneckerPaperPathGradings.FirstShadow g u v := by
  rw [← KroneckerPaperPathGradings.ambientFirstShadow_iff]
  constructor
  · rintro ⟨hu,⟨hv,he⟩,hmin⟩
    refine ⟨hu,hg,hv,he,?_⟩
    intro k hk hd heq
    have hle := hmin (cyclicIndex u v k) ⟨hd,heq⟩
    rw [cyclicLength_prefix] at hle
    omega
  · rintro ⟨hu,hg,hv,he,hfirst⟩
    refine ⟨hu,⟨hv,he⟩,?_⟩
    intro w hw
    by_contra hn
    have hlt : cyclicLength u w < cyclicLength u v := by omega
    let k : Fin (cyclicLength u v) := ⟨cyclicLength u w-1,by have := cyclicLength_pos u w; omega⟩
    have hk : cyclicIndex u v k = w := cyclicIndex_endpoint_prefix u v w hlt.le
    have hp := cyclicLength_pos u w
    apply hfirst k (by dsimp [k]; omega)
    · simpa only [hk] using hw.1
    · simpa only [hk, ofBounded] using hw.2

theorem hShadow_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) (u : Edge P)
    (hg : 0 < (g (edgeEquiv P u)).val) :
    hShadow (ofBounded g) u = KroneckerPaperPathGradings.horizontalShadow g u := by
  by_cases hx : ∃ v, FirstHShadow (ofBounded g) u v
  · obtain ⟨v,hv⟩ := hx
    rw [hShadow_eq_cyclicN hv, KroneckerPaperPathGradings.horizontalShadow_eq_cyclicN
      g u v ((firstH_ofBounded_iff g u v hg).mp hv)]
  · have hy : ¬∃ v, KroneckerPaperPathGradings.FirstShadow g u v := by
      rintro ⟨v,hv⟩; exact hx ⟨v,(firstH_ofBounded_iff g u v hg).mpr hv⟩
    simp only [hShadow,hx,ite_false,KroneckerPaperPathGradings.horizontalShadow,hy]
    rfl

def MaximalHShadowSubpath {P : TNEPath} (g : Grading P) (C : CyclicSubpath P) : Prop :=
  0 < g (edgeEquiv P C.first) ∧ FirstHShadow g C.first C.last ∧
    ∀ D : CyclicSubpath P, 0 < g (edgeEquiv P D.first) → FirstHShadow g D.first D.last →
      C.Included D → D.Included C

theorem maximalHShadow_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) (C : CyclicSubpath P) :
    MaximalHShadowSubpath (ofBounded g) C ↔
      KroneckerPaperPathGradings.ShadowComponent g C := by
  constructor
  · rintro ⟨hp,hc,hm⟩
    refine ⟨(firstH_ofBounded_iff g _ _ hp).mp hc,?_⟩
    intro D hd hcd
    have hpD := ((KroneckerPaperPathGradings.ambientFirstShadow_iff g _ _).mpr hd).2.1
    exact hm D hpD ((firstH_ofBounded_iff g _ _ hpD).mpr hd) hcd
  · rintro ⟨hc,hm⟩
    have hp := ((KroneckerPaperPathGradings.ambientFirstShadow_iff g _ _).mpr hc).2.1
    refine ⟨hp,(firstH_ofBounded_iff g _ _ hp).mpr hc,?_⟩
    intro D hd hs hcd
    exact hm D ((firstH_ofBounded_iff g _ _ hd).mp hs) hcd

end KroneckerNaturalPathGradings
