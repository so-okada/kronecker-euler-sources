import KroneckerWeights

/-! The restriction/extension bijection for a positioned complete shadow.
All colors and support conditions are part of the finite objects. Proving
that every tight grading on the specific maximal Dyck path has this
position is a separate, explicitly recorded manuscript obligation. -/
set_option autoImplicit false
namespace KroneckerTight
open KroneckerStack KroneckerCompatibility KroneckerComponent KroneckerComponentRoots
open KroneckerColoring
open KroneckerWeights

/-- A vertical edge belongs to the horizontal shadow up to and including
its first equality edge: no earlier vertical edge is an equality witness.
If there is no equality in the cyclic traversal, this includes the whole
traversal, as in the definition of horizontal shadow. -/
def InHShadow (E : ℕ → Edge) (u v : ℕ) : Prop :=
  ¬ HWitness E u v

theorem shadow_iff_active {E : ℕ → Edge} {u v : ℕ} (hu : PositiveH E u) :
    InHShadow E u v ↔ Active E u v :=
  ⟨active_of_no_hwitness hu,active_no_hwitness⟩

def ShadowSupport (E : ℕ → Edge) (N : ℕ) : Prop :=
  ∀ v,v<N→PositiveV E v→
    ∃ u,u<N ∧ PositiveH E u ∧ InHShadow E u (if u≤v then v else v+N)

/-- The negative-determinant tight-grading conditions with total vertical
grade a and total horizontal grade b. The path and determinant conditions
enter the enumeration theorem, not these grading predicates. -/
def Tight {m N : ℕ} (shape : ℕ → Bool) (a b : ℤ) (g : Coloring m N) : Prop :=
  CyclicCompatible (trace shape g) N ∧ HTotal shape g=b ∧ VTotal shape g=a ∧
    ShadowSupport (trace shape g) N

def LocatedTight {m n k : ℕ} (shape : ℕ → Bool) (a b : ℤ)
    (g : Coloring m (n+k)) : Prop :=
  Tight shape a b g ∧ RootComponent (trace shape g) n ∧ ZeroOutside g

theorem root_shadow_support {E : ℕ → Edge} {n N : ℕ}
    (hr : RootComponent E n)
    (hz : ∀j,n≤j→j<N→(E j).grade=0) : ShadowSupport E N := by
  intro v hv hvp
  have hvn := positive_inside hz hv (Or.inr hvp)
  refine ⟨0,by have := hr.1; omega,hr.2.1,?_⟩
  rw [ite_eq_left (Nat.zero_le _),shadow_iff_active hr.2.1]
  intro j hj hjv
  simpa [debt,walk] using hr.2.2.2 j hj (by omega)

theorem connected_extends {m n k : ℕ} (shape : ℕ → Bool) (a b : ℤ)
    (hh : HEdges shape n=a+1) (hv : VEdges shape n=b)
    {g : Coloring m n} (hc : Connected m (word shape g) 0) :
    LocatedTight shape a b (extend k g) := by
  have hn := (connected_iff.mp hc).1
  have hword : word shape g=
      KroneckerComponent.segment (trace shape (extend k g)) 0 n := by
    simpa using restrict_word shape (extend k g)
  have hn' := hn
  rw [hword] at hn'
  have hr := node_root_component hn'
  have hz := extend_zero_outside k g
  have hzt := zero_outside_trace shape hz
  have hcompatible := (zero_extension_compatible hr (by omega) hzt).mpr (node_compatible hr hn')
  have ht := node_totals shape g hn
  refine ⟨⟨hcompatible,?_,?_,root_shadow_support hr hzt⟩,hr,hz⟩
  · rw [extend_htotal,ht.1,hv]
  · rw [extend_vtotal]
    have h := ht.2
    rw [hh] at h
    norm_num at h
    omega

theorem located_restricts {m n k : ℕ} (shape : ℕ → Bool) (a b : ℤ)
    (hh : HEdges shape n=a+1)
    {g : Coloring m (n+k)} (ht : LocatedTight shape a b g) :
    Connected m (word shape (restrict g)) 0 := by
  obtain ⟨ht,hr,hz⟩ := ht
  have hcompatible := (zero_extension_compatible hr (by omega) (zero_outside_trace shape hz)).mp ht.1
  have hbounds : ∀ e ∈ KroneckerComponent.segment (trace shape g) 0 n,e.grade≤m := by
    rw [← restrict_word]
    exact word_grade_bounds shape (restrict g)
  obtain ⟨c,hc⟩ := (compatibility_iff_connected hr).mp ⟨hcompatible,hbounds⟩
  rw [← restrict_word] at hc
  have hn := (connected_iff.mp hc).1
  have hcredit := (node_totals shape (restrict g) hn).2
  have htotal : VTotal shape (restrict g)=a := by
    rw [← extend_vtotal shape k (restrict g),extend_restrict hz]
    exact ht.2.2.1
  rw [hh,htotal] at hcredit
  have hc0 : c=0 := by omega
  simpa [hc0] using hc

/-- This bijection has no localization assumption: its target explicitly
consists of tight gradings whose complete shadow is this prefix. -/
def frameEquiv {m n k : ℕ} (shape : ℕ → Bool) (a b : ℤ)
    (hh : HEdges shape n=a+1) (hv : VEdges shape n=b) :
    {g : Coloring m n // Connected m (word shape g) 0} ≃
      {g : Coloring m (n+k) // LocatedTight shape a b g} where
  toFun g := ⟨extend k g.val,connected_extends shape a b hh hv g.property⟩
  invFun g := ⟨restrict g.val,located_restricts shape a b hh g.property⟩
  left_inv g := Subtype.ext (restrict_extend k g.val)
  right_inv g := Subtype.ext (extend_restrict g.property.2.2)

theorem frame_count {m n k : ℕ} (shape : ℕ → Bool) (a b : ℤ)
    (hh : HEdges shape n=a+1) (hv : VEdges shape n=b) :
    Nat.card {g : Coloring m n // Connected m (word shape g) 0} =
      Nat.card {g : Coloring m (n+k) // LocatedTight shape a b g} :=
  Nat.card_congr (frameEquiv shape a b hh hv)

theorem tight_count_weighted {m N : ℕ} (shape : ℕ → Bool) (a b : ℤ) :
    Nat.card {g : Coloring m N // Tight shape a b g}=
      weightedCount (fun d : Grades m N => Tight shape a b (representative d)) :=
  colored_count (fun d => Tight shape a b (representative d))



theorem connected_count_bound {m n c : ℕ} (shape : ℕ → Bool) :
    Nat.card {g : Coloring m n // Connected m (word shape g) c}≤(2^m)^n :=
  (colored_count (fun d => Connected m (word shape (representative d)) c)).trans_le
    (colored_count_bound _)

end KroneckerTight
