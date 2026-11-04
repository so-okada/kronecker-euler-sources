import KroneckerPaperNodes

/-! Prefix-count contracts for an arbitrary assigned ending occurrence.
`Fin n` value `i` represents manuscript edge `U_{i+1}`; boundaries are unchanged.
No saturation or node hypothesis is imposed on the owner of the ending edge. -/
set_option autoImplicit false
namespace KroneckerPrecursorPrefixHelpers
noncomputable section
open KroneckerStack KroneckerPredecessor

theorem prefix_counts {n k l : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n) (hkl : k ≤ l) (hln : l ≤ n) (x : Fin n) :
    load U p 0 x = 0 ∧ load U p k x ≤ load U p l x ∧
      load U p l x ≤ (U x).grade :=
  ⟨load_zero U p x, load_mono U p hkl x, load_le_grade U p hp hln x⟩

theorem saturated_prefix {n k l : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n) (x : Fin n) (hs : load U p k x = (U x).grade)
    (hkl : k ≤ l) (hln : l ≤ n) :
    (∀ w ∈ assignedEdges U p x, w.val < k) ∧ load U p l x = (U x).grade := by
  constructor
  · intro w hw
    obtain ⟨hwV, hw⟩ := mem_assignedEdges.mp hw
    exact assigned_lt_of_saturated_prefix hp hs hwV hw
  · have hm := load_mono U p hkl x
    have hb := load_le_grade U p hp hln x
    omega

theorem before_assigned {n k : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n) {x v : Fin n} (hv : ¬ IsHorizontal U v)
    (hassign : p v = x) (hk : k ≤ v.val) :
    x.val < v.val ∧ load U p k x < (U x).grade ∧
      (1 : ℤ) ≤ (U x).grade - (load U p k x : ℤ) := by
  obtain ⟨_, hprior, hcap, _⟩ := hp v v.isLt hv
  rw [hassign] at hprior hcap
  have hm := load_mono U p hk x
  exact ⟨hprior, by omega, by omega⟩

theorem assignments_between {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n) {x v w : Fin n} (hv : ¬ IsHorizontal U v)
    (hassign : p v = x) (hxw : x.val < w.val) (hwv : w.val ≤ v.val)
    (hw : ¬ IsHorizontal U w) :
    IsHorizontal U (p w) ∧ x.val ≤ (p w).val ∧ (p w).val < w.val := by
  have hx := (hp v v.isLt hv).1
  rw [hassign] at hx
  obtain ⟨hwH, hprior, _, hlast⟩ := hp w w.isLt hw
  exact ⟨hwH, hlast x hx hxw (before_assigned hp hv hassign hwv).2.1, hprior⟩

theorem interior_saturated {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n) {x v y : Fin n} (hv : ¬ IsHorizontal U v)
    (hassign : p v = x) (hy : IsHorizontal U y)
    (hxy : x.val < y.val) (hyv : y.val < v.val) :
    load U p v.val y = (U y).grade ∧ load U p n y = (U y).grade ∧
      (∀ w ∈ assignedEdges U p y, y.val < w.val ∧ w.val < v.val) := by
  have hs : load U p v.val y = (U y).grade := by
    have hle := load_le_grade U p hp (Nat.le_of_lt v.isLt) y
    by_contra hne
    have hlt : load U p v.val y < (U y).grade := by omega
    have hlast := (hp v v.isLt hv).2.2.2 y hy hyv hlt
    rw [hassign] at hlast
    omega
  have hfull := (saturated_prefix hp y hs (Nat.le_of_lt v.isLt) le_rfl).2
  refine ⟨hs, hfull, ?_⟩
  intro w hw
  obtain ⟨hwV, hw⟩ := mem_assignedEdges.mp hw
  have hprior := (hp w w.isLt hwV).2.1
  rw [hw] at hprior
  exact ⟨hprior, assigned_lt_of_saturated_prefix hp hs hwV hw⟩

theorem interior_max_node {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n) {x v y : Fin n} (hv : ¬ IsHorizontal U v)
    (hassign : p v = x) (hy : IsHorizontal U y)
    (hxy : x.val < y.val) (hyv : y.val < v.val) (hg : 0 < (U y).grade) :
    ∃ hF : (assignedEdges U p y).Nonempty,
      IsNode U p y ((assignedEdges U p y).max' hF) ∧
      y.val < ((assignedEdges U p y).max' hF).val ∧
      ((assignedEdges U p y).max' hF).val < v.val := by
  classical
  obtain ⟨hs, hfull, hbounds⟩ := interior_saturated hp hv hassign hy hxy hyv
  have hF : (assignedEdges U p y).Nonempty := by
    apply Finset.card_pos.mp
    rw [← load_eq_card_assigned, hfull]
    exact hg
  have hm := Finset.max'_mem (assignedEdges U p y) hF
  obtain ⟨hV, ha⟩ := mem_assignedEdges.mp hm
  refine ⟨hF, ⟨hy, hV, ha, hfull, ?_⟩, hbounds _ hm⟩
  intro w hwV hw
  exact Finset.le_max' _ w (mem_assignedEdges.mpr ⟨hwV, hw⟩)

#print axioms prefix_counts
#print axioms saturated_prefix
#print axioms before_assigned
#print axioms assignments_between
#print axioms interior_saturated
#print axioms interior_max_node
end
end KroneckerPrecursorPrefixHelpers
