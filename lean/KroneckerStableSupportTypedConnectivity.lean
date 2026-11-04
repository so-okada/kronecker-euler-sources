import KroneckerExactDirectSumNormalForm

section

set_option autoImplicit false
namespace KroneckerFiniteQuiverHom
open Module
open scoped BigOperators

def cutSubrep {V A : Type} {s t : A → V} {d : V → ℕ}
    (R : Representation s t d) (P : V → Prop) [DecidablePred P]
    (hcut : ∀ a, P (s a) → ¬ P (t a) → R.arrow a = 0) : Subrep R where
  space v := if P v then ⊤ else ⊥
  invariant := by
    intro a x hx
    by_cases ht : P (t a)
    · simp [ht]
    · by_cases hs : P (s a)
      · simp [ht, hcut a hs ht]
      · have hx0 : x = 0 := by simpa [hs] using hx
        simp [hx0, ht]

theorem cut_size {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    (R : Representation s t d) (P : V → Prop) [DecidablePred P]
    (hcut : ∀ a, P (s a) → ¬ P (t a) → R.arrow a = 0) :
    size (cutSubrep R P hcut) = ∑ v, if P v then d v else 0 := by
  unfold size
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : P v
  · rw [show (cutSubrep R P hcut).space v = ⊤ by simp [cutSubrep, h]]
    simp [h, Space]
  · rw [show (cutSubrep R P hcut).space v = ⊥ by simp [cutSubrep, h]]
    simp [h]

theorem cut_weight {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    (R : Representation s t d) (θ : V → ℤ) (P : V → Prop) [DecidablePred P]
    (hcut : ∀ a, P (s a) → ¬ P (t a) → R.arrow a = 0) :
    weight θ (cutSubrep R P hcut) = ∑ v, if P v then θ v * (d v : ℤ) else 0 := by
  unfold weight
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : P v
  · rw [show (cutSubrep R P hcut).space v = ⊤ by simp [cutSubrep, h]]
    simp [h, Space]
  · rw [show (cutSubrep R P hcut).space v = ⊥ by simp [cutSubrep, h]]
    simp [h]

/-- A stable representation cannot split into two nonzero vertex blocks with
all crossing maps zero. The partition is arbitrary, not coordinate-restricted. -/
theorem stable_no_disconnected_cut {V A : Type} [Fintype V]
    {s t : A → V} {d : V → ℕ} (R : Representation s t d) (θ : V → ℤ)
    (hR : Stable θ R) (P : V → Prop) [DecidablePred P]
    (hcut : ∀ a, P (s a) → ¬ P (t a) → R.arrow a = 0)
    (hback : ∀ a, ¬ P (s a) → P (t a) → R.arrow a = 0)
    (hp : 0 < ∑ v, if P v then d v else 0)
    (hn : 0 < ∑ v, if P v then 0 else d v) : False := by
  classical
  let U := cutSubrep R P hcut
  let W := cutSubrep R (fun v => ¬ P v) (by
    intro a ha hb
    exact hback a ha (not_not.mp hb))
  have hU : size U = ∑ v, if P v then d v else 0 := cut_size R P hcut
  have hW : size W = ∑ v, if P v then 0 else d v := by
    simpa [W] using cut_size R (fun v => ¬ P v) _
  have hsum : size U + size W = ∑ v, d v := by
    rw [hU, hW, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  have hu := hR.2 U (by omega) (by omega)
  have hw := hR.2 W (by omega) (by omega)
  have hweights : weight θ U + weight θ W = 0 := by
    rw [show weight θ U = _ from cut_weight R θ P hcut,
      show weight θ W = _ from cut_weight R θ (fun v => ¬ P v) _,
      ← Finset.sum_add_distrib]
    convert hR.1 using 1
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : P v <;> simp [h]
  omega

end KroneckerFiniteQuiverHom
end

section

/-! King stability forces the actual positive support to be connected by typed
signed walks. This proof allows loops and parallel arrows and does not assume
a graph model or a positive girth bound. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableSupportTypedConnectivity
open KroneckerAbelianCover LabeledWalk KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
open KroneckerAccumulatedDimensionNormalization KroneckerTypedQuiverMaps
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

theorem finite_stable_walk_connected (Q : TypedQuiver) [Fintype Q.V] (d : Q.V → ℕ)
    (R : Representation Q.source Q.target d) (θ : Q.V → ℤ)
    (hR : Stable θ R) (hpos : ∀v, 0 < d v) (r v : Q.V) :
    Nonempty (LabeledWalk Q.source Q.target r v) := by
  by_contra hn
  let P : Q.V → Prop := fun w => Nonempty (LabeledWalk Q.source Q.target r w)
  have hcut : ∀ a, P (Q.source a) → ¬ P (Q.target a) → R.arrow a = 0 := by
    rintro a ⟨p⟩ ht
    exact False.elim (ht ⟨append p (.forward a (.nil _))⟩)
  have hback : ∀ a, ¬ P (Q.source a) → P (Q.target a) → R.arrow a = 0 := by
    rintro a hs ⟨p⟩
    exact False.elim (hs ⟨append p (.backward a (.nil _))⟩)
  have hp : 0 < ∑ w, if P w then d w else 0 := by
    have hs : (if P r then d r else 0) ≤ ∑ w, if P w then d w else 0 :=
      Finset.single_le_sum (fun w _ => Nat.zero_le (if P w then d w else 0)) (Finset.mem_univ r)
    rw [ite_eq_left (show P r from ⟨.nil r⟩)] at hs
    exact (hpos r).trans_le hs
  have hnp : 0 < ∑ w, if P w then 0 else d w := by
    have hs : (if P v then 0 else d v) ≤ ∑ w, if P w then 0 else d w :=
      Finset.single_le_sum (fun w _ => Nat.zero_le (if P w then 0 else d w)) (Finset.mem_univ v)
    rw [ite_eq_right hn] at hs
    exact (hpos v).trans_le hs
  exact stable_no_disconnected_cut R θ hR P hcut hback hp hnp

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

local instance supportQuiverFintype (Q : TypedQuiver) (d : Q.V →₀ ℕ) : Fintype (supportQuiver Q d).V :=
  supportFintype d

theorem stable_connected_dimension (Q : TypedQuiver) (d : Q.V →₀ ℕ) (hd : d ≠ 0)
    (R : Representation Q.source Q.target (fun v => d v)) (θ : Q.V → ℤ)
    (hR : FiniteSupportStable d θ R) : ConnectedDimension Q d := by
  obtain ⟨r,hr⟩ := Finsupp.support_nonempty_iff.mpr hd
  let i : QuiverMap (supportQuiver Q d) Q :=
    ⟨Subtype.val,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  refine ⟨⟨r,hr⟩,?_⟩
  intro v
  obtain ⟨p⟩ := finite_stable_walk_connected (supportQuiver Q d) (supportDimension d)
    (restrictToSupport Q d R) (supportCharacter d θ)
    ((finiteSupportStable_iff_restrict Q d θ R).mp hR)
    (fun w => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp w.property)) ⟨r,hr⟩ v
  exact ⟨i.walk p⟩

end KroneckerStableSupportTypedConnectivity
end
end

