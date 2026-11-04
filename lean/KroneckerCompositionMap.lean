import KroneckerGeometricPrograms
import KroneckerNaturalPathGradings
import Mathlib.Data.Fintype.EquivFin

/-! Proposition 4.10(1): existence of a map with the stated fibre bound.
This proof extracts a map from the finite cardinal estimate. It proves the
existence statement without identifying the map with the prose construction. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerCompositionMap
open KroneckerPaperPaths KroneckerNaturalPathGradings

theorem map_of_card_le (α β : Type*) [Finite α] [Finite β] (B : ℕ)
    (h : Nat.card α ≤ B*Nat.card β) :
    ∃ f : α → β, ∀ y : β, Nat.card {x : α // f x=y} ≤ B := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card α ≤ Fintype.card (Fin B × β) by
      simpa only [Fintype.card_prod, Fintype.card_fin, Nat.card_eq_fintype_card] using h)
  refine ⟨fun x => (e x).2,fun y => ?_⟩
  let f : {x : α // (e x).2=y} → Fin B := fun x => (e x.val).1
  have hf : Function.Injective f := by
    intro x z hxz
    apply Subtype.ext
    apply e.injective
    exact Prod.ext hxz (x.property.trans z.property.symm)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

instance finiteConnected (m : ℕ) (P : TNEPath) (d : ℕ) :
    Finite (ConnectedColorings m P d) := by
  let e := (connectedColoringEquiv m P d).trans
    ((KroneckerPaperPathGradings.connectedColoringEquiv m P d).trans
      (KroneckerPaperColors.connectedColoringEquiv
        (m := m) (n := P.steps.length) (KroneckerWordCounts.pathShape P.steps) d).symm)
  exact Finite.of_injective e e.injective

theorem geometric_composition_map {m M u v P K A D : ℕ} (hm : 3 ≤ m)
    (hM : M ≤ m-1) (hinsert : 0 < K+A → 4 ≤ m ∧ M ≤ m-2)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
    (rs ts left right : List ℕ) (o q w : LatticePoint)
    (p : EditProgram m (runPath rs o) (runPath ts q) K A D)
    (hl : ∀ r ∈ left, 1 ≤ r ∧ r ≤ M)
    (hr : ∀ r ∈ right, 1 ≤ r ∧ r ≤ M)
    (hll : left.length=P) (hrl : right.length=P)
    (hP : K+A+(m+1)*D ≤ P) :
    ∃ Φ : ConnectedColorings m (runPath rs o) 0 →
        ConnectedColorings m (runPath (left++(u::ts++[v])++right) w) 0,
      ∀ ξ, Nat.card {c // Φ c=ξ} ≤ KroneckerFiberBudget.fiberBudget m rs.length D := by
  apply map_of_card_le
  change connectedCount m (runPath rs o) 0 ≤ _ * connectedCount m _ 0
  simp only [connectedCount_eq_bounded, KroneckerPaperPathGradings.connectedCount_runPath]
  exact KroneckerDeletePrescribedRuns.prescribed_run_count hm hM hinsert hu hv
    rs ts left right p.toRaw hl hr hll hrl hP

end KroneckerCompositionMap
