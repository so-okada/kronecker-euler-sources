import KroneckerPositiveFlowBoundary
import KroneckerChainLocalSlotClasses
import KroneckerColoredShell
import KroneckerFiberBudget

/-! Focused correspondence lemmas for the five definition-review corrections.
The manuscript's source set J is C here; its sink set I is B.
Chain index t : Fin n denotes manuscript z_(t.val+1), and n=c-1.
The first ordered mark is indexed by false, the second by true.
The existing shellPath takes an arbitrary path word, without a grading.
-/
noncomputable section
open Classical
open scoped BigOperators
set_option autoImplicit false
namespace KroneckerManuscriptFiveIssueCorrections

open KroneckerBipartiteIncidence KroneckerReflectedSourceGeneration
open KroneckerFlowBoundaryIdentity

/-- A nonempty proper vertex subset closed under source-to-sink adjacency
has an edge from an outside source to an inside sink. -/
theorem source_closed_boundary_exists {S T : Type*} [Fintype S] [Fintype T]
    (R : S → T → Prop) (hc : (incidenceGraph R).Connected)
    (C : Finset S) (B : Finset T) (hne : C.Nonempty ∨ B.Nonempty)
    (hclosed : ∀ s ∈ C, ∀ t, R s t → t ∈ B)
    (hproper : ¬(C = Finset.univ ∧ B = Finset.univ)) :
    ∃ s, s ∉ C ∧ ∃ t, t ∈ B ∧ R s t := by
  by_contra hcut
  push Not at hcut
  let P : S ⊕ T → Prop := fun v => match v with
    | .inl s => s ∈ C
    | .inr t => t ∈ B
  have hp : ∀ u v, (incidenceGraph R).Adj u v → P u → P v := by
    intro u v huv hu
    cases u with
    | inl s => cases v with
      | inl s' => exact False.elim huv
      | inr t => exact hclosed s hu t huv
    | inr t => cases v with
      | inr t' => exact False.elim huv
      | inl s =>
        by_contra hs
        exact hcut s hs t hu huv
  have hall : ∀ v, P v := by
    rcases hne with ⟨s,hs⟩ | ⟨t,ht⟩
    · exact fun v => reachable_closed P hp hs (hc (.inl s) v)
    · exact fun v => reachable_closed P hp ht (hc (.inr t) v)
  exact hproper ⟨Finset.eq_univ_of_forall (fun s => hall (.inl s)),
    Finset.eq_univ_of_forall (fun t => hall (.inr t))⟩

/-- Lemma 7.27(3), in the finite bipartite incidence model.
The edge flow is extended by zero to nonincident source/sink pairs. -/
theorem source_closed_flow_difference_positive {S T : Type*}
    [Fintype S] [Fintype T]
    (R : S → T → Prop) (hc : (incidenceGraph R).Connected)
    (f : S → T → ℝ) (hzero : ∀ s t, ¬R s t → f s t = 0)
    (hpos : ∀ s t, R s t → 0 < f s t)
    (C : Finset S) (B : Finset T) (hne : C.Nonempty ∨ B.Nonempty)
    (hclosed : ∀ s ∈ C, ∀ t, R s t → t ∈ B)
    (hproper : ¬(C = Finset.univ ∧ B = Finset.univ)) :
    0 < (∑ t ∈ B, ∑ s, f s t) - (∑ s ∈ C, ∑ t, f s t) := by
  have hf : ∀ s t, 0 ≤ f s t := by
    intro s t
    by_cases h : R s t
    · exact le_of_lt (hpos s t h)
    · rw [hzero s t h]
  have hz : ∀ s ∈ C, ∀ t ∉ B, f s t = 0 := by
    intro s hs t ht
    exact hzero s t (fun h => ht (hclosed s hs t h))
  rw [boundary_demand_difference f C B hz]
  obtain ⟨s,hs,t,ht,hst⟩ := source_closed_boundary_exists R hc C B hne hclosed hproper
  exact boundary_flux_positive f C B hf s t hs ht (hpos s t hst)

open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainPortColors
open KroneckerChainNeighborIndices KroneckerChainSlotAssignments

/-- The first mark receives the preceding source's right edge; the second
receives the following source's left edge. No color inequality is assumed. -/
theorem internal_mark_sources {n : ℕ} (t : Fin n) :
    (internalNeighbors t false).val = t.castSucc ∧
    (internalNeighbors t true).val = t.succ := by
  constructor <;> rfl

theorem internal_mark_colors {n : ℕ} (σ : ColorChoices n) (t : Fin n) :
    neighborColors σ (internalBlock t) (internalNeighbors t false) = σ t.castSucc 2 ∧
    neighborColors σ (internalBlock t) (internalNeighbors t true) = σ t.succ 0 :=
  internal_neighbor_colors σ t

/-- The actual gluing assignment attaches the two ordered slots to these
incident sources, including the case of equal slot colors. -/
theorem internal_mark_attachments {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (t : Fin n) :
    (familyAssignment M).slot t.castSucc (internalBlock t) (internalNeighbors t false).property =
      (M (internalBlock t)).2.val (internalNeighbors t false) ∧
    (familyAssignment M).slot t.succ (internalBlock t) (internalNeighbors t true).property =
      (M (internalBlock t)).2.val (internalNeighbors t true) := by
  constructor <;> rfl

theorem internal_marks_distinct {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (t : Fin n) :
    (M (internalBlock t)).2.val (internalNeighbors t false) ≠
      (M (internalBlock t)).2.val (internalNeighbors t true) := by
  intro h
  exact Bool.false_ne_true ((internalNeighbors t).injective ((M (internalBlock t)).2.property.1 h))

open KroneckerColoredShell KroneckerWordCounts KroneckerFiberBudget

theorem zero_budget_parameters (m K A D : ℕ) (h : K + A + (m+1)*D ≤ 0) :
    K = 0 ∧ A = 0 ∧ D = 0 := by
  have : D ≤ (m+1)*D := by nlinarith
  omega

/-- Proposition 4.10 when P=0. There are no edits or outer runs; the target
is the preserving unary shell. Translation is handled by the manuscript's
existing word-reindexing lemma. -/
theorem zero_budget_composition (m u v ν K A D : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (U : List Bool) (hbudget : K + A + (m+1)*D ≤ 0) :
    ∃ Φ : ConnectedColorings m U 0 → ConnectedColorings m (shellPath u v U) 0,
      Function.Injective Φ ∧ fiberBudget m ν D = 1 := by
  have hD := (zero_budget_parameters m K A D hbudget).2.2
  exact ⟨unaryShell u v 0 hm hu hv U, unaryShell_injective u v 0 hm hu hv U,
    hD ▸ fiberBudget_zero m ν⟩

/-- The coefficient used in the three-arrow deletion bound. -/
theorem three_arrow_fiber_budget (ν D : ℕ) :
    fiberBudget 3 ν D = (ν+D).choose D * 64^D := by
  simp only [fiberBudget]
  have h : 2^(2*3*D) = (2^6)^D := by rw [←pow_mul]
  rw [h]
  norm_num

end KroneckerManuscriptFiveIssueCorrections
