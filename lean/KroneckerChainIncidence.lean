import KroneckerTreeGluingCriterion
import KroneckerGluedSupportTree

/- Original module: KroneckerThreeBlockStar -/
section
set_option autoImplicit false
namespace KroneckerThreeBlockStar
open SimpleGraph KroneckerBipartiteIncidence KroneckerLinearCoverBlocks
open KroneckerGluingKingWeight KroneckerTreeGluingCriterion KroneckerGluedSubrepEquivalence
open KroneckerIncidenceDivergence KroneckerSkeletonFlowExistence KroneckerFlowEdgeExtension
open KroneckerGluedLinearRepresentation KroneckerGluedSupportTree
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def starIncidence : Unit → Fin 3 → Prop := fun _ _ => True

theorem star_degree (i : Unit) : Fintype.card {j // starIncidence i j}=3 := by
  calc
    Fintype.card {j // starIncidence i j} = Fintype.card (Fin 3) :=
      Fintype.card_congr ⟨Subtype.val, fun j => ⟨j, True.intro⟩,
        fun _ => rfl, fun _ => rfl⟩
    _ = 3 := Fintype.card_fin 3

theorem star_connected : (incidenceGraph starIncidence).Connected := by
  have hr : ∀ v,(incidenceGraph starIncidence).Reachable (.inl ()) v := by
    intro v
    cases v with
    | inl i => cases i; exact Reachable.refl _
    | inr j => exact (show (incidenceGraph starIncidence).Adj (.inl ()) (.inr j) from True.intro).reachable
  exact { preconnected := fun u v => (hr u).symm.trans (hr v), nonempty := ⟨.inl ()⟩ }

theorem star_tree : (incidenceGraph starIncidence).IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨star_connected,?_⟩
  rw [Nat.card_eq_fintype_card,←edgeFinset_card,incidence_edgeFinset_count,
    KroneckerTreeFlowUniqueness.incidence_edge_count]
  simp [star_degree]

noncomputable def starSlope (a : Fin 3 → ℕ) : ℝ := ((∑ j,a j : ℕ)+1)/2
noncomputable def starFlow (a : Fin 3 → ℕ) (e : Edge starIncidence) : ℝ := starSlope a-a e.1.2

theorem star_flow_equations (a : Fin 3 → ℕ) : FlowEquations (starSlope a) a (starFlow a) := by
  have hx : 2*starSlope a=(∑ j,(a j : ℝ))+1 := by simp [starSlope,Nat.cast_sum]; ring
  constructor
  · intro i
    simp only [extendFlow,starIncidence,starFlow]
    norm_num
    linarith
  · intro j
    simp [extendFlow,starIncidence,starFlow]

theorem star_slope_positive_iff (a : Fin 3 → ℕ) (j : Fin 3) :
    0<starSlope a-(a j : ℝ) ↔ 2*a j<(∑ k,a k)+1 := by
  have hx : 2*starSlope a=(∑ k,(a k : ℝ))+1 := by simp [starSlope,Nat.cast_sum]; ring
  have hc : (2 : ℝ)*a j<(∑ k,(a k : ℝ))+1 ↔ 2*a j<(∑ k,a k)+1 := by
    norm_cast
  rw [←hc]
  constructor <;> intro h <;> linarith

/-- A nonuniform three-block family is stable exactly under the three strict
triangle inequalities on its block source dimensions. -/
theorem three_block_stability_iff (B : Fin 3 → LinearCoverBlock)
    (attach : ∀ i j,starIncidence i j → (B j).Sink)
    (hdef : ∀ j,PositiveDefect (B j)) (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1) :
    BlockKingStable (gluedBlock B starIncidence attach) ↔
      ∀ j,2*sourceDimension (B j)<(∑ k,sourceDimension (B k))+1 := by
  let a := fun j => sourceDimension (B j)
  have hx : slopeParameter (I:=Unit) B=starSlope a := by
    norm_num [slopeParameter,totalSource,starSlope,a]
  have hf : FlowEquations (slopeParameter (I:=Unit) B) a (starFlow a) := by
    rw [hx]; exact star_flow_equations a
  rw [global_stability_iff,tree_flow_stability_criterion B starIncidence attach star_tree star_degree hdef hdim _ hf]
  constructor
  · intro h j
    exact (star_slope_positive_iff a j).mp (h ⟨((),j),trivial⟩)
  · intro h e
    exact (star_slope_positive_iff a e.1.2).mpr (h e.1.2)

end KroneckerThreeBlockStar
end

/- Original module: KroneckerChainIncidence -/
section
set_option autoImplicit false
namespace KroneckerChainIncidence
open KroneckerBipartiteIncidence
attribute [local instance] Classical.propDecidable

/-- There are `n+1` connectors, `n+2` axial blocks, and one middle block
at each connector. The case `n=0` is the three-leaf star. -/
abbrev Connector (n : ℕ) := Fin (n+1)
abbrev Block (n : ℕ) := Fin (n+2) ⊕ Fin (n+1)

def incidence {n : ℕ} (i : Connector n) : Block n → Prop
  | .inl j => j=i.castSucc ∨ j=i.succ
  | .inr j => j=i

def portBlock {n : ℕ} (i : Connector n) (p : Fin 3) : Block n :=
  if p=0 then .inl i.castSucc else if p=1 then .inr i else .inl i.succ

theorem port_incident {n : ℕ} (i : Connector n) (p : Fin 3) :
    incidence i (portBlock i p) := by
  fin_cases p <;> simp [portBlock,incidence]

theorem port_injective {n : ℕ} (i : Connector n) :
    Function.Injective (portBlock i) := by
  intro p q h
  fin_cases p <;> fin_cases q <;> simp_all [portBlock]
  all_goals have hh := congrArg Fin.val h; simp at hh

theorem incident_iff_port {n : ℕ} (i : Connector n) (j : Block n) :
    incidence i j ↔ ∃ p,portBlock i p=j := by
  constructor
  · cases j with
    | inl j =>
      rintro (rfl|rfl)
      · exact ⟨0,by simp [portBlock]⟩
      · exact ⟨2,by simp [portBlock]⟩
    | inr j =>
      intro h
      change j=i at h
      subst j
      exact ⟨1,by simp [portBlock]⟩
  · rintro ⟨p,rfl⟩
    exact port_incident i p

noncomputable def portEquiv {n : ℕ} (i : Connector n) :
    Fin 3 ≃ {j // incidence i j} :=
  Equiv.ofBijective (fun p => ⟨portBlock i p,port_incident i p⟩) ⟨
    fun _ _ h => port_injective i (congrArg Subtype.val h),
    fun j => by
      obtain ⟨p,hp⟩ := (incident_iff_port i j).mp j.2
      exact ⟨p,Subtype.ext hp⟩⟩

theorem connector_degree {n : ℕ} (i : Connector n) :
    Fintype.card {j // incidence i j}=3 := by
  exact (Fintype.card_congr (portEquiv i)).symm

end KroneckerChainIncidence
end
