import KroneckerColoredLeafTransport

/- Original module: KroneckerColoredFreeActions -/
section
set_option autoImplicit false
namespace KroneckerColoredFreeActions
open KroneckerProperColoredReflection KroneckerColoredIncidenceIso
open KroneckerColoredAutomorphismGroup KroneckerColoredRootRigidity KroneckerBipartiteIncidence

variable {I J : Type} {R : I → J → Prop} (C : ProperColoring R)

def sourceAction : MulAction (ColoredIso C C) I where
  smul e i := e.source i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def sinkAction : MulAction (ColoredIso C C) J where
  smul e j := e.sink j
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def edgeAction : MulAction (ColoredIso C C) {p : I × J // R p.1 p.2} where
  smul e p := ⟨(e.source p.1.1,e.sink p.1.2),(e.incidence _ _).mpr p.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem source_action_free (hR : (incidenceGraph R).Connected) (e : ColoredIso C C)
    (i : I) (h : e.source i=i) : e=1 :=
  (automorphism_eq_one_iff e).mpr (connected_root_rigidity hR e (.inl i) (congrArg Sum.inl h))

theorem sink_action_free (hR : (incidenceGraph R).Connected) (e : ColoredIso C C)
    (j : J) (h : e.sink j=j) : e=1 :=
  (automorphism_eq_one_iff e).mpr (connected_root_rigidity hR e (.inr j) (congrArg Sum.inr h))

theorem edge_action_free (hR : (incidenceGraph R).Connected) (e : ColoredIso C C)
    (p : {p : I × J // R p.1 p.2})
    (h : (edgeAction C).smul e p=p) : e=1 := by
  apply source_action_free C hR e p.1.1
  exact congrArg (fun q => q.1.1) h

end KroneckerColoredFreeActions
end

/- Original module: KroneckerFreeActionDivisibility -/
section
set_option autoImplicit false
namespace KroneckerFreeActionDivisibility

/-- A free action partitions a finite set into copies of the actual group. -/
theorem free_action_card_dvd {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X] (hfree : ∀ g : G,∀ x : X,g • x=x → g=1) :
    Fintype.card G ∣ Fintype.card X := by
  classical
  have hs : ∀ x : X,MulAction.stabilizer G x=⊥ := by
    intro x
    apply le_antisymm _ bot_le
    intro g hg
    exact (Subgroup.mem_bot).mpr (hfree g x hg)
  have hc := Fintype.card_congr (MulAction.selfEquivOrbitsQuotientProd hs)
  rw [Fintype.card_prod] at hc
  exact ⟨Fintype.card (Quotient (MulAction.orbitRel G X)),by simpa [mul_comm] using hc⟩

open KroneckerProperColoredReflection KroneckerColoredIncidenceIso KroneckerBipartiteIncidence
open KroneckerColoredFreeActions KroneckerColoredAutomorphismGroup
attribute [local instance] Classical.propDecidable

theorem automorphism_card_divisibility {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (hR : (incidenceGraph R).Connected) :
    Fintype.card (ColoredIso C C) ∣ Fintype.card I ∧
    Fintype.card (ColoredIso C C) ∣ Fintype.card J ∧
    Fintype.card (ColoredIso C C) ∣ Fintype.card {p : I × J // R p.1 p.2} := by
  refine ⟨?_,?_,?_⟩
  · let := sourceAction C
    exact free_action_card_dvd (source_action_free C hR)
  · let := sinkAction C
    exact free_action_card_dvd (sink_action_free C hR)
  · let := edgeAction C
    exact free_action_card_dvd (edge_action_free C hR)

end KroneckerFreeActionDivisibility
end
