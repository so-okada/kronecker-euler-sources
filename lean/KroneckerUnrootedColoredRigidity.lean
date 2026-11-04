import KroneckerFreeActionDivisibility

set_option autoImplicit false
namespace KroneckerUnrootedColoredRigidity
open KroneckerProperColoredReflection KroneckerColoredIncidenceIso KroneckerBipartiteIncidence
open KroneckerColoredAutomorphismGroup KroneckerFreeActionDivisibility SimpleGraph
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem tree_incidence_card {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hT : (incidenceGraph R).IsTree) :
    Fintype.card {p : I × J // R p.1 p.2}+1=Fintype.card I+Fintype.card J := by
  classical
  have hs := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype R)
  rw [Fintype.card_sigma] at hs
  have he := hT.card_edgeFinset
  have hd := (incidenceGraph R).sum_degrees_eq_twice_card_edges
  rw [incidence_degree_sum] at hd
  rw [Fintype.card_sum] at he
  omega

/-- The order of a free automorphism group divides both vertices and edges;
the Euler characteristic of a finite tree forces that order to be one. -/
theorem tree_automorphism_card {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (hT : (incidenceGraph R).IsTree) :
    Fintype.card (ColoredIso C C)=1 := by
  obtain ⟨hi,hj,he⟩ := automorphism_card_divisibility C hT.connected
  have hv := dvd_add hi hj
  rw [←tree_incidence_card R hT] at hv
  apply Nat.eq_one_of_dvd_one
  simpa using Nat.dvd_sub hv he

theorem unrooted_rigidity {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (hT : (incidenceGraph R).IsTree)
    (e : ColoredIso C C) : e=1 := by
  haveI : Subsingleton (ColoredIso C C) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (tree_automorphism_card C hT))
  exact Subsingleton.elim _ _

theorem tree_iso_unique {I J I' J' : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} {R' : I' → J' → Prop}
    {C : ProperColoring R} {C' : ProperColoring R'}
    (hT : (incidenceGraph R).IsTree) (e f : ColoredIso C C') : e=f := by
  have h := unrooted_rigidity C hT (e.trans f.symm)
  apply iso_ext <;> apply Equiv.ext <;> intro x
  · have hx := congrArg (fun g : ColoredIso C C => g.source x) h
    change f.source.symm (e.source x) = x at hx
    exact f.source.symm.injective (hx.trans (f.source.symm_apply_apply x).symm)
  · have hx := congrArg (fun g : ColoredIso C C => g.sink x) h
    change f.sink.symm (e.sink x) = x at hx
    exact f.sink.symm.injective (hx.trans (f.sink.symm_apply_apply x).symm)

end KroneckerUnrootedColoredRigidity
