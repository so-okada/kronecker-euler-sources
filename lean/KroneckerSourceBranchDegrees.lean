import KroneckerLeafDeletedSourceBranch

set_option autoImplicit false
namespace KroneckerSourceBranchDegrees
open KroneckerFiniteColoredTables KroneckerLeafDeletedSourceBranch
open KroneckerBipartiteIncidence KroneckerUnrootedColoredRigidity
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I J : Type} {T : ColoredTable I J} {r : I} {d : Fin 3}

noncomputable def branchSourceColorEquiv (h : IsSourceBranch T r d) (i : I) :
    {j // Incidence T i j} ≃ {e : Fin 3 // i≠r ∨ e≠d} := by
  let f : {j // Incidence T i j} → {e : Fin 3 // i≠r ∨ e≠d} :=
    fun j => ⟨(coloring T).color i j j.2,(h.2 i _).mp ⟨j,code_color T i j j.2⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro j k hjk
    exact (coloring T).at_source i (congrArg Subtype.val hjk)
  · intro e
    obtain ⟨j,hj⟩ := (h.2 i e.1).mpr e.2
    refine ⟨⟨j,⟨e,hj⟩⟩,?_⟩
    apply Subtype.ext
    exact Option.some.inj ((code_color T i j ⟨e,hj⟩).symm.trans hj)

/-- The omitted parent edge lowers precisely the root source degree from three to two. -/
theorem source_branch_degrees [Fintype J] (h : IsSourceBranch T r d) (i : I) :
    Fintype.card {j // Incidence T i j}=if i=r then 2 else 3 := by
  classical
  have hc := Fintype.card_congr (branchSourceColorEquiv h i)
  by_cases hi : i=r
  · simpa [hi] using hc
  · simpa [hi] using hc

/-- A source branch has exactly twice as many retained sinks as sources. -/
theorem source_branch_sink_count [Fintype I] [Fintype J] (h : IsSourceBranch T r d) :
    Fintype.card J=2*Fintype.card I := by
  classical
  have he := tree_incidence_card (Incidence T) h.1
  have hs := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (Incidence T))
  rw [Fintype.card_sigma] at hs
  have hd : ∀ i,Fintype.card {j // Incidence T i j}+(if i=r then 1 else 0)=3 := by
    intro i
    rw [source_branch_degrees h i]
    split_ifs <;> omega
  have ht := congrArg (fun f : I → ℕ => ∑ i,f i) (funext hd)
  simp only [Finset.sum_add_distrib] at ht
  simp at ht
  omega

end KroneckerSourceBranchDegrees
