import KroneckerOutgoingSinkBranches

set_option autoImplicit false
namespace KroneckerBranchIsomorphismInvariance
open KroneckerFiniteColoredTables KroneckerColoredIncidenceIso KroneckerTableIsomorphisms
open KroneckerLeafDeletedSourceBranch KroneckerOutgoingSinkBranches

variable {I J I' J' : Type} {T : ColoredTable I J} {U : ColoredTable I' J'}

theorem source_color_transport (e : ColoredIso (coloring T) (coloring U)) (i : I) (d : Fin 3) :
    (∃ j,U.code (e.source i) j=some d) ↔ ∃ j,T.code i j=some d := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨j,rfl⟩ := e.sink.surjective j
    exact ⟨j,(iso_preserves_code T U e i j).symm.trans hj⟩
  · rintro ⟨j,hj⟩
    exact ⟨e.sink j,(iso_preserves_code T U e i j).trans hj⟩

theorem source_branch_iso_iff (e : ColoredIso (coloring T) (coloring U)) (r : I) (d : Fin 3) :
    IsSourceBranch U (e.source r) d ↔ IsSourceBranch T r d := by
  constructor
  · rintro ⟨ht,hc⟩
    refine ⟨e.graphIso.isTree_iff.mpr ht,?_⟩
    intro i c
    simpa only [source_color_transport,e.source.injective.ne_iff] using hc (e.source i) c
  · rintro ⟨ht,hc⟩
    refine ⟨e.graphIso.isTree_iff.mp ht,?_⟩
    intro i c
    obtain ⟨i,rfl⟩ := e.source.surjective i
    simpa only [source_color_transport,e.source.injective.ne_iff] using hc i c

theorem sink_branch_iso_iff (e : ColoredIso (coloring T) (coloring U)) (r : J) (d : Fin 3) :
    IsSinkBranch U (e.sink r) d ↔ IsSinkBranch T r d := by
  constructor
  · rintro ⟨ht,hc,ha⟩
    refine ⟨e.graphIso.isTree_iff.mpr ht,fun i c => (source_color_transport e i c).mp (hc (e.source i) c),?_⟩
    intro i hi
    exact ha (e.source i) ((iso_preserves_code T U e i r).trans hi)
  · rintro ⟨ht,hc,ha⟩
    refine ⟨e.graphIso.isTree_iff.mp ht,?_,?_⟩
    · intro i c
      obtain ⟨i,rfl⟩ := e.source.surjective i
      exact (source_color_transport e i c).mpr (hc i c)
    · intro i hi
      obtain ⟨i,rfl⟩ := e.source.surjective i
      exact ha i ((iso_preserves_code T U e i r).symm.trans hi)

end KroneckerBranchIsomorphismInvariance
