import KroneckerTableIsomorphisms
import KroneckerUnrootedColoredRigidity

/- Original module: KroneckerTableRelabeling -/
section
set_option autoImplicit false
namespace KroneckerTableRelabeling
open KroneckerFiniteColoredTables KroneckerTableIsomorphisms KroneckerColoredIncidenceIso

variable {I J : Type}

def relabel (p : Equiv.Perm I × Equiv.Perm J) (T : ColoredTable I J) : ColoredTable I J where
  code i j := T.code (p.1.symm i) (p.2.symm j)
  atSource := by
    intro i j k d hj hk
    exact p.2.symm.injective (T.atSource _ _ _ d hj hk)
  atSink := by
    intro i k j d hi hk
    exact p.1.symm.injective (T.atSink _ _ _ d hi hk)

noncomputable def relabelIso (p : Equiv.Perm I × Equiv.Perm J) (T : ColoredTable I J) :
    ColoredIso (coloring T) (coloring (relabel p T)) :=
  isoOfCode T (relabel p T) p.1 p.2 (by intro i j; simp [relabel])

instance relabelAction : MulAction (Equiv.Perm I × Equiv.Perm J) (ColoredTable I J) where
  smul := relabel
  one_smul T := by apply table_ext; rfl
  mul_smul p q T := by apply table_ext; rfl

theorem relabel_eq_iff (p : Equiv.Perm I × Equiv.Perm J) (T U : ColoredTable I J) :
    relabel p T=U ↔ ∀ i j,U.code (p.1 i) (p.2 j)=T.code i j := by
  constructor
  · rintro rfl i j; simp [relabel]
  · intro h
    apply table_ext
    funext i j
    simpa [relabel] using (h (p.1.symm i) (p.2.symm j)).symm

theorem table_orbit_iff_iso (T U : ColoredTable I J) :
    (∃ p : Equiv.Perm I × Equiv.Perm J,relabel p T=U) ↔
      Nonempty (ColoredIso (coloring T) (coloring U)) := by
  constructor
  · rintro ⟨p,rfl⟩; exact ⟨relabelIso p T⟩
  · rintro ⟨e⟩
    exact ⟨(e.source,e.sink),(relabel_eq_iff _ T U).mpr (iso_preserves_code T U e)⟩

end KroneckerTableRelabeling
end

/- Original module: KroneckerSaturatedTableAction -/
section
set_option autoImplicit false
namespace KroneckerSaturatedTableAction
open KroneckerFiniteColoredTables KroneckerTableRelabeling KroneckerTableIsomorphisms
open KroneckerBipartiteIncidence KroneckerColoredIncidenceIso KroneckerColoredAutomorphismGroup
open KroneckerUnrootedColoredRigidity
attribute [local instance] Classical.propDecidable

variable (I J : Type) [Fintype I] [Fintype J]

abbrev SaturatedTable := {T : ColoredTable I J // (incidenceGraph (Incidence T)).IsTree ∧
  ∀ i,Fintype.card {j // Incidence T i j}=3}

variable {I J}

def relabelTree (p : Equiv.Perm I × Equiv.Perm J) (T : SaturatedTable I J) : SaturatedTable I J :=
  ⟨relabel p T.1,(relabelIso p T.1).graphIso.isTree_iff.mp T.2.1,by
    intro i
    have hd := (relabelIso p T.1).source_degree (p.1.symm i)
    simpa only [relabelIso,isoOfCode,Equiv.apply_symm_apply] using hd.trans (T.2.2 (p.1.symm i))⟩

instance saturatedRelabelAction : MulAction (Equiv.Perm I × Equiv.Perm J) (SaturatedTable I J) where
  smul := relabelTree
  one_smul T := by apply Subtype.ext; apply table_ext; rfl
  mul_smul p q T := by apply Subtype.ext; apply table_ext; rfl

/-- Relabeling fixes a table only when both vertex permutations are identity. -/
theorem saturated_relabel_free (p : Equiv.Perm I × Equiv.Perm J) (T : SaturatedTable I J)
    (h : p • T=T) : p=1 := by
  have hc := (relabel_eq_iff p T.1 T.1).mp (congrArg Subtype.val h)
  let e := isoOfCode T.1 T.1 p.1 p.2 hc
  have he := unrooted_rigidity (coloring T.1) T.2.1 e
  exact Prod.ext (congrArg ColoredIso.source he) (congrArg ColoredIso.sink he)

omit [Fintype I] in
theorem saturated_orbit_iff_iso (T U : SaturatedTable I J) :
    (∃ p : Equiv.Perm I × Equiv.Perm J,p • T=U) ↔
      Nonempty (ColoredIso (coloring T.1) (coloring U.1)) := by
  constructor
  · rintro ⟨p,h⟩
    exact (table_orbit_iff_iso T.1 U.1).mp ⟨p,congrArg Subtype.val h⟩
  · intro h
    obtain ⟨p,hp⟩ := (table_orbit_iff_iso T.1 U.1).mpr h
    exact ⟨p,Subtype.ext hp⟩

end KroneckerSaturatedTableAction
end
