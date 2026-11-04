import KroneckerChainRecoveredSkeleton

/- Original module: KroneckerChainConnectorAdjacency -/
section
set_option autoImplicit false
namespace KroneckerChainConnectorAdjacency
open KroneckerChainIncidence KroneckerChainBlockNeighbors

def Consecutive {n : ℕ} (i j : Fin (n+1)) : Prop := i.val+1=j.val ∨ j.val+1=i.val

/-- Contracting the degree-two blocks gives the ordinary finite path on the
connectors. The two incidences must be at distinct connectors. -/
theorem common_block_iff_consecutive {n : ℕ} (i k : Connector n) :
    (i≠k ∧ ∃ j,incidence i j ∧ incidence k j) ↔ Consecutive i k := by
  constructor
  · rintro ⟨hne,j,hi,hk⟩
    cases j with
    | inr j => exact False.elim (hne (hi.symm.trans hk))
    | inl j =>
      simp only [incidence,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ] at hi hk
      have hn : i.val≠k.val := fun h => hne (Fin.ext h)
      unfold Consecutive
      omega
  · intro h
    have hn : i≠k := by intro he; subst k; unfold Consecutive at h; omega
    refine ⟨hn,?_⟩
    rcases h with h | h
    · refine ⟨.inl i.succ,Or.inr rfl,Or.inl ?_⟩
      exact Fin.ext h
    · refine ⟨.inl k.succ,Or.inl ?_,Or.inr rfl⟩
      exact Fin.ext h

/-- Between two distinct connectors the connecting block is unique. -/
theorem common_block_unique {n : ℕ} {i k : Connector n} (hne : i≠k)
    {j l : Block n} (hij : incidence i j) (hkj : incidence k j)
    (hil : incidence i l) (hkl : incidence k l) : j=l := by
  have hn : i.val≠k.val := fun h => hne (Fin.ext h)
  cases j with
  | inr j => exact False.elim (hne (hij.symm.trans hkj))
  | inl j => cases l with
    | inr l => exact False.elim (hne (hil.symm.trans hkl))
    | inl l =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [incidence,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ] at hij hkj hil hkl
      omega

end KroneckerChainConnectorAdjacency
end

/- Original module: KroneckerFinitePathRigidity -/
section
set_option autoImplicit false
namespace KroneckerFinitePathRigidity
open KroneckerChainConnectorAdjacency

variable {n : ℕ} (e : Equiv.Perm (Fin (n+1)))
  (h : ∀ i j,Consecutive (e i) (e j) ↔ Consecutive i j)

include h in
theorem path_fixed_zero (hz : e 0=0) : ∀ i,e i=i := by
  have aux : ∀ k (hk : k≤n),e ⟨k,by omega⟩=⟨k,by omega⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hk0 : k=0
      · subst k; exact hz
      let p : Fin (n+1) := ⟨k-1,by omega⟩
      let q : Fin (n+1) := ⟨k,by omega⟩
      have hp : e p=p := ih (k-1) (by omega) (by omega)
      have ha : Consecutive (e p) (e q) := (h p q).mpr (Or.inl (by dsimp [p,q]; omega))
      rw [hp] at ha
      apply Fin.ext
      change (e q).val=k
      rcases ha with ha | ha
      · dsimp [p] at ha; omega
      · by_cases hk1 : k=1
        · dsimp [p] at ha; omega
        · let r : Fin (n+1) := ⟨k-2,by omega⟩
          have hr : e r=r := ih (k-2) (by omega) (by omega)
          have heq : e q=e r := by
            rw [hr]
            apply Fin.ext
            dsimp [p,r] at *
            omega
          have := congrArg Fin.val (e.injective heq)
          dsimp [q,r] at this
          omega
  intro i
  exact aux i.val (by omega)

include h in
theorem path_endpoint : e 0=0 ∨ e 0=Fin.last n := by
  by_contra hn
  have hz : (e 0).val≠0 := by intro hv; exact hn (Or.inl (Fin.ext hv))
  have hl : (e 0).val≠n := by intro hv; exact hn (Or.inr (Fin.ext hv))
  let p : Fin (n+1) := ⟨(e 0).val-1,by omega⟩
  let q : Fin (n+1) := ⟨(e 0).val+1,by omega⟩
  have hp : Consecutive 0 (e.symm p) := (h 0 (e.symm p)).mp (by
    rw [e.apply_symm_apply]; right; dsimp [p]; omega)
  have hq : Consecutive 0 (e.symm q) := (h 0 (e.symm q)).mp (by
    rw [e.apply_symm_apply]; left; rfl)
  have heq : e.symm p=e.symm q := by
    apply Fin.ext
    unfold Consecutive at hp hq
    simp only [Fin.val_zero] at hp hq
    omega
  have hv := congrArg Fin.val (e.symm.injective heq)
  dsimp [p,q] at hv
  omega

end KroneckerFinitePathRigidity
end

/- Original module: KroneckerFinitePathCount -/
section
set_option autoImplicit false
namespace KroneckerFinitePathCount
open KroneckerChainConnectorAdjacency KroneckerFinitePathRigidity
attribute [local instance] Classical.propDecidable

abbrev PathPerm (n : ℕ) := {e : Equiv.Perm (Fin (n+1)) // ∀ i j,Consecutive (e i) (e j) ↔ Consecutive i j}

noncomputable instance (n : ℕ) : Fintype (PathPerm n) := Fintype.ofFinite _

theorem path_determined_by_first {n : ℕ} (e f : PathPerm n) (h0 : e.1 0=f.1 0) : e=f := by
  have h : ∀ i j,Consecutive ((e.1.trans f.1.symm) i) ((e.1.trans f.1.symm) j) ↔ Consecutive i j := by
    intro i j
    have hf := f.2 (f.1.symm (e.1 i)) (f.1.symm (e.1 j))
    simp only [Equiv.apply_symm_apply] at hf
    exact hf.symm.trans (e.2 i j)
  have hz : (e.1.trans f.1.symm) 0=0 := by
    change f.1.symm (e.1 0)=0
    rw [h0,f.1.symm_apply_apply]
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hi := congrArg f.1 (path_fixed_zero _ h hz i)
  simpa using hi

noncomputable def firstCode {n : ℕ} (e : PathPerm n) :
    {i : Fin (n+1) // i=0 ∨ i=Fin.last n} := ⟨e.1 0,path_endpoint e.1 e.2⟩

theorem path_permutation_count (n : ℕ) : Fintype.card (PathPerm n)≤2 := by
  have h := Fintype.card_le_of_injective (firstCode (n:=n)) (by
    intro e f he
    exact path_determined_by_first e f (congrArg Subtype.val he))
  by_cases hn : n=0
  · subst n
    have hc : Fintype.card {i : Fin 1 // i=0 ∨ i=Fin.last 0}≤1 :=
      Fintype.card_subtype_le _
    simp only [←Nat.card_eq_fintype_card] at h hc ⊢
    exact h.trans (hc.trans (by omega))
  · have hne : (0 : Fin (n+1))≠Fin.last n := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_zero,Fin.val_last] at this
      omega
    rw [Fintype.card_subtype_eq_or_eq_of_ne hne] at h
    exact h

end KroneckerFinitePathCount
end

/- Original module: KroneckerChainSkeletonPermutations -/
section
set_option autoImplicit false
namespace KroneckerChainSkeletonPermutations
open Module KroneckerChainIncidence KroneckerChainConnectorAdjacency KroneckerFinitePathCount
open KroneckerChainPortColors KroneckerChainSlotAssignments KroneckerChainRepresentativeIndependence
open KroneckerChainIntrinsicTransport KroneckerChainRecoveredSkeleton KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

abbrev SkeletonPerm (n : ℕ) :=
  {p : Equiv.Perm (Connector n) × Equiv.Perm (Block n) //
    ∀ i j,incidence (p.1 i) (p.2 j) ↔ incidence i j}

noncomputable instance (n : ℕ) : Fintype (SkeletonPerm n) := Fintype.ofFinite _

noncomputable def connectorPath {n : ℕ} (p : SkeletonPerm n) : PathPerm n := ⟨p.1.1,by
  intro i k
  rw [←common_block_iff_consecutive,←common_block_iff_consecutive]
  constructor
  · rintro ⟨hne,j,hij,hkj⟩
    refine ⟨fun he => hne (congrArg p.1.1 he),p.1.2.symm j,?_,?_⟩
    · exact (p.2 _ _).mp (by simpa using hij)
    · exact (p.2 _ _).mp (by simpa using hkj)
  · rintro ⟨hne,j,hij,hkj⟩
    exact ⟨p.1.1.injective.ne hne,p.1.2 j,(p.2 _ _).mpr hij,(p.2 _ _).mpr hkj⟩⟩



noncomputable def recoveredSkeletonPerm {n : ℕ} {d d' : Block n → ℕ}
    {σ τ : ColorChoices n} (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
    (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)
    (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
    (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
      finrank ℂ ((gluedRepresentative M).block.Space s)) : SkeletonPerm n :=
  ⟨(recoveredConnectorEquiv M N hd hd' e he,chainBlockEquiv M N hd hd' e he),
    recovered_chain_incidence M N hd hd' e he⟩

end KroneckerChainSkeletonPermutations
end
