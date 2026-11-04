import KroneckerChainIncidence

set_option autoImplicit false
namespace KroneckerChainBlockNeighbors
open KroneckerChainIncidence
attribute [local instance] Classical.propDecidable

def leftBlock (n : ℕ) : Block n := .inl 0
def rightBlock (n : ℕ) : Block n := .inl (Fin.last (n+1))
def middleBlock {n : ℕ} (i : Connector n) : Block n := .inr i
def internalBlock {n : ℕ} (t : Fin n) : Block n := .inl t.castSucc.succ

theorem left_incidence {n : ℕ} (i : Connector n) :
    incidence i (leftBlock n) ↔ i=0 := by
  simp only [incidence,leftBlock,Fin.ext_iff,Fin.val_zero,Fin.val_castSucc,Fin.val_succ]
  omega

theorem right_incidence {n : ℕ} (i : Connector n) :
    incidence i (rightBlock n) ↔ i=Fin.last n := by
  simp only [incidence,rightBlock,Fin.ext_iff,Fin.val_last,Fin.val_castSucc,Fin.val_succ]
  have hi := i.isLt
  omega

theorem middle_incidence {n : ℕ} (i t : Connector n) :
    incidence i (middleBlock t) ↔ i=t := by
  exact eq_comm

theorem internal_incidence {n : ℕ} (i : Connector n) (t : Fin n) :
    incidence i (internalBlock t) ↔ i=t.castSucc ∨ i=t.succ := by
  simp only [incidence,internalBlock,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
  omega

theorem block_cases {n : ℕ} (j : Block n) :
    j=leftBlock n ∨ j=rightBlock n ∨ (∃ i,j=middleBlock i) ∨ ∃ t,j=internalBlock t := by
  cases j with
  | inr j => exact Or.inr (Or.inr (Or.inl ⟨j,rfl⟩))
  | inl j =>
    refine Fin.cases ?_ (fun i => ?_) j
    · exact Or.inl rfl
    · refine Fin.lastCases ?_ (fun t => ?_) i
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨t,rfl⟩))


theorem internal_degree {n : ℕ} (t : Fin n) :
    Fintype.card {i // incidence i (internalBlock t)}=2 := by
  simp only [internal_incidence]
  apply Fintype.card_subtype_eq_or_eq_of_ne
  intro h
  have hv := congrArg Fin.val h
  simp at hv

end KroneckerChainBlockNeighbors
