import KroneckerChainLatticeParameters
import KroneckerFiniteStableChainFamily

/- Original module: KroneckerLatticeParameterRecovery -/
section
set_option autoImplicit false
namespace KroneckerLatticeParameterRecovery
open KroneckerChainLatticeParameters KroneckerFiniteStateBins KroneckerChainIncidence
open KroneckerChainBinRecovery

/-- Equal bounded flow values recover every state, bin and integer lattice index. -/
theorem lattice_parameter_recovery {n : ℕ} {x : ℝ} (hx : 0<x)
    (p q : LatticeParameter n x)
    (hl : ∀ t≤n,leftFlow p.2 t=leftFlow q.2 t)
    (hr : ∀ t≤n,rightFlow p.2 t=rightFlow q.2 t) : p=q := by
  rcases p with ⟨⟨i,h⟩,l,r⟩
  rcases q with ⟨⟨j,k⟩,L,R⟩
  have D := lattice_parameter_bins (P:=⟨i,h⟩) (l,r)
  have E := lattice_parameter_bins (P:=⟨j,k⟩) (L,R)
  have hi : i=j := by
    funext t
    have he := hl t (by omega)
    have hs := bin_index_unique x (leftFlow (P:=⟨i,h⟩) (l,r) t) _ _ hx
      (D.left_bin t (by omega)) (he.symm ▸ E.left_bin t (by omega))
    simp only [stateFunction,extend_at,stateValue] at hs
    exact Fin.ext (Nat.add_right_cancel hs)
  cases hi
  have hh : h=k := by
    funext t
    have he := hr t.castSucc (by have ht := t.isLt; simp only [Fin.val_castSucc]; omega)
    have hs := bin_index_unique x (rightFlow (P:=⟨i,h⟩) (l,r) t.castSucc) _ _ hx
      (D.right_bin t.castSucc (by omega)) (he.symm ▸ E.right_bin t.castSucc (by omega))
    simp only [binFunction,extend_at,rightBin,Fin.lastCases_castSucc] at hs
    exact Fin.ext hs
  cases hh
  have hl' : l=L := by
    funext t
    apply Subtype.ext
    have he := hl t (by omega)
    simp only [leftFlow,extend_at] at he
    exact_mod_cast add_left_cancel he
  have hr' : r=R := by
    funext t
    apply Subtype.ext
    have he := hr t (by omega)
    simp only [rightFlow,extend_at] at he
    exact_mod_cast add_left_cancel he
  cases hl'
  cases hr'
  rfl

end KroneckerLatticeParameterRecovery
end

/- Original module: KroneckerLatticeDimensionEmbedding -/
section
set_option autoImplicit false
namespace KroneckerLatticeDimensionEmbedding
open KroneckerChainLatticeParameters KroneckerLatticeParameterRecovery
open KroneckerFiniteChainInputs KroneckerFiniteStableChainFamily
open KroneckerChainBlockSizes

noncomputable def parameterDimensions {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) (p : LatticeParameter n x) : DimensionData n a :=
  (lattice_flow_enters_family n a x (leftFlow p.2) (rightFlow p.2)
    (stateFunction p.1) (binFunction p.1) hx ha (lattice_parameter_bins p.2)
    (lattice_parameter_integrality p.2).1 (lattice_parameter_integrality p.2).2).choose

theorem parameter_dimensions_spec {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) (p : LatticeParameter n x) :
    (∀ j,(dimensions (parameterDimensions hx ha p) j : ℝ)=
      blockSize n x (leftFlow p.2) (rightFlow p.2) j) ∧ BinCompatible (parameterDimensions hx ha p) :=
  (lattice_flow_enters_family n a x (leftFlow p.2) (rightFlow p.2)
    (stateFunction p.1) (binFunction p.1) hx ha (lattice_parameter_bins p.2)
    (lattice_parameter_integrality p.2).1 (lattice_parameter_integrality p.2).2).choose_spec

/-- The actual block dimensions distinguish every enumerated lattice parameter. -/
theorem parameter_dimensions_injective {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) : Function.Injective (parameterDimensions hx ha) := by
  intro p q hpq
  have hd : blockSize n x (leftFlow p.2) (rightFlow p.2)=
      blockSize n x (leftFlow q.2) (rightFlow q.2) := by
    funext j
    rw [←(parameter_dimensions_spec hx ha p).1 j,←(parameter_dimensions_spec hx ha q).1 j,hpq]
  have hf := block_sizes_recover_flows n x (leftFlow p.2) (rightFlow p.2)
    (leftFlow q.2) (rightFlow q.2) hd
  exact lattice_parameter_recovery (by linarith) p q (fun t ht => (hf t ht).1) (fun t ht => (hf t ht).2)

end KroneckerLatticeDimensionEmbedding
end

/- Original module: KroneckerMarkedLatticeInputs -/
section
set_option autoImplicit false
namespace KroneckerMarkedLatticeInputs
open KroneckerChainLatticeParameters KroneckerLatticeDimensionEmbedding
open KroneckerFiniteChainInputs KroneckerFiniteStableChainFamily
open KroneckerChainLocalSlotClasses KroneckerChainPortColors KroneckerChainIncidence
attribute [local instance] Classical.propDecidable

abbrev MarkedLatticeInput {n a : ℕ} {x : ℝ} (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) :=
  Σ p : LatticeParameter n x,Σ σ : ColorChoices n,FamilyClass (dimensions (parameterDimensions hx ha p)) σ

noncomputable instance {n a : ℕ} {x : ℝ} (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) :
    Fintype (MarkedLatticeInput hx ha) := Fintype.ofFinite _

noncomputable def toChainInput {n a : ℕ} {x : ℝ} {hx : 100000≤x} {ha : ((n : ℝ)+2)*x=a}
    (X : MarkedLatticeInput hx ha) : ChainInput n a := ⟨parameterDimensions hx ha X.1,X.2⟩

theorem marked_input_injective {n a : ℕ} {x : ℝ} (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) :
    Function.Injective (toChainInput (hx:=hx) (ha:=ha)) := by
  rintro ⟨p,X⟩ ⟨q,Y⟩ he
  have hpq := parameter_dimensions_injective hx ha (congrArg Sigma.fst he)
  cases hpq
  have hXY : X=Y := by
    simpa only [toChainInput,Sigma.mk.inj_iff,heq_eq_eq,true_and] using he
  cases hXY
  rfl

theorem marked_input_stable {n a : ℕ} {x : ℝ} {hx : 100000≤x} {ha : ((n : ℝ)+2)*x=a}
    (X : MarkedLatticeInput hx ha) : toChainInput X∈stableInputs n a := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(parameter_dimensions_spec hx ha X.1).2⟩

/-- Actual marked classes, summed over every lattice parameter and connector coloring. -/
theorem marked_lattice_card {n a : ℕ} {x : ℝ} (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) :
    Fintype.card (MarkedLatticeInput hx ha)=
      ∑ p : LatticeParameter n x,∑ σ : ColorChoices n,
        ∏ j : Block n,Fintype.card (LocalClass (dimensions (parameterDimensions hx ha p)) σ j) := by
  simp only [←Nat.card_eq_fintype_card,MarkedLatticeInput,Nat.card_sigma,FamilyClass,Nat.card_pi]

end KroneckerMarkedLatticeInputs
end
