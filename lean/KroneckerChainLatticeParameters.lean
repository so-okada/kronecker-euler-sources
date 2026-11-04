import Mathlib.Data.Int.Interval
import KroneckerChainBinFamily

/- Original module: KroneckerShiftedLatticeCount -/
section
set_option autoImplicit false
namespace KroneckerShiftedLatticeCount
open KroneckerChainFlowIntegrality

noncomputable def latticeIndices (o A B : ℝ) : Finset ℤ := Finset.Ico ⌈A-o⌉ ⌈B-o⌉

theorem lattice_indices_membership (o A B : ℝ) (z : ℤ) :
    z∈latticeIndices o A B ↔ A≤o+z ∧ o+z<B := by
  simp only [latticeIndices,Finset.mem_Ico,Int.ceil_le,Int.lt_ceil]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem shifted_lattice_count (o A B : ℝ) (hAB : A≤B) :
    B-A-1≤((latticeIndices o A B).card : ℝ) := by
  have hab : ⌈A-o⌉≤⌈B-o⌉ := Int.ceil_mono (by linarith)
  have hc : ((latticeIndices o A B).card : ℤ)=⌈B-o⌉-⌈A-o⌉ :=
    Int.card_Ico_of_le _ _ hab
  have hcR : ((latticeIndices o A B).card : ℝ)=(⌈B-o⌉ : ℝ)-(⌈A-o⌉ : ℝ) := by
    exact_mod_cast hc
  have hA := Int.ceil_lt_add_one (A-o)
  have hB := Int.le_ceil (B-o)
  linarith

theorem positive_lattice_count_at_zero (o B : ℝ) (_hB : 0≤B) (hz : OnLattice o 0) :
    B-1≤(((latticeIndices o 0 B).filter (fun z : ℤ => 0<o+(z : ℝ))).card : ℝ) := by
  classical
  obtain ⟨z,hz⟩ := hz
  have ho : o=-(z : ℝ) := by linarith
  have hs : ((latticeIndices o 0 B).filter (fun k : ℤ => 0<o+(k : ℝ)))=Finset.Ico (z+1) ⌈B-o⌉ := by
    ext k
    rw [Finset.mem_filter,lattice_indices_membership,Finset.mem_Ico,Int.lt_ceil]
    have hki : z+1≤k ↔ (z : ℝ)<k := by norm_cast
    rw [hki]
    constructor
    · rintro ⟨⟨hA,hBk⟩,hp⟩
      constructor <;> linarith
    · rintro ⟨hk,hBk⟩
      exact ⟨⟨by linarith,by linarith⟩,by linarith⟩
  rw [hs,Int.card_Ico]
  have hceil := Int.le_ceil (B-o)
  have hnat : (⌈B-o⌉-(z+1) : ℤ)≤(⌈B-o⌉-(z+1)).toNat := by omega
  have hnatR : (⌈B-o⌉ : ℝ)-((z : ℝ)+1)≤((⌈B-o⌉-(z+1)).toNat : ℝ) := by
    exact_mod_cast hnat
  linarith

end KroneckerShiftedLatticeCount
end

/- Original module: KroneckerPositiveShiftedLattice -/
section
set_option autoImplicit false
namespace KroneckerPositiveShiftedLattice
open KroneckerShiftedLatticeCount KroneckerChainFlowIntegrality

theorem positive_filter_without_zero (o A B : ℝ) (hA : 0≤A)
    (hz : ¬OnLattice o 0) :
    (latticeIndices o A B).filter (fun z : ℤ => 0<o+(z : ℝ))=latticeIndices o A B := by
  classical
  apply Finset.filter_eq_self.mpr
  intro z hz'
  have h := (lattice_indices_membership o A B z).mp hz'
  have hn : o+(z : ℝ)≠0 := fun he => hz ⟨z,he.symm⟩
  exact lt_of_le_of_ne (hA.trans h.1) (Ne.symm hn)

/-- Excluding zero costs no additional unit, even for nonintegral shifts. -/
theorem positive_lattice_count (o A B : ℝ) (hA : 0≤A) (hAB : A≤B) :
    B-A-1≤(((latticeIndices o A B).filter (fun z : ℤ => 0<o+(z : ℝ))).card : ℝ) := by
  classical
  by_cases hAz : A=0
  · subst A
    by_cases hz : OnLattice o 0
    · simpa only [sub_zero] using positive_lattice_count_at_zero o B hAB hz
    · rw [positive_filter_without_zero o 0 B le_rfl hz]
      exact shifted_lattice_count o 0 B hAB
  · have hAp : 0<A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hf : (latticeIndices o A B).filter (fun z : ℤ => 0<o+(z : ℝ))=
        latticeIndices o A B := by
      apply Finset.filter_eq_self.mpr
      intro z hz
      exact hAp.trans_le ((lattice_indices_membership o A B z).mp hz).1
    rw [hf]
    exact shifted_lattice_count o A B hAB

end KroneckerPositiveShiftedLattice
end

/- Original module: KroneckerFiniteBinLattices -/
section
set_option autoImplicit false
namespace KroneckerFiniteBinLattices
open KroneckerShiftedLatticeCount KroneckerPositiveShiftedLattice
open KroneckerChainPositiveBins KroneckerChainFlowIntegrality
attribute [local instance] Classical.propDecidable

noncomputable def binIndices (x o : ℝ) (b : ℕ) : Finset ℤ :=
  latticeIndices o ((b : ℝ)*x/256) (((b : ℝ)+1)*x/256)
noncomputable def positiveBinIndices (x o : ℝ) (b : ℕ) : Finset ℤ :=
  (binIndices x o b).filter (fun z => 0<o+(z : ℝ))
abbrev BinPoint (x o : ℝ) (b : ℕ) := {z : ℤ // z∈binIndices x o b}
abbrev PositiveBinPoint (x o : ℝ) (b : ℕ) := {z : ℤ // z∈positiveBinIndices x o b}

theorem bin_membership (x o : ℝ) (b : ℕ) (z : ℤ) :
    z∈binIndices x o b ↔ InBin x b (o+(z : ℝ)) :=
  lattice_indices_membership o _ _ z

theorem positive_bin_membership (x o : ℝ) (b : ℕ) (z : ℤ) :
    z∈positiveBinIndices x o b ↔ InBin x b (o+(z : ℝ)) ∧ 0<o+(z : ℝ) := by
  simp only [positiveBinIndices,Finset.mem_filter,bin_membership]

theorem bin_point_lower (x o : ℝ) (b : ℕ) (hx : 0≤x) :
    x/256-1≤(Fintype.card (BinPoint x o b) : ℝ) := by
  have hab : (b : ℝ)*x/256≤((b : ℝ)+1)*x/256 := by nlinarith
  have h := shifted_lattice_count o _ _ hab
  simpa only [BinPoint,Fintype.card_coe] using (show x/256-1≤((binIndices x o b).card : ℝ) by
    dsimp [binIndices]; nlinarith [h])

theorem positive_bin_point_lower (x o : ℝ) (b : ℕ) (hx : 0≤x) :
    x/256-1≤(Fintype.card (PositiveBinPoint x o b) : ℝ) := by
  have hab : (b : ℝ)*x/256≤((b : ℝ)+1)*x/256 := by nlinarith
  have h := positive_lattice_count o _ _ (by positivity) hab
  simpa only [PositiveBinPoint,Fintype.card_coe] using
    (show x/256-1≤((positiveBinIndices x o b).card : ℝ) by
      dsimp [positiveBinIndices,binIndices]; nlinarith [h])

end KroneckerFiniteBinLattices
end

/- Original module: KroneckerFiniteStateBins -/
section
set_option autoImplicit false
namespace KroneckerFiniteStateBins
open KroneckerChainIncidence
attribute [local instance] Classical.propDecidable

abbrev State := Fin 253

def stateValue (i : State) : ℕ := i.val+1
abbrev StateWord (n : ℕ) := Connector n → State
abbrev TransitionBins {n : ℕ} (i : StateWord n) :=
  ∀ t : Fin n,Fin (254-max (stateValue (i t.castSucc)) (stateValue (i t.succ)))
abbrev StateBins (n : ℕ) := Σ i : StateWord n,TransitionBins i

noncomputable instance (n : ℕ) : Fintype (StateBins n) := Fintype.ofFinite _

def rightBin {n : ℕ} {i : StateWord n} (h : TransitionBins i) : Connector n → ℕ :=
  Fin.lastCases 0 (fun t => (h t).val)

theorem transition_bin_constraints {n : ℕ} (i : StateWord n) (h : TransitionBins i)
    (t : Fin n) :
    stateValue (i t.castSucc)+rightBin h t.castSucc≤253 ∧
    stateValue (i t.succ)+rightBin h t.castSucc≤253 := by
  have ht := (h t).isLt
  have hi := (i t.castSucc).isLt
  have hj := (i t.succ).isLt
  simp only [rightBin,Fin.lastCases_castSucc]
  dsimp [stateValue] at *
  omega

theorem state_bin_constraints {n : ℕ} (P : StateBins n) :
    (∀ t,stateValue (P.1 t)+rightBin P.2 t≤253) ∧
    (∀ t : Fin n,stateValue (P.1 t.succ)+rightBin P.2 t.castSucc≤253) ∧
    rightBin P.2 (Fin.last n)=0 := by
  refine ⟨?_,fun t => (transition_bin_constraints P.1 P.2 t).2,? _⟩
  · intro t
    refine Fin.lastCases ?_ (fun s => (transition_bin_constraints P.1 P.2 s).1) t
    simp only [rightBin,Fin.lastCases_last,Nat.add_zero,stateValue]
    have h := (P.1 (Fin.last n)).isLt
    omega
  · simp only [rightBin,Fin.lastCases_last]

theorem transition_bins_card {n : ℕ} (i : StateWord n) :
    Fintype.card (TransitionBins i)=
      ∏ t : Fin n,(254-max (stateValue (i t.castSucc)) (stateValue (i t.succ))) := by
  simp only [TransitionBins,Fintype.card_pi,Fintype.card_fin]

theorem state_bins_card (n : ℕ) : Fintype.card (StateBins n)=
    ∑ i : StateWord n,∏ t : Fin n,(254-max (stateValue (i t.castSucc)) (stateValue (i t.succ))) := by
  simp only [←Nat.card_eq_fintype_card,StateBins,Nat.card_sigma,TransitionBins,Nat.card_pi,Nat.card_fin]

end KroneckerFiniteStateBins
end

/- Original module: KroneckerChainLatticeParameters -/
section
set_option autoImplicit false
namespace KroneckerChainLatticeParameters
open KroneckerFiniteStateBins KroneckerFiniteBinLattices KroneckerChainIncidence
open KroneckerChainBinFamily KroneckerChainFlowIntegrality
attribute [local instance] Classical.propDecidable

noncomputable def extend {α : Type*} [Zero α] {n : ℕ} (f : Connector n → α) (t : ℕ) : α :=
  if ht : t<n+1 then f ⟨t,ht⟩ else 0

theorem extend_at {α : Type*} [Zero α] {n : ℕ} (f : Connector n → α) (t : Connector n) :
    extend f t=f t := by simp [extend,t.isLt]

noncomputable def offset (x : ℝ) {n : ℕ} (t : Connector n) : ℝ := ((t.val : ℝ)+1)*x
abbrev LeftPoints {n : ℕ} (x : ℝ) (P : StateBins n) :=
  ∀ t : Connector n,BinPoint x (offset x t) (stateValue (P.1 t))
abbrev RightPoints {n : ℕ} (x : ℝ) (P : StateBins n) :=
  ∀ t : Connector n,PositiveBinPoint x (-offset x t) (rightBin P.2 t)
abbrev LatticeFor {n : ℕ} (x : ℝ) (P : StateBins n) := LeftPoints x P × RightPoints x P
abbrev LatticeParameter (n : ℕ) (x : ℝ) := Σ P : StateBins n,LatticeFor x P

noncomputable def leftFlow {n : ℕ} {x : ℝ} {P : StateBins n} (L : LatticeFor x P) : ℕ → ℝ :=
  extend (fun t => offset x t+((L.1 t).val : ℝ))
noncomputable def rightFlow {n : ℕ} {x : ℝ} {P : StateBins n} (L : LatticeFor x P) : ℕ → ℝ :=
  extend (fun t => -offset x t+((L.2 t).val : ℝ))
noncomputable def stateFunction {n : ℕ} (P : StateBins n) : ℕ → ℕ := extend (fun t => stateValue (P.1 t))
noncomputable def binFunction {n : ℕ} (P : StateBins n) : ℕ → ℕ := extend (rightBin P.2)

noncomputable instance (n : ℕ) (x : ℝ) : Fintype (LatticeParameter n x) := Fintype.ofFinite _

theorem lattice_parameter_bins {n : ℕ} {x : ℝ} {P : StateBins n} (L : LatticeFor x P) :
    BinData n x (leftFlow L) (rightFlow L) (stateFunction P) (binFunction P) := by
  have hs := state_bin_constraints P
  have eval {α : Type} [Zero α] (f : Connector n → α) (t : ℕ) (ht : t≤n) :
      extend f t=f ⟨t,by omega⟩ := by simp [extend,show t<n+1 by omega]
  constructor
  · intro t ht
    rw [stateFunction,eval _ t ht]
    exact Nat.succ_le_succ (Nat.zero_le _)
  · intro t ht
    rw [stateFunction,binFunction,eval _ t ht,eval _ t ht]
    exact hs.1 ⟨t,by omega⟩
  · intro t ht
    rw [stateFunction,binFunction,eval _ (t+1) (by omega),eval _ t (by omega)]
    exact hs.2.1 ⟨t,ht⟩
  · intro t ht
    rw [stateFunction,leftFlow,eval _ t ht,eval _ t ht]
    exact (bin_membership _ _ _ _).mp (L.1 ⟨t,by omega⟩).property
  · intro t ht
    rw [binFunction,rightFlow,eval _ t ht,eval _ t ht]
    exact ((positive_bin_membership _ _ _ _).mp (L.2 ⟨t,by omega⟩).property).1
  · intro t ht
    rw [rightFlow,eval _ t ht]
    exact ((positive_bin_membership _ _ _ _).mp (L.2 ⟨t,by omega⟩).property).2
  · rw [binFunction,eval _ n le_rfl]
    exact hs.2.2

theorem lattice_parameter_integrality {n : ℕ} {x : ℝ} {P : StateBins n} (L : LatticeFor x P) :
    (∀ t≤n,OnLattice (((t : ℝ)+1)*x) (leftFlow L t)) ∧
    (∀ t≤n,OnLattice (-((t : ℝ)+1)*x) (rightFlow L t)) := by
  constructor
  · intro t ht
    refine ⟨(L.1 ⟨t,by omega⟩).val,?_⟩
    simp [leftFlow,extend,show t<n+1 by omega,offset]
  · intro t ht
    refine ⟨(L.2 ⟨t,by omega⟩).val,?_⟩
    simp [rightFlow,extend,show t<n+1 by omega,offset]
    ring

end KroneckerChainLatticeParameters
end
