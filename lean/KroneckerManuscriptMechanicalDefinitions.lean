import KroneckerGeometricRunEdits
import KroneckerFrameWord

set_option autoImplicit false
namespace KroneckerManuscriptMechanicalDefinitions
open KroneckerPaperPaths KroneckerFiniteWindows

def phaseGap (q h φ : ℕ) : ℕ :=
  if h%q ≤ φ then φ-h%q else q+φ-h%q

theorem phaseGap_spec (q h φ : ℕ) (hq : 0<q) (hφ : φ<q) :
    phaseGap q h φ < q ∧ (h+phaseGap q h φ)%q=φ := by
  have hh := Nat.mod_lt h hq
  unfold phaseGap
  split_ifs with hr
  · have hs : h%q+(φ-h%q)=φ := by omega
    constructor
    · omega
    · rw [Nat.add_mod, Nat.mod_eq_of_lt (show φ-h%q<q by omega),hs,Nat.mod_eq_of_lt hφ]
  · have hs : h%q+(q+φ-h%q)=q+φ := by omega
    constructor
    · omega
    · rw [Nat.add_mod, Nat.mod_eq_of_lt (show q+φ-h%q<q by omega),hs]
      simp [Nat.mod_eq_of_lt hφ]

theorem phaseGap_unique (q h φ r : ℕ) (hq : 0<q) (hφ : φ<q)
    (hr : r<q) (he : (h+r)%q=φ) : r=phaseGap q h φ := by
  have hh := Nat.mod_lt h hq
  rw [Nat.add_mod,Nat.mod_eq_of_lt hr] at he
  by_cases hz : h%q+r<q
  · rw [Nat.mod_eq_of_lt hz] at he
    unfold phaseGap
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at he
    unfold phaseGap
    split_ifs <;> omega

theorem full_window_starts (X : List ℕ) (q i : ℕ) (hq : 0<q) :
    i ∈ Finset.range (X.length+1-q) ↔ i+q ≤ X.length := by
  rw [Finset.mem_range]
  omega

set_option backward.isDefEq.respectTransparency false in
theorem bad_window_geometric (X : List ℕ) (p : ℤ) (q i : ℕ)
    (hq : 0<q) (o : LatticePoint) :
    i ∈ (Finset.range (X.length+1-q)).filter (fun j => wordWindowSum X j q ≠ p) ↔
      i+q ≤ X.length ∧ ((runPath ((X.drop i).take q) o).steps.count false : ℤ) ≠ p := by
  simp only [Finset.mem_filter,full_window_starts X q i hq,runPath_north_count,wordWindowSum]

end KroneckerManuscriptMechanicalDefinitions
#print axioms KroneckerManuscriptMechanicalDefinitions.phaseGap_spec
#print axioms KroneckerManuscriptMechanicalDefinitions.phaseGap_unique
#print axioms KroneckerManuscriptMechanicalDefinitions.bad_window_geometric
