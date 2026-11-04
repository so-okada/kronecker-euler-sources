import KroneckerManuscriptMechanicalDefinitions
import KroneckerManuscriptOuterExtension
import KroneckerExactSlotCounts

/-! The manuscript's run-factors, run phase, named outer extension,
and marked-slot counts. The source indices below are zero based. -/
set_option autoImplicit false
noncomputable section

namespace KroneckerManuscriptMechanicalDefinitions
open KroneckerPaperPaths KroneckerWordCounts

/-- The factor consisting of simple runs h+1 through h+l, in its position
in the prefix of length h+l. The manuscript requires l>0 and h+l≤rs.length. -/
def ccsRunFactor (rs : List ℕ) (h l : ℕ) (o : LatticePoint) : TNEPath :=
  subpath (runPath (rs.take (h+l)) o)
    (runWord (rs.take h)).length (runWord (rs.take (h+l))).length

theorem ccsRunFactor_steps (rs : List ℕ) (h l : ℕ) (o : LatticePoint) :
    (ccsRunFactor rs h l o).steps = runWord ((rs.drop h).take l) := by
  simp only [ccsRunFactor, subpath_steps, runPath_steps]
  rw [List.take_add]
  simp [runWord, List.flatMap_append]

theorem ccsRunFactor_horizontal_length (rs : List ℕ) (h l : ℕ)
    (o : LatticePoint) (hl : h+l ≤ rs.length) :
    (ccsRunFactor rs h l o).steps.count true = l := by
  rw [ccsRunFactor_steps]
  have H := runPath_east_count ((rs.drop h).take l) o
  simpa only [runPath_steps, List.length_take, List.length_drop,
    Nat.min_eq_left (show l ≤ rs.length-h by omega)] using H

theorem ccsRunFactor_vertical_length (rs : List ℕ) (h l : ℕ)
    (o : LatticePoint) :
    (ccsRunFactor rs h l o).steps.count false = ((rs.drop h).take l).sum := by
  rw [ccsRunFactor_steps]
  exact runPath_north_count ((rs.drop h).take l) o

/-- Run phase at the beginning of simple run h+1 of the period-q sequence. -/
def RunPhase (q h : ℕ) : ℕ := h % q

theorem runPhase_formula (q h : ℕ) : RunPhase q h = h-q*(h/q) := by
  have H := Nat.mod_add_div h q
  unfold RunPhase
  omega

theorem runPhase_range (q h : ℕ) (hq : 0<q) : RunPhase q h < q :=
  Nat.mod_lt h hq

theorem runPhase_after_gap (q h φ : ℕ) (hq : 0<q) (hφ : φ<q) :
    RunPhase q (h+phaseGap q h φ)=φ :=
  (phaseGap_spec q h φ hq hφ).2

end KroneckerManuscriptMechanicalDefinitions

namespace KroneckerManuscriptOuterExtension
open KroneckerColoring KroneckerWordCounts

variable (m : ℕ) (hm : 3 ≤ m) (A B : List ℕ) (U : List Bool) (d : ℕ)
  (hAB : A.length ≤ 2*B.length) (hBA : B.length ≤ 2*A.length)
  (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) (hB : ∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1)

/-- A chosen extension for the fixed paths and surplus d. -/
def i_d_extension :
    Extension m d U (runWord A ++ U ++ runWord B) (runWord A).length :=
  Classical.choice (balanced_extension m hm A B U d hAB hBA hA hB)

/-- The map i_d in Lemma 3.6. -/
def i_d : ConnectedColorings m U d →
    ConnectedColorings m (runWord A ++ U ++ runWord B) d :=
  (i_d_extension m hm A B U d hAB hBA hA hB).map

theorem i_d_injective : Function.Injective (i_d m hm A B U d hAB hBA hA hB) :=
  (i_d_extension m hm A B U d hAB hBA hA hB).injective

theorem i_d_recover (g : ConnectedColorings m U d) (i : Fin U.length) :
    (i_d m hm A B U d hAB hBA hA hB g).val
      ⟨(runWord A).length+i.val, by simp only [List.length_append]; omega⟩ = g.val i :=
  (i_d_extension m hm A B U d hAB hBA hA hB).recover g i

theorem i_d_grade_color (g : ConnectedColorings m U d) (i : Fin U.length) :
    let j : Fin (runWord A ++ U ++ runWord B).length :=
      ⟨(runWord A).length+i.val, by simp only [List.length_append]; omega⟩
    grade ((i_d m hm A B U d hAB hBA hA hB g).val j) = grade (g.val i) ∧
    ((i_d m hm A B U d hAB hBA hA hB g).val j).2.val+1 = (g.val i).2.val+1 := by
  dsimp only
  rw [i_d_recover]
  exact ⟨rfl,rfl⟩

end KroneckerManuscriptOuterExtension

namespace KroneckerManuscriptMarkedCounts
open KroneckerReflectedSingleSlotCounts KroneckerReflectedPairSlotCounts

def P (j : ℕ) (d : Fin 3) : ℕ :=
  Fintype.card (SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d)

def Qeq (j : ℕ) (d : Fin 3) : ℕ :=
  Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d d)

def Qne (j : ℕ) (d e : Fin 3) : ℕ :=
  Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d e)

theorem P_formula (j : ℕ) (d : Fin 3) :
    (P j d : ℚ) = ((4*j+4).choose (j+1) : ℚ)/(3*j+4) :=
  reflected_single_slot_closed_count j d

theorem P_color_independent (j : ℕ) (d e : Fin 3) : P j d = P j e := by
  exact_mod_cast (P_formula j d).trans (P_formula j e).symm

theorem Qeq_formula (j : ℕ) (hj : 0<j) (d : Fin 3) :
    Qeq j d = 2*(4*j+2).choose (j-1) := by
  obtain ⟨n,rfl⟩ : ∃ n, j=n+1 := ⟨j-1, by omega⟩
  simpa [Qeq, Nat.mul_add, Nat.add_assoc] using reflected_same_slot_count n d

theorem Qeq_color_independent (j : ℕ) (hj : 0<j) (d e : Fin 3) :
    Qeq j d = Qeq j e :=
  (Qeq_formula j hj d).trans (Qeq_formula j hj e).symm

theorem Qne_ratio (j : ℕ) {d e : Fin 3} (hde : d≠e) :
    2*j*Qne j d e = (2*j+3)*Qeq j d :=
  reflected_slot_pair_ratio j hde

theorem Qne_color_independent (j : ℕ) (hj : 0<j)
    {d e d' e' : Fin 3} (hde : d≠e) (hde' : d'≠e') :
    Qne j d e = Qne j d' e' := by
  apply Nat.eq_of_mul_eq_mul_left (show 0<2*j by omega)
  rw [Qne_ratio j hde, Qne_ratio j hde', Qeq_color_independent j hj d d']

end KroneckerManuscriptMarkedCounts
