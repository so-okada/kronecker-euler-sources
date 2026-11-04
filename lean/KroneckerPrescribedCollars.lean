import KroneckerCollarRecovery

/-! Pair any two prescribed equal-length collars in their actual outside-to-inside order. -/
set_option autoImplicit false
namespace KroneckerPrescribedCollars
open KroneckerWordCounts KroneckerCollarColoring

def pairCollars (A B : List ℕ) : List (ℕ×ℕ) := A.zip B.reverse

theorem pairCollars_length (A B : List ℕ) (hlen : A.length=B.length) :
    (pairCollars A B).length=A.length := by simp [pairCollars,hlen]

theorem pairCollars_legal (m : ℕ) (A B : List ℕ)
    (hA : ∀ r ∈ A,1 ≤ r ∧ r ≤ m-1) (hB : ∀ r ∈ B,1 ≤ r ∧ r ≤ m-1) :
    LegalPairs m (pairCollars A B) := by
  intro p hp
  have h := List.of_mem_zip hp
  exact ⟨hA p.1 h.1,hB p.2 (by simpa using h.2)⟩

theorem pairCollars_path (A B rs : List ℕ) (hlen : A.length=B.length) :
    collarPath (pairCollars A B) (runWord rs)=runWord (A++rs++B) := by
  rw [collarPath_runWord]
  unfold pairCollars
  rw [List.map_fst_zip (by simpa using hlen.le),List.map_snd_zip (by simpa using hlen.ge)]
  simp

end KroneckerPrescribedCollars
