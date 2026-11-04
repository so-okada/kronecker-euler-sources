import KroneckerMiddleDeleteLift

/- Original module: KroneckerMiddleProgramLift -/
section
/-! Assign arbitrary prescribed shell pairs to every step of a raw middle program. -/
set_option autoImplicit false
namespace KroneckerMiddleProgramLift
open KroneckerColoredShell KroneckerCollarColoring KroneckerVerticalPrograms
open KroneckerMiddlePrograms KroneckerMiddleContext KroneckerMiddleInsertLift KroneckerMiddleDeleteLift

noncomputable def liftMiddle {m u v : ℕ} {U V : List Bool} {A D : ℕ} (p : MiddleProgram U V A D)
    (pairs : List (ℕ×ℕ)) (hlen : pairs.length=A+D) (hp : EditPairs m pairs) :
    Program m (shellPath u v U) (collarPath pairs (shellPath u v V)) A D := by
  induction p generalizing pairs with
  | nil =>
    have h : pairs=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst pairs
    exact .nil
  | @insert V A D p i hi ih =>
    cases pairs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons pair pairs =>
      have htail : pairs.length=A+D := by simp only [List.length_cons] at hlen; omega
      exact insertLift pairs (ih pairs htail (fun q hq => hp q (by simp [hq]))) pair.1 pair.2 i
        (hp pair (by simp)).1 (hp pair (by simp)).2 hi
  | @delete V A D p i hi hv ih =>
    cases pairs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons pair pairs =>
      have htail : pairs.length=A+D := by simp only [List.length_cons] at hlen; omega
      exact deleteLift pairs (ih pairs htail (fun q hq => hp q (by simp [hq]))) pair.1 pair.2 i
        (hp pair (by simp)).1 (hp pair (by simp)).2 hi hv


end KroneckerMiddleProgramLift
end

/- Original module: KroneckerMiddleProgramCount -/
section
/-! Comparison for arbitrary raw middle edits, with prescribed edit and draining layers. -/
set_option autoImplicit false
namespace KroneckerMiddleProgramCount
open KroneckerWordCounts KroneckerFiberBudget KroneckerColoredShell KroneckerCollarColoring
open KroneckerMiddlePrograms KroneckerMiddleContext KroneckerMiddleProgramLift KroneckerBufferedProgramCount



end KroneckerMiddleProgramCount
end

/- Original module: KroneckerPrescribedLayerSplit -/
section
/-! Split any sufficiently long prescribed pair list into outer drain layers and inner edit layers. -/
set_option autoImplicit false
namespace KroneckerPrescribedLayerSplit
open KroneckerCollarColoring KroneckerMiddleContext

theorem collarPath_append (outer inner : List (ℕ×ℕ)) (U : List Bool) :
    collarPath (outer++inner) U=collarPath outer (collarPath inner U) := by
  induction outer with
  | nil => rfl
  | cons p outer ih => simp only [List.cons_append,collarPath,ih]

theorem layer_split_lengths {m A D : ℕ} (pairs : List (ℕ×ℕ)) (h : A+(m+1)*D ≤ pairs.length) :
    (pairs.drop (pairs.length-(A+D))).length=A+D ∧
      m*D ≤ (pairs.take (pairs.length-(A+D))).length := by
  simp only [List.length_drop,List.length_take]
  have hsum : A+(m+1)*D=A+D+m*D := by rw [Nat.add_mul,Nat.one_mul]; omega
  omega

theorem editPairs_sublist {m : ℕ} {small large : List (ℕ×ℕ)}
    (h : small.Sublist large) (hp : EditPairs m large) : EditPairs m small :=
  fun p hp' => hp p (h.subset hp')

theorem editPairs_legal {m : ℕ} {pairs : List (ℕ×ℕ)} (hp : EditPairs m pairs) : LegalPairs m pairs := by
  intro p h
  have t := hp p h
  omega

end KroneckerPrescribedLayerSplit
end
