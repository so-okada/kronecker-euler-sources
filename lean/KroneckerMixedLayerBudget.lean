import KroneckerMiddleCompleteLift

/- Original module: KroneckerMixedInsertLift -/
section
/-! Lift a middle vertical insertion after any number of complete-run steps. -/
set_option autoImplicit false
namespace KroneckerMixedInsertLift
open KroneckerColoredShell KroneckerCollarColoring KroneckerMixedPrograms KroneckerListInsertion
open KroneckerMiddleContext KroneckerMiddlePositions KroneckerMiddleInsertLift

def mixedInsertLift {m u v : ℕ} {U V : List Bool} {K A D : ℕ} (pairs : List (ℕ×ℕ))
    (p : MixedProgram m (shellPath u v U) (collarPath pairs (shellPath u v V)) K A D)
    (x y i : ℕ) (hx : 1 ≤ x ∧ x ≤ m-2) (hy : 1 ≤ y ∧ y ≤ m-2) (hi : i ≤ V.length) :
    MixedProgram m (shellPath u v U) (collarPath ((x,y)::pairs) (shellPath u v (insertAt i false V))) K (A+1) D := by
  simpa only [inserted_middle_path pairs u v x y i V hi] using
    MixedProgram.insert p x y ((leftContext pairs u).length+i) hx hy (middle_insert_bounds pairs u v V i hi)


end KroneckerMixedInsertLift
end

/- Original module: KroneckerMixedDeleteLift -/
section
/-! Lift a middle vertical deletion after any number of complete-run steps. -/
set_option autoImplicit false
namespace KroneckerMixedDeleteLift
open KroneckerColoredShell KroneckerCollarColoring KroneckerMixedPrograms KroneckerListDeletion
open KroneckerMiddleContext KroneckerMiddlePositions KroneckerMiddleDeleteLift

def mixedDeleteLift {m u v : ℕ} {U V : List Bool} {K A D : ℕ} (pairs : List (ℕ×ℕ))
    (p : MixedProgram m (shellPath u v U) (collarPath pairs (shellPath u v V)) K A D)
    (x y i : ℕ) (hx : 1 ≤ x ∧ x ≤ m-2) (hy : 1 ≤ y ∧ y ≤ m-2)
    (hi : i < V.length) (hvrt : V[i]=false) :
    MixedProgram m (shellPath u v U) (collarPath ((x,y)::pairs) (shellPath u v (removeAt i V))) K A (D+1) := by
  simpa only [deleted_middle_path pairs u v x y i V hi] using
    MixedProgram.delete p x y ((leftContext pairs u).length+i) hx hy
      (middle_delete_bound pairs u v V i hi) (middle_vertical pairs u v V i hi hvrt)


end KroneckerMixedDeleteLift
end

/- Original module: KroneckerRawProgramLift -/
section
/-! Lift an arbitrary raw K/A/D edit list into the literal buffered prescribed target. -/
set_option autoImplicit false
namespace KroneckerRawProgramLift
open KroneckerColoredShell KroneckerCollarColoring KroneckerMixedPrograms KroneckerRawMixedPrograms
open KroneckerMiddleContext KroneckerMiddleCompleteLift KroneckerMixedInsertLift KroneckerMixedDeleteLift

noncomputable def liftRaw {m u v : ℕ} {U V : List Bool} {K A D : ℕ} (p : RawProgram m U V K A D)
    (pairs : List (ℕ×ℕ)) (hlen : pairs.length=A+D) (hp : EditPairs m pairs) :
    MixedProgram m (shellPath u v U) (collarPath pairs (shellPath u v V)) K A D := by
  induction p generalizing pairs with
  | nil =>
    have h : pairs=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst pairs
    exact .nil
  | complete p r i hr hi ih =>
    exact completeLift pairs (ih pairs hlen hp) r i hr hi
  | @insert V K A D p i hi ih =>
    cases pairs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons pair pairs =>
      have htail : pairs.length=A+D := by simp only [List.length_cons] at hlen; omega
      exact mixedInsertLift pairs (ih pairs htail (fun q hq => hp q (by simp [hq]))) pair.1 pair.2 i
        (hp pair (by simp)).1 (hp pair (by simp)).2 hi
  | @delete V K A D p i hi hv ih =>
    cases pairs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons pair pairs =>
      have htail : pairs.length=A+D := by simp only [List.length_cons] at hlen; omega
      exact mixedDeleteLift pairs (ih pairs htail (fun q hq => hp q (by simp [hq]))) pair.1 pair.2 i
        (hp pair (by simp)).1 (hp pair (by simp)).2 hi hv


end KroneckerRawProgramLift
end

/- Original module: KroneckerRawProgramCount -/
section
/-! Actual raw K/A/D comparisons with fixed edit layers and enough surplus-draining layers. -/
set_option autoImplicit false
namespace KroneckerRawProgramCount
open KroneckerWordCounts KroneckerFiberBudget KroneckerColoredShell KroneckerCollarColoring
open KroneckerRawMixedPrograms KroneckerMiddleContext KroneckerRawProgramLift KroneckerBufferedMixedCount

theorem raw_program_count {m u v : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) {U V : List Bool} {K A D : ℕ}
    (p : RawProgram m U V K A D) (edit drain : List (ℕ×ℕ))
    (he : edit.length=A+D) (hle : EditPairs m edit) (hld : LegalPairs m drain) (hd : K+m*D ≤ drain.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*
      pathCount m (collarPath drain (collarPath edit (shellPath u v V))) 0 :=
  buffered_mixed_count hm hu hv (liftRaw p edit he hle) drain hld hd

theorem raw_program_real {m u v : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) {U V : List Bool} {K A D : ℕ}
    (p : RawProgram m U V K A D) (edit drain : List (ℕ×ℕ))
    (he : edit.length=A+D) (hle : EditPairs m edit) (hld : LegalPairs m drain) (hd : K+m*D ≤ drain.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤
      (pathCount m (collarPath drain (collarPath edit (shellPath u v V))) 0 : ℝ) :=
  buffered_mixed_real hm hu hv (liftRaw p edit he hle) drain hld hd

end KroneckerRawProgramCount
end

/- Original module: KroneckerMixedLayerBudget -/
section
/-! The manuscript layer allowance supplies A+D edit layers and K+mD drain layers. -/
set_option autoImplicit false
namespace KroneckerMixedLayerBudget

theorem mixed_layer_lengths {m K A D : ℕ} (pairs : List (ℕ×ℕ))
    (h : K+A+(m+1)*D ≤ pairs.length) :
    (pairs.drop (pairs.length-(A+D))).length=A+D ∧
      K+m*D ≤ (pairs.take (pairs.length-(A+D))).length := by
  simp only [List.length_drop,List.length_take]
  have hsum : K+A+(m+1)*D=A+D+(K+m*D) := by rw [Nat.add_mul,Nat.one_mul]; omega
  omega

end KroneckerMixedLayerBudget
end
