import KroneckerContextDeletion

/- Original module: KroneckerMiddlePrograms -/
section
/-! A word-dependent sequence of raw middle edits; shell types are assigned later. -/
set_option autoImplicit false
namespace KroneckerMiddlePrograms
open KroneckerListInsertion KroneckerListDeletion

inductive MiddleProgram (U : List Bool) : List Bool → ℕ → ℕ → Type
  | nil : MiddleProgram U U 0 0
  | insert {V : List Bool} {A D : ℕ} (p : MiddleProgram U V A D) (i : ℕ) (hi : i ≤ V.length) :
      MiddleProgram U (insertAt i false V) (A+1) D
  | delete {V : List Bool} {A D : ℕ} (p : MiddleProgram U V A D) (i : ℕ)
      (hi : i < V.length) (hv : V[i]=false) : MiddleProgram U (removeAt i V) A (D+1)

def steps {U V : List Bool} {A D : ℕ} : MiddleProgram U V A D → ℕ
  | .nil => 0
  | .insert p _ _ => steps p+1
  | .delete p _ _ _ => steps p+1

theorem middle_steps {U V : List Bool} {A D : ℕ} (p : MiddleProgram U V A D) : steps p=A+D := by
  induction p with
  | nil => rfl
  | insert p i hi ih => simp only [steps,ih]; omega
  | delete p i hi hv ih => simp only [steps,ih]; omega

end KroneckerMiddlePrograms
end

/- Original module: KroneckerMiddleContext -/
section
/-! Literal left and right contexts of the prescribed edit shells and two buffers. -/
set_option autoImplicit false
namespace KroneckerMiddleContext
open KroneckerStack KroneckerWordCounts KroneckerColoredShell KroneckerCollarColoring

def EditPairs (m : ℕ) (L : List (ℕ×ℕ)) : Prop :=
  ∀ p ∈ L,(1 ≤ p.1 ∧ p.1 ≤ m-2) ∧ (1 ≤ p.2 ∧ p.2 ≤ m-2)

def leftContext (pairs : List (ℕ×ℕ)) (u : ℕ) : List Bool :=
  runWord (pairs.map Prod.fst)++runShape u

def rightContext (pairs : List (ℕ×ℕ)) (v : ℕ) : List Bool :=
  runShape v++runWord (pairs.map Prod.snd).reverse

theorem collar_middle_context (pairs : List (ℕ×ℕ)) (u v : ℕ) (U : List Bool) :
    collarPath pairs (shellPath u v U)=leftContext pairs u++U++rightContext pairs v := by
  induction pairs with
  | nil => simp [collarPath,shellPath,leftContext,rightContext,runWord,List.append_assoc]
  | cons p pairs ih =>
    rw [collarPath,ih]
    simp [shellPath,leftContext,rightContext,runWord,List.append_assoc]

theorem leftContext_positive (pairs : List (ℕ×ℕ)) (u : ℕ) : 1 ≤ (leftContext pairs u).length := by
  simp [leftContext,runShape]
  omega

end KroneckerMiddleContext
end

/- Original module: KroneckerMiddlePositions -/
section
/-! Translate raw middle positions through all previously prescribed shells. -/
set_option autoImplicit false
namespace KroneckerMiddlePositions
open KroneckerColoredShell KroneckerCollarColoring KroneckerMiddleContext KroneckerContextDeletion

theorem middle_insert_bounds (pairs : List (ℕ×ℕ)) (u v : ℕ) (U : List Bool) (i : ℕ)
    (hi : i ≤ U.length) :
    1 ≤ (leftContext pairs u).length+i ∧
      (leftContext pairs u).length+i ≤ (collarPath pairs (shellPath u v U)).length := by
  rw [collar_middle_context]
  have h := leftContext_positive pairs u
  simp only [List.length_append]
  omega

theorem middle_delete_bound (pairs : List (ℕ×ℕ)) (u v : ℕ) (U : List Bool) (i : ℕ)
    (hi : i < U.length) :
    (leftContext pairs u).length+i < (collarPath pairs (shellPath u v U)).length := by
  rw [collar_middle_context]
  simp only [List.length_append]
  omega

theorem middle_vertical (pairs : List (ℕ×ℕ)) (u v : ℕ) (U : List Bool) (i : ℕ)
    (hi : i < U.length) (hv : U[i]=false) :
    (collarPath pairs (shellPath u v U))[(leftContext pairs u).length+i]'(middle_delete_bound pairs u v U i hi)=false := by
  have h := getElem_context (leftContext pairs u) U (rightContext pairs v) i hi
  simpa only [collar_middle_context,hv] using h

end KroneckerMiddlePositions
end

/- Original module: KroneckerMiddleInsertLift -/
section
/-! Lift one raw middle insertion to the actual prescribed-shell insertion map. -/
set_option autoImplicit false
namespace KroneckerMiddleInsertLift
open KroneckerColoredShell KroneckerCollarColoring KroneckerVerticalPrograms KroneckerInsertionPalette
open KroneckerMiddleContext KroneckerMiddlePositions KroneckerContextInsertion KroneckerListInsertion

theorem inserted_middle_path (pairs : List (ℕ×ℕ)) (u v x y i : ℕ) (V : List Bool) (hi : i ≤ V.length) :
    insertedPath x y ((leftContext pairs u).length+i) (collarPath pairs (shellPath u v V))=
      collarPath ((x,y)::pairs) (shellPath u v (insertAt i false V)) := by
  simp only [insertedPath,collarPath,shellPath]
  change shellPath x y (insertAt ((leftContext pairs u).length+i) false (collarPath pairs (shellPath u v V)))=
    shellPath x y (collarPath pairs (shellPath u v (insertAt i false V)))
  rw [collar_middle_context,insertAt_context _ _ _ _ _ hi,collar_middle_context]

def insertLift {m u v : ℕ} {U V : List Bool} {A D : ℕ} (pairs : List (ℕ×ℕ))
    (p : Program m (shellPath u v U) (collarPath pairs (shellPath u v V)) A D)
    (x y i : ℕ) (hx : 1 ≤ x ∧ x ≤ m-2) (hy : 1 ≤ y ∧ y ≤ m-2) (hi : i ≤ V.length) :
    Program m (shellPath u v U) (collarPath ((x,y)::pairs) (shellPath u v (insertAt i false V))) (A+1) D := by
  simpa only [inserted_middle_path pairs u v x y i V hi] using
    Program.insert p x y ((leftContext pairs u).length+i) hx hy (middle_insert_bounds pairs u v V i hi)

end KroneckerMiddleInsertLift
end

/- Original module: KroneckerMiddleDeleteLift -/
section
/-! Lift one raw middle deletion to the actual prescribed-shell deletion map. -/
set_option autoImplicit false
namespace KroneckerMiddleDeleteLift
open KroneckerColoredShell KroneckerCollarColoring KroneckerVerticalPrograms KroneckerDeletionColoring
open KroneckerMiddleContext KroneckerMiddlePositions KroneckerContextDeletion KroneckerListDeletion

theorem deleted_middle_path (pairs : List (ℕ×ℕ)) (u v x y i : ℕ) (V : List Bool) (hi : i < V.length) :
    deletionPath x y (collarPath pairs (shellPath u v V)) ((leftContext pairs u).length+i)=
      collarPath ((x,y)::pairs) (shellPath u v (removeAt i V)) := by
  change shellPath x y (removeAt ((leftContext pairs u).length+i) (collarPath pairs (shellPath u v V)))=
    shellPath x y (collarPath pairs (shellPath u v (removeAt i V)))
  rw [collar_middle_context,removeAt_context _ _ _ _ hi,collar_middle_context]

def deleteLift {m u v : ℕ} {U V : List Bool} {A D : ℕ} (pairs : List (ℕ×ℕ))
    (p : Program m (shellPath u v U) (collarPath pairs (shellPath u v V)) A D)
    (x y i : ℕ) (hx : 1 ≤ x ∧ x ≤ m-2) (hy : 1 ≤ y ∧ y ≤ m-2)
    (hi : i < V.length) (hvertical : V[i]=false) :
    Program m (shellPath u v U) (collarPath ((x,y)::pairs) (shellPath u v (removeAt i V))) A (D+1) := by
  simpa only [deleted_middle_path pairs u v x y i V hi] using
    Program.delete p x y ((leftContext pairs u).length+i) hx hy
      (middle_delete_bound pairs u v V i hi) (middle_vertical pairs u v V i hi hvertical)

end KroneckerMiddleDeleteLift
end
