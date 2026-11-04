import KroneckerTaggedWordCount

/- Original module: KroneckerVerticalPrograms -/
section
/-! A fixed finite program of actual vertical edits, with prescribed shell types at each step. -/
set_option autoImplicit false
namespace KroneckerVerticalPrograms
open KroneckerInsertionPalette KroneckerDeletionColoring

inductive Program (m : ℕ) (U : List Bool) : List Bool → ℕ → ℕ → Type
  | nil : Program m U U 0 0
  | insert {V : List Bool} {A D : ℕ} (p : Program m U V A D) (u v i : ℕ)
      (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) (hi : 1 ≤ i ∧ i ≤ V.length) :
      Program m U (insertedPath u v i V) (A+1) D
  | delete {V : List Bool} {A D : ℕ} (p : Program m U V A D) (u v i : ℕ)
      (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2)
      (hi : i < V.length) (hvertical : V[i]=false) :
      Program m U (deletionPath u v V i) A (D+1)

def steps {m : ℕ} {U V : List Bool} {A D : ℕ} : Program m U V A D → ℕ
  | .nil => 0
  | .insert p _ _ _ _ _ _ => steps p+1
  | .delete p _ _ _ _ _ _ _ => steps p+1

theorem steps_eq {m : ℕ} {U V : List Bool} {A D : ℕ} (p : Program m U V A D) : steps p=A+D := by
  induction p with
  | nil => rfl
  | insert p u v i hu hv hi ih => simp only [steps,ih]; omega
  | delete p u v i hu hv hi hvert ih => simp only [steps,ih]; omega

end KroneckerVerticalPrograms
end

/- Original module: KroneckerProgramLayouts -/
section
/-! The layout and deleted-original record of a vertical edit program are independent of colors. -/
set_option autoImplicit false
namespace KroneckerProgramLayouts
open KroneckerTaggedLayout KroneckerWrappedTags KroneckerEditedLayouts KroneckerVerticalPrograms

def programLayout {m n q : ℕ} {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (L : Layout n q U) : Layout n q V :=
  match p with
  | .nil => L
  | .insert p u v i _ _ _ => wrapLayout u v (insertLayout i (programLayout p L))
  | .delete p u v i _ _ hi hvert => wrapLayout u v (removeLayout i hi hvert (programLayout p L))

theorem programLayout_deleted_bound {m n q : ℕ} {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (L : Layout n q U) :
    (programLayout p L).deleted.length ≤ L.deleted.length+D := by
  induction p with
  | nil => simp [programLayout]
  | insert p u v i hu hv hi ih => exact ih
  | delete p u v i hu hv hi hvert ih =>
    have h := removeLayout_deleted_bound i hi hvert (programLayout p L)
    change (removeLayout i hi hvert (programLayout p L)).deleted.length ≤ _
    omega

end KroneckerProgramLayouts
end

/- Original module: KroneckerProgramExecution -/
section
/-! Execute the prescribed edits on actual connected colorings. -/
set_option autoImplicit false
namespace KroneckerProgramExecution
open KroneckerWordCounts KroneckerVerticalPrograms KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap

abbrev SurplusColorings (m : ℕ) (U : List Bool) := (c : ℕ) × ConnectedColorings m U c

noncomputable def runProgram {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) (g : ConnectedColorings m U c) : SurplusColorings m V :=
  match p with
  | .nil => ⟨c,g⟩
  | .insert p u v i hu hv hi =>
    let old := runProgram hm p c g
    ⟨old.1,verticalInsertion u v i old.1 hm hu hv _ hi old.2⟩
  | .delete p u v i hu hv hi hvert =>
    let old := runProgram hm p c g
    let d := verticalDeletion u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvert old.2
    ⟨old.1+d.1.val,d.2⟩

theorem runProgram_nil {m : ℕ} (hm : 4 ≤ m) (U : List Bool) (c : ℕ) (g : ConnectedColorings m U c) :
    runProgram hm (.nil : Program m U U 0 0) c g=⟨c,g⟩ := rfl

theorem runProgram_insert_surplus {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (u v i : ℕ) (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2)
    (hi : 1 ≤ i ∧ i ≤ V.length) (c : ℕ) (g : ConnectedColorings m U c) :
    (runProgram hm (.insert p u v i hu hv hi) c g).1=(runProgram hm p c g).1 := rfl

end KroneckerProgramExecution
end
