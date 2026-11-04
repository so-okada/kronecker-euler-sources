import KroneckerBinaryShell
import KroneckerOneRun

/-! Lemma 3.6: prescribed outer runs, arbitrary interior path, and exact
recovery of every input palette entry (both grade and color). -/
set_option autoImplicit false
namespace KroneckerManuscriptOuterExtension
open KroneckerStack KroneckerColoring KroneckerWordCounts
open KroneckerColoredShell KroneckerBinaryShell KroneckerOneRun

structure Extension (m d : ℕ) (U V : List Bool) (k : ℕ) where
  length_le : k+U.length ≤ V.length
  map : ConnectedColorings m U d → ConnectedColorings m V d
  recover : ∀ g (i : Fin U.length),
    (map g).val ⟨k+i.val, by have := i.isLt; omega⟩ = g.val i

namespace Extension
variable {m d : ℕ} {U V W : List Bool} {k l : ℕ}

def identity (m d : ℕ) (U : List Bool) : Extension m d U U 0 where
  length_le := by omega
  map := id
  recover := by intros; simp

def trans (f : Extension m d U V k) (g : Extension m d V W l) :
    Extension m d U W (l+k) where
  length_le := by have := f.length_le; have := g.length_le; omega
  map := g.map ∘ f.map
  recover := by
    intro x i
    have h := g.recover (f.map x) ⟨k+i.val, by have := f.length_le; have := i.isLt; omega⟩
    simpa only [Function.comp_apply, Nat.add_assoc] using h.trans (f.recover x i)

theorem injective (f : Extension m d U V k) : Function.Injective f.map := by
  intro x y h
  apply Subtype.ext
  funext i
  have h' := congrArg (fun z : ConnectedColorings m V d =>
    z.val ⟨k+i.val, by have := f.length_le; have := i.isLt; omega⟩) h
  simpa only [f.recover] using h'

end Extension

def unary (m d u v : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool) :
    Extension m d U (shellPath u v U) (u+1) where
  length_le := by simp [shellPath, runShape]; omega
  map := unaryShell u v d hm hu hv U
  recover := by
    intro g i
    exact congrFun (unaryShell_recover u v d hm hu hv U g) i

def leftTwo (m d u r v : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hr : 1 ≤ r ∧ r ≤ m-1)
    (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool) :
    Extension m d U (binaryPath u v (runShape r) U) ((u+1)+(r+1)) where
  length_le := by simp [binaryPath, runShape]; omega
  map := fun g => by
    have base := oneRun (m := m) hr.1 (by omega) ⟨0, Nat.choose_pos (by omega)⟩
    exact ⟨(binaryShell u v 0 d hm hu hv (runShape r) U (base,g)).val,
      by simpa using (binaryShell u v 0 d hm hu hv (runShape r) U (base,g)).property⟩
  recover := by
    intro g i
    have h := congrFun (recoverRight_binaryColoring u v (by omega) (by omega)
      hm hv.1 (runShape r) U
      (oneRun (m := m) hr.1 (by omega) ⟨0,Nat.choose_pos (by omega)⟩).val g.val) i
    simpa only [recoverRight, binaryShell, runShape, List.length_cons,
      List.length_replicate] using h

def rightTwo (m d u r v : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hr : 1 ≤ r ∧ r ≤ m-1)
    (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool) :
    Extension m d U (binaryPath u v U (runShape r)) (u+1) where
  length_le := by simp [binaryPath, runShape]; omega
  map := fun g => by
    have base := oneRun (m := m) hr.1 (by omega) ⟨0, Nat.choose_pos (by omega)⟩
    exact (binaryShell u v d 0 hm hu hv U (runShape r) (g,base))
  recover := by
    intro g i
    exact congrFun (recoverLeft_binaryColoring u v (by omega) (by omega)
      hm hv.1 U (runShape r) g.val
      (oneRun (m := m) hr.1 (by omega) ⟨0,Nat.choose_pos (by omega)⟩).val) i

theorem balanced_extension_aux (m : ℕ) (hm : 3 ≤ m) (n : ℕ) :
    ∀ (A B : List ℕ), A.length+B.length=n →
      A.length ≤ 2*B.length → B.length ≤ 2*A.length →
      (∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) → (∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) →
      ∀ (U : List Bool) (d : ℕ),
        Nonempty (Extension m d U (runWord A ++ U ++ runWord B) (runWord A).length) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A B hn hAB hBA hA hB U d
    cases A with
    | nil =>
      have hBnil : B = [] := List.length_eq_zero_iff.mp (by simpa using hBA)
      subst B
      simpa [runWord] using Nonempty.intro (Extension.identity m d U)
    | cons u A =>
      have hu := hA u (by simp)
      have hBne : B ≠ [] := by intro h; subst B; simp at hAB
      obtain ⟨Bs, v, htail⟩ : ∃ Bs v, B = Bs ++ [v] :=
        ⟨B.dropLast, B.getLast hBne, (List.dropLast_append_getLast hBne).symm⟩
      subst B
      have hv := hB v (by simp)
      simp only [List.length_cons, List.length_append] at hn hAB hBA
      by_cases heq : A.length = Bs.length
      · obtain ⟨f⟩ := ih (A.length+Bs.length) (by omega) A Bs rfl
          (by omega) (by omega) (fun r hr => hA r (by simp [hr]))
          (fun r hr => hB r (by simp [hr])) U d
        have e := f.trans (unary m d u v hm hu hv (runWord A ++ U ++ runWord Bs))
        exact ⟨by simpa [shellPath, runWord, runShape, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using e⟩
      · by_cases hleft : Bs.length < A.length
        · cases A with
          | nil => simp at hleft
          | cons r As =>
            have hr := hA r (by simp)
            obtain ⟨f⟩ := ih (As.length+Bs.length) (by simp at hn; omega) As Bs rfl
              (by simp at hAB; omega) (by simp at hleft; omega)
              (fun t ht => hA t (by simp [ht])) (fun t ht => hB t (by simp [ht])) U d
            have e := f.trans (leftTwo m d u r v hm hu hr hv (runWord As ++ U ++ runWord Bs))
            exact ⟨by simpa [binaryPath, runWord, runShape, List.append_assoc,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using e⟩
        · have hright : A.length < Bs.length := by omega
          have hBsne : Bs ≠ [] := by intro h; subst Bs; simp at hright
          obtain ⟨Bt, r, ht⟩ : ∃ Bt r, Bs = Bt ++ [r] :=
            ⟨Bs.dropLast, Bs.getLast hBsne, (List.dropLast_append_getLast hBsne).symm⟩
          subst Bs
          have hr := hB r (by simp)
          obtain ⟨f⟩ := ih (A.length+Bt.length) (by simp at hn; omega) A Bt rfl
            (by simp at hright; omega) (by simp at hBA; omega)
            (fun t ht => hA t (by simp [ht])) (fun t ht => hB t (by simp [ht])) U d
          have e := f.trans (rightTwo m d u r v hm hu hr hv (runWord A ++ U ++ runWord Bt))
          exact ⟨by simpa [binaryPath, runWord, runShape, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using e⟩

/-- The construction with explicit restriction to the interior edge positions. -/
theorem balanced_extension (m : ℕ) (hm : 3 ≤ m) (A B : List ℕ) (U : List Bool) (d : ℕ)
    (hAB : A.length ≤ 2*B.length) (hBA : B.length ≤ 2*A.length)
    (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) (hB : ∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) :
    Nonempty (Extension m d U (runWord A ++ U ++ runWord B) (runWord A).length) :=
  balanced_extension_aux m hm (A.length+B.length) A B rfl hAB hBA hA hB U d

/-- The injectivity assertion of Lemma 3.6. -/
theorem balanced_injection (m : ℕ) (hm : 3 ≤ m) (A B : List ℕ) (U : List Bool) (d : ℕ)
    (hAB : A.length ≤ 2*B.length) (hBA : B.length ≤ 2*A.length)
    (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) (hB : ∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) :
    ∃ f : ConnectedColorings m U d → ConnectedColorings m (runWord A ++ U ++ runWord B) d,
      Function.Injective f := by
  obtain ⟨f⟩ := balanced_extension m hm A B U d hAB hBA hA hB
  exact ⟨f.map, f.injective⟩

end KroneckerManuscriptOuterExtension
