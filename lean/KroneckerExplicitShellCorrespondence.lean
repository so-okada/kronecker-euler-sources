import KroneckerExplicitShellGrading

set_option autoImplicit false
noncomputable section
namespace KroneckerExplicitShellCorrespondence
open KroneckerPaperPaths KroneckerNaturalPathGradings
open KroneckerManuscriptShell

def gradedWord (X : TNEPath) (f : G X) : List KroneckerStack.Edge :=
  List.ofFn (fun k : Edge X => if X.steps[k.val] then
    KroneckerStack.Edge.H (f (edgeEquiv X k)) else
    KroneckerStack.Edge.V (f (edgeEquiv X k)))

@[simp] theorem gradedWord_length (X : TNEPath) (f : G X) :
    (gradedWord X f).length = X.steps.length := by simp [gradedWord]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem gradedWord_shell (X : TNEPath) (f : G X) (u v j ε : ℕ) (hv : 1 ≤ v) :
    gradedWord (path X u v) (GShell X f u v j ε) =
      [.H (u+1)] ++ List.replicate u (.V 0) ++ gradedWord X f ++
      [.H (v-1)] ++ List.replicate (v-1) (.V 0) ++ [.V (j+1+ε)] := by
  apply List.ext_getElem
  · simp only [gradedWord_length, path_length, List.length_append,
      List.length_singleton, List.length_replicate]
    omega
  · intro k hk hl
    have hlen : k < u+1+X.steps.length+v+1 := by
      simpa only [gradedWord_length, path_length] using hk
    cases k with
    | zero =>
      simp [gradedWord, GShell, path, KroneckerColoredShell.shellPath, KroneckerStack.runShape]
    | succ k =>
      simp only [gradedWord, List.getElem_ofFn, GShell, Equiv.symm_apply_apply]
      simp (disch := omega) [path, KroneckerColoredShell.shellPath,
        KroneckerStack.runShape, List.getElem_append, List.getElem_cons_succ,
        List.getElem_replicate, List.length_ofFn, List.getElem_ofFn]
      by_cases ha : k < u
      · have hi : ¬ (u ≤ k ∧ k+1 < u+1+X.steps.length) := by omega
        have hr : k+1 ≠ u+1+X.steps.length := by omega
        have he : k+1 ≠ u+(X.steps.length+(v+1)) := by omega
        simp [ha, hi, hr, he]
      · by_cases hb : k-u < X.steps.length
        · have hi : u ≤ k ∧ k+1 < u+1+X.steps.length := by omega
          simp [ha, hb, hi]
        · have hi : ¬ (u ≤ k ∧ k+1 < u+1+X.steps.length) := by omega
          by_cases hr : k+1 = u+1+X.steps.length
          · have ht : k-u-X.steps.length = 0 := by omega
            simp [ha, hb, hr, ht]
          · have ht : k-u-X.steps.length ≠ 0 := by omega
            simp only [ha, hb, hi, hr]
            simp only [List.getElem_cons, ht]
            simp only [List.getElem_replicate, ite_false]
            simp only [List.getElem_append, List.length_replicate]
            split_ifs <;> simp_all [gradedWord_length,path_length] <;>
              first | contradiction | omega

end KroneckerExplicitShellCorrespondence

namespace KroneckerExplicitShellCorrespondence
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptShell

theorem gradedWord_trace (X : TNEPath) (f : G X) :
    gradedWord X f = KroneckerPaperConnected.wordList (geometricTrace f) X.steps.length := by
  apply List.ext_getElem
  · simp [gradedWord, KroneckerPaperConnected.wordList]
  · intro k hk hl
    have hkX : k < X.steps.length := by simpa only [gradedWord_length] using hk
    have hn : X.steps.length ≠ 0 := by omega
    simp [gradedWord, KroneckerPaperConnected.wordList, geometricTrace,
      KroneckerSourceNaturalGradings.naturalTrace, hn, Nat.mod_eq_of_lt hkX,
      KroneckerWordCounts.pathShape, List.getD, hkX]

theorem connected_of_gradedWord {m d : ℕ} (X : TNEPath) (f : G X)
    (h : KroneckerStack.Connected m (gradedWord X f) d) :
    ConnectedGrading f ∧ Surp X f = (d : ℤ) := by
  rw [gradedWord_trace] at h
  have hn := KroneckerStack.connected_node h
  refine ⟨KroneckerPaperConnected.nodeRun_connected hn, ?_⟩
  have hb := KroneckerPaperConnected.nodeRun_balance hn
  change KroneckerCompatibility.balance (geometricTrace f) X.steps.length - 1 = _
  omega

theorem shell_encoding (X : TNEPath) (f : G X) (u v ε : ℕ) (hv : 1 ≤ v)
    (xs : List (List KroneckerStack.Edge × ℕ)) (hx : gradedWord X f = xs.flatMap Prod.fst) :
    gradedWord (path X u v) (GShell X f u v xs.length ε) = Shell xs u v ε := by
  rw [gradedWord_shell X f u v xs.length ε hv, Shell_eq, hx]

theorem explicit_shell_connected (m u v ε : ℕ) (X : TNEPath) (f : G X)
    (xs : List (List KroneckerStack.Edge × ℕ))
    (hword : gradedWord X f = xs.flatMap Prod.fst)
    (hm : 3 ≤ m) (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (hx : ∀ p ∈ xs, KroneckerStack.Connected m p.1 p.2)
    (hcase : (xs.length ≤ 2 ∧ ε = 0) ∨
      (xs.length = 1 ∧ ε = 1 ∧ 1 ≤ (xs.map Prod.snd).sum)) :
    ConnectedGrading (GShell X f u v xs.length ε) ∧
      Surp (path X u v) (GShell X f u v xs.length ε) =
        ((xs.map Prod.snd).sum : ℤ) - (ε : ℤ) := by
  have hc := connected_of_gradedWord (m := m) (path X u v)
    (GShell X f u v xs.length ε) (by
      rw [shell_encoding X f u v ε hv.1 xs hword]
      exact KroneckerManuscriptShell.connected m u v ε xs hm hu hv hx hcase)
  have he : ε ≤ (xs.map Prod.snd).sum := by
    rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl, he⟩ <;> omega
  exact ⟨hc.1, hc.2.trans (Int.natCast_sub he)⟩

end KroneckerExplicitShellCorrespondence
