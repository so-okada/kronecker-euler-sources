import KroneckerManuscriptGradingSets
import KroneckerColoredShell

/-! Definition 3.1 and the four claims of Lemma 3.3.
The graded-edge encoding uses the manuscript's vertical length v;
the implementation's suffix parameter is v-1. The existing geometric and
coloring equivalences interpret this encoding on tNE paths. The pointwise
grading of equation (3.1) is defined in KroneckerExplicitShellGrading. -/
set_option autoImplicit false
namespace KroneckerManuscriptShell
open KroneckerStack

def Shell (xs : List (List Edge × ℕ)) (u v ε : ℕ) : List Edge :=
  shell u (v-1) ε xs

theorem Shell_eq (xs : List (List Edge × ℕ)) (u v ε : ℕ) :
    Shell xs u v ε = [.H (u+1)] ++ List.replicate u (.V 0) ++
      xs.flatMap Prod.fst ++ [.H (v-1)] ++ List.replicate (v-1) (.V 0) ++
        [.V (xs.length+1+ε)] := rfl

/-- Claim 1: every grade is at most m, using only the definition's bounds. -/
theorem grades (m u v ε : ℕ) (xs : List (List Edge × ℕ))
    (hu : u+1 ≤ m) (hv : v-1 ≤ m) (hlast : xs.length+1+ε ≤ m)
    (hx : ∀ p ∈ xs, ∀ e ∈ p.1, e.grade ≤ m) :
    ∀ e ∈ Shell xs u v ε, e.grade ≤ m :=
  shell_grades m u (v-1) ε xs hu hv hlast hx

/-- Claim 2: connectedness, including the grade bound. -/
theorem connected (m u v ε : ℕ) (xs : List (List Edge × ℕ))
    (hm : 3 ≤ m) (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (hx : ∀ p ∈ xs, Connected m p.1 p.2)
    (hcase : (xs.length ≤ 2 ∧ ε = 0) ∨
      (xs.length = 1 ∧ ε = 1 ∧ 1 ≤ (xs.map Prod.snd).sum)) :
    Connected m (Shell xs u v ε) ((xs.map Prod.snd).sum-ε) :=
  manuscript_shell m u v ε xs hm hu hv hx hcase

/-- Claim 3: surplus is the sum of the input surpluses minus ε. -/
theorem surplus (m u v ε : ℕ) (xs : List (List Edge × ℕ))
    (hm : 3 ≤ m) (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (hx : ∀ p ∈ xs, Connected m p.1 p.2)
    (hcase : (xs.length ≤ 2 ∧ ε = 0) ∨
      (xs.length = 1 ∧ ε = 1 ∧ 1 ≤ (xs.map Prod.snd).sum)) :
    credit (Shell xs u v ε)-1 = ((xs.map Prod.snd).sum : ℤ)-(ε : ℤ) := by
  have h := connected_surplus (connected m u v ε xs hm hu hv hx hcase)
  have he : ε ≤ (xs.map Prod.snd).sum := by
    rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl, he⟩ <;> omega
  rw [Nat.cast_sub he] at h
  omega

end KroneckerManuscriptShell
