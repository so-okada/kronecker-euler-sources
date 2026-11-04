import KroneckerPaperPathGradings
import KroneckerPeriodicWords
import Mathlib.Data.List.Rotate

set_option autoImplicit false

namespace KroneckerPaperPaths

theorem concat_assoc (P Q R : TNEPath) :
    concat (concat P Q) R = concat P (concat Q R) := by
  apply TNEPath.ext
  · simp [List.append_assoc]
  · by_cases hP : P.steps = [] <;> by_cases hQ : Q.steps = [] <;>
      by_cases hR : R.steps = [] <;> simp [concat, ofSteps, hP, hQ, hR]

theorem ofSteps_concat (s t : List Bool) (o : LatticePoint) :
    concat (ofSteps s o) (ofSteps t o) = ofSteps (s ++ t) o := by
  apply TNEPath.ext
  · rfl
  by_cases hs : s = [] <;> by_cases ht : t = [] <;>
    simp [concat, ofSteps, hs, ht]

theorem ofSteps_self (P : TNEPath) : ofSteps P.steps P.origin = P := by
  simpa only [translate, add_zero] using translate_zero P

theorem concat_translate (P Q : TNEPath) (t : LatticePoint) :
    concat (translate P t) (translate Q t) = translate (concat P Q) t := by
  apply TNEPath.ext
  · rfl
  by_cases hP : P.steps = [] <;> by_cases hQ : Q.steps = [] <;>
    simp [concat, translate, ofSteps, hP, hQ]

def power (P : TNEPath) : ℕ → TNEPath
  | 0 => empty
  | n + 1 => concat (power P n) P

@[simp] theorem power_zero (P : TNEPath) : power P 0 = empty := rfl

@[simp] theorem power_one (P : TNEPath) : power P 1 = P := empty_concat P

theorem power_add (P : TNEPath) (i j : ℕ) :
    power P (i + j) = concat (power P i) (power P j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    change concat (power P (i + j)) P = concat (power P i) (concat (power P j) P)
    rw [ih, concat_assoc]

theorem power_translate (P : TNEPath) (t : LatticePoint) (n : ℕ) :
    power (translate P t) n = translate (power P n) t := by
  induction n with
  | zero => simp
  | succ n ih => simp only [power, ih, concat_translate]

def runPath (rs : List ℕ) (o : LatticePoint) : TNEPath :=
  ofSteps (KroneckerWordCounts.runWord rs) o

@[simp] theorem runPath_steps (rs : List ℕ) (o : LatticePoint) :
    (runPath rs o).steps = KroneckerWordCounts.runWord rs := rfl

@[simp] theorem runPath_nil (o : LatticePoint) : runPath [] o = empty := by
  simp [runPath, KroneckerWordCounts.runWord]

theorem runPath_append (rs ss : List ℕ) (o : LatticePoint) :
    runPath (rs ++ ss) o = concat (runPath rs o) (runPath ss o) := by
  simp only [runPath, KroneckerWordCounts.runWord, List.flatMap_append,
    ofSteps_concat]

theorem runPath_singleton (j : ℕ) (hj : 0 < j) :
    runPath [j] 0 = simpleRun j hj := by
  simp [runPath, KroneckerWordCounts.runWord, KroneckerStack.runShape, simpleRun]

theorem runPath_translate (rs : List ℕ) (o t : LatticePoint) :
    translate (runPath rs o) t = runPath rs (o + t) := ofSteps_translate _ _ _

theorem runPath_power (rs : List ℕ) (o : LatticePoint) (n : ℕ) :
    power (runPath rs o) n = runPath (KroneckerPeriodicWords.repeatRuns rs n) o := by
  induction n with
  | zero => simp [KroneckerPeriodicWords.repeatRuns]
  | succ n ih => rw [power, ih, KroneckerPeriodicWords.repeatRuns, runPath_append]

def decodeRuns : List Bool → ℕ × List ℕ
  | [] => (0, [])
  | false :: s => let d := decodeRuns s; (d.1 + 1, d.2)
  | true :: s => let d := decodeRuns s; (0, d.1 :: d.2)

theorem decodeRuns_north (j : ℕ) (s : List Bool) :
    decodeRuns (List.replicate j false ++ s) =
      (j + (decodeRuns s).1, (decodeRuns s).2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp [List.replicate_succ, decodeRuns, ih, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

theorem decodeRuns_runWord (rs : List ℕ) :
    decodeRuns (KroneckerWordCounts.runWord rs) = (0, rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp [KroneckerWordCounts.runWord, KroneckerStack.runShape, decodeRuns,
      decodeRuns_north, KroneckerWordCounts.runWord] at ih ⊢
    rw [ih]
    simp

theorem runWord_injective : Function.Injective KroneckerWordCounts.runWord := by
  intro rs ss h
  have hd := congrArg decodeRuns h
  simpa only [decodeRuns_runWord, Prod.mk.injEq, true_and] using hd

theorem runPath_injective (o : LatticePoint) :
    Function.Injective (fun rs => runPath rs o) := by
  intro rs ss h
  exact runWord_injective (congrArg TNEPath.steps h)

def rotateRuns (P : TNEPath) (j : ℕ) : TNEPath :=
  runPath ((decodeRuns P.steps).2.rotate j) P.origin

def exchangeRuns (P : TNEPath) (j : ℕ) : TNEPath :=
  let rs := (decodeRuns P.steps).2
  runPath (rs.take j ++ ((rs.drop j).take 2).reverse ++ rs.drop (j + 2)) P.origin

theorem rotateRuns_runPath (rs : List ℕ) (o : LatticePoint) (j : ℕ) :
    rotateRuns (runPath rs o) j = runPath (rs.rotate j) o := by
  simp only [rotateRuns, runPath_steps, decodeRuns_runWord]
  by_cases h : rs = []
  · simp [h]
  · have hs : KroneckerWordCounts.runWord rs ≠ [] := by
      intro hs
      have : rs = [] := runWord_injective hs
      exact h this
    simp [runPath, ofSteps, hs]

end KroneckerPaperPaths
