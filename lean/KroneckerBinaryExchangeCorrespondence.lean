import KroneckerManuscriptNotationSync
import KroneckerGeometricBinaryPrograms

/-! Every adjacent exchange of the two binary run lengths supplies the
manuscript's adjacent-shell-exchange data, including the translated origin. -/

noncomputable section
set_option autoImplicit false

namespace KroneckerBinaryExchangeCorrespondence
open KroneckerPaperPaths KroneckerWordCounts KroneckerBinaryExchangeShapes
open KroneckerManuscriptExchangeDefinitions KroneckerManuscriptNotationSync

def witness (right : Bool) (A B : List ℕ) (o : LatticePoint) (u v : Fin 2) :
    AdjShellExch :=
  ⟨binaryPrefix A, false :: runWord B, o, u, v, right⟩

theorem witness_source (right : Bool) (A B : List ℕ) (o : LatticePoint)
    (u v : Fin 2) :
    (witness right A B o u v).X = runPath (A ++ pairRuns right ++ B) o := by
  change ofSteps (KroneckerExchangePath.sourcePath right (binaryPrefix A)
    (false :: runWord B)) o = ofSteps (runWord (A ++ pairRuns right ++ B)) o
  rw [binary_source]

theorem witness_target (right : Bool) (A B : List ℕ) (o : LatticePoint)
    (u v : Fin 2) :
    (witness right A B o u v).X' = runPath (A ++ pairRuns (!right) ++ B) o := by
  change ofSteps (KroneckerExchangePath.targetPath right (binaryPrefix A)
    (false :: runWord B)) o = ofSteps (runWord (A ++ pairRuns (!right) ++ B)) o
  rw [binary_target]

/-- The geometric run exchange is the same target as the shell witness. -/
theorem witness_exchange_target (right : Bool) (A B : List ℕ) (o : LatticePoint)
    (u v : Fin 2) :
    (witness right A B o u v).X' =
      exchangeRuns (runPath (A ++ pairRuns right ++ B) o) A.length := by
  rw [exchange_pairRuns, witness_target]

/-- Every binary run decomposition has a wrapped exchange for either shell size. -/
theorem binary_wrapped_exchange (right : Bool) (A B : List ℕ) (o : LatticePoint)
    (u v : Fin 2) :
    (WrapExch (runPath (A ++ pairRuns right ++ B) o)
      (exchangeRuns (runPath (A ++ pairRuns right ++ B) o) A.length) u v).Nonempty := by
  have h := WrapExch_nonempty (witness right A B o u v)
  rw [witness_source, witness_exchange_target] at h
  exact h

/-- The prefix can be empty or start with E; the suffix is arbitrary. -/
def segmentWitness (right : Bool) (L R : List Bool) (o : LatticePoint) (u v : Fin 2) :
    AdjShellExch :=
  ⟨(L ++ [true, false]).drop 1, false :: R, o, u, v, right⟩

theorem segment_source_word (right : Bool) (L R : List Bool)
    (hL : L = [] ∨ ∃ L', L = true :: L') :
    KroneckerExchangePath.sourcePath right ((L ++ [true, false]).drop 1) (false :: R) =
      L ++ runWord (pairRuns right) ++ R := by
  rcases hL with rfl | ⟨L', rfl⟩
  · cases right <;> simp [KroneckerExchangePath.sourcePath, runWord,
      KroneckerStack.runShape, pairRuns]
  · cases right <;> simp [KroneckerExchangePath.sourcePath, runWord,
      KroneckerStack.runShape, pairRuns, List.append_assoc]

theorem segment_target_word (right : Bool) (L R : List Bool)
    (hL : L = [] ∨ ∃ L', L = true :: L') :
    KroneckerExchangePath.targetPath right ((L ++ [true, false]).drop 1) (false :: R) =
      L ++ runWord (pairRuns (!right)) ++ R := by
  exact segment_source_word (!right) L R hL

theorem segment_source (right : Bool) (L R : List Bool) (o : LatticePoint)
    (u v : Fin 2) (hL : L = [] ∨ ∃ L', L = true :: L') :
    (segmentWitness right L R o u v).X =
      ofSteps (L ++ runWord (pairRuns right) ++ R) o := by
  change ofSteps (KroneckerExchangePath.sourcePath right ((L ++ [true, false]).drop 1)
    (false :: R)) o = ofSteps (L ++ runWord (pairRuns right) ++ R) o
  rw [segment_source_word right L R hL]

theorem segment_target (right : Bool) (L R : List Bool) (o : LatticePoint)
    (u v : Fin 2) (hL : L = [] ∨ ∃ L', L = true :: L') :
    (segmentWitness right L R o u v).X' =
      ofSteps (L ++ runWord (pairRuns (!right)) ++ R) o := by
  change ofSteps (KroneckerExchangePath.targetPath right ((L ++ [true, false]).drop 1)
    (false :: R)) o = ofSteps (L ++ runWord (pairRuns (!right)) ++ R) o
  rw [segment_target_word right L R hL]

theorem segment_wrapped_exchange (right : Bool) (L R : List Bool) (o : LatticePoint)
    (u v : Fin 2) (hL : L = [] ∨ ∃ L', L = true :: L') :
    (WrapExch (ofSteps (L ++ runWord (pairRuns right) ++ R) o)
      (ofSteps (L ++ runWord (pairRuns (!right)) ++ R) o) u v).Nonempty := by
  have h := WrapExch_nonempty (segmentWitness right L R o u v)
  rw [segment_source right L R o u v hL, segment_target right L R o u v hL] at h
  exact h

/-- No three consecutive north edges occur in a binary run. -/
def noThreeNorth : List Bool → Bool
  | false :: false :: false :: _ => false
  | [] => true
  | _ :: xs => noThreeNorth xs

theorem noThreeNorth_tail (a : Bool) (xs : List Bool)
    (h : noThreeNorth (a :: xs) = true) : noThreeNorth xs = true := by
  cases a <;> cases xs with
  | nil => simp [noThreeNorth]
  | cons b ys => cases b <;> cases ys with
    | nil => simp [noThreeNorth]
    | cons c zs => cases c <;> simp_all [noThreeNorth]

theorem noThreeNorth_suffix (L R : List Bool)
    (h : noThreeNorth (L ++ R) = true) : noThreeNorth R = true := by
  induction L with
  | nil => exact h
  | cons a L ih => exact ih (noThreeNorth_tail a _ h)

theorem noThreeNorth_runWord (rs : List ℕ) (hs : ∀ r ∈ rs, r = 1 ∨ r = 2) :
    noThreeNorth (runWord rs) = true := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      have hr : r = 1 ∨ r = 2 := hs r (by simp)
      have ht : ∀ q ∈ rs, q = 1 ∨ q = 2 := fun q h => hs q (by simp [h])
      have hi := ih ht
      cases rs with
      | nil => rcases hr with rfl | rfl <;>
          simp [runWord, KroneckerStack.runShape, noThreeNorth]
      | cons q qs =>
          rcases hr with rfl | rfl <;>
            simpa [runWord, KroneckerStack.runShape, noThreeNorth] using hi

theorem noThreeNorth_replicate_bound (n : ℕ) (R : List Bool)
    (h : noThreeNorth (List.replicate n false ++ R) = true) : n ≤ 2 := by
  cases n with
  | zero => omega
  | succ n => cases n with
    | zero => omega
    | succ n => cases n with
      | zero => omega
      | succ n => simp [List.replicate_succ, noThreeNorth] at h

/-- These are exactly the two possible lengths in any exchange decomposition
of a binary run, even when the suffix begins inside a simple run. -/
theorem binary_decomposition_lengths (X : TNEPath) (hX : Binary X)
    (L R : List Bool) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (hshape : X.steps = L ++ KroneckerStack.runShape a ++ KroneckerStack.runShape b ++ R) :
    (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
  obtain ⟨rs, hrs, hpath, hbinary⟩ := hX
  have hn : noThreeNorth X.steps = true := by
    rw [hpath, runPath_steps]
    exact noThreeNorth_runWord rs hbinary
  rw [hshape] at hn
  have ha' : a ≤ 2 := by
    have h := noThreeNorth_suffix L _ (by simpa [List.append_assoc] using hn)
    change noThreeNorth (true :: (List.replicate a false ++ (KroneckerStack.runShape b ++ R))) = true at h
    have h := noThreeNorth_tail true _ h
    exact noThreeNorth_replicate_bound a _ h
  have hb' : b ≤ 2 := by
    have h := noThreeNorth_suffix (L ++ KroneckerStack.runShape a) _ (by
      simpa [List.append_assoc] using hn)
    change noThreeNorth (true :: (List.replicate b false ++ R)) = true at h
    have h := noThreeNorth_tail true _ h
    exact noThreeNorth_replicate_bound b _ h
  omega

theorem binary_decomposition_prefix (X : TNEPath) (hX : Binary X)
    (L R : List Bool) (a b : ℕ)
    (hshape : X.steps = L ++ KroneckerStack.runShape a ++ KroneckerStack.runShape b ++ R) :
    L = [] ∨ ∃ L', L = true :: L' := by
  obtain ⟨rs, hrs, hpath, hbinary⟩ := hX
  have hfirst : X.steps.head? = some true := by
    rw [hpath, runPath_steps]
    cases rs with
    | nil => simp at hrs
    | cons r rs => simp [runWord, KroneckerStack.runShape]
  cases L with
  | nil => exact Or.inl rfl
  | cons first rest =>
      cases first with
      | false =>
          rw [hshape] at hfirst
          simp at hfirst
      | true => exact Or.inr ⟨rest,rfl⟩

/-- For every exchange decomposition of a binary path, the manuscript's
source and exchanged target admit the existing wrapped-exchange map. The
suffix can begin inside the second simple run. -/
theorem arbitrary_binary_decomposition_wrapped_exchange
    (X : TNEPath) (hX : Binary X) (L R : List Bool) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (hshape : X.steps = L ++ KroneckerStack.runShape a ++ KroneckerStack.runShape b ++ R)
    (u v : Fin 2) :
    (WrapExch X
      (ofSteps (L ++ KroneckerStack.runShape b ++ KroneckerStack.runShape a ++ R) X.origin)
      u v).Nonempty := by
  have hL := binary_decomposition_prefix X hX L R a b hshape
  rcases binary_decomposition_lengths X hX L R a b ha hb hne hshape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hx : X = ofSteps (L ++ runWord (pairRuns true) ++ R) X.origin := by
      calc
        X = ofSteps X.steps X.origin := (ofSteps_self X).symm
        _ = _ := congrArg (fun s => ofSteps s X.origin) (by
          simpa [pairRuns,runWord,KroneckerStack.runShape,List.append_assoc] using hshape)
    have ht : ofSteps (L ++ runWord (pairRuns (!true)) ++ R) X.origin =
        ofSteps (L ++ KroneckerStack.runShape 2 ++ KroneckerStack.runShape 1 ++ R) X.origin := by
      simp [pairRuns,runWord,List.flatMap,KroneckerStack.runShape,List.append_assoc]
    have hh := segment_wrapped_exchange true L R X.origin u v hL
    rw [← hx, ht] at hh
    exact hh

  · have hx : X = ofSteps (L ++ runWord (pairRuns false) ++ R) X.origin := by
      calc
        X = ofSteps X.steps X.origin := (ofSteps_self X).symm
        _ = _ := congrArg (fun s => ofSteps s X.origin) (by
          simpa [pairRuns,runWord,KroneckerStack.runShape,List.append_assoc] using hshape)
    have ht : ofSteps (L ++ runWord (pairRuns (!false)) ++ R) X.origin =
        ofSteps (L ++ KroneckerStack.runShape 1 ++ KroneckerStack.runShape 2 ++ R) X.origin := by
      simp [pairRuns,runWord,List.flatMap,KroneckerStack.runShape,List.append_assoc]
    have hh := segment_wrapped_exchange false L R X.origin u v hL
    rw [← hx, ht] at hh
    exact hh

/-- The exchange-decomposition equation as written for NE factors, including
the translation by the initial point, yields the wrapped-exchange witness. -/
theorem geometric_exchange_decomposition_wrapped (X L R : TNEPath) (hX : Binary X)
    (hL : L.origin = 0) (hR : R.origin = 0) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (hshape : X = translate
      (concat (concat (concat L (simpleRun a ha)) (simpleRun b hb)) R) X.origin)
    (u v : Fin 2) :
    (WrapExch X (translate
      (concat (concat (concat L (simpleRun b hb)) (simpleRun a ha)) R) X.origin) u v).Nonempty := by
  have hs : X.steps = L.steps ++ KroneckerStack.runShape a ++
      KroneckerStack.runShape b ++ R.steps := by
    have h := congrArg TNEPath.steps hshape
    simpa [KroneckerStack.runShape,List.append_assoc] using h
  have hL' : L = ofSteps L.steps 0 := by simpa [hL] using (ofSteps_self L).symm
  have hR' : R = ofSteps R.steps 0 := by simpa [hR] using (ofSteps_self R).symm
  have ht : translate (concat (concat (concat L (simpleRun b hb)) (simpleRun a ha)) R) X.origin =
      ofSteps (L.steps ++ KroneckerStack.runShape b ++ KroneckerStack.runShape a ++ R.steps)
        X.origin := by
    rw [hL',hR']
    simp [simpleRun, ofSteps_concat, ofSteps_translate, KroneckerStack.runShape, List.append_assoc]
  rw [ht]
  exact arbitrary_binary_decomposition_wrapped_exchange X hX L.steps R.steps a b ha hb hne hs u v

end KroneckerBinaryExchangeCorrespondence

#print axioms KroneckerBinaryExchangeCorrespondence.witness_source
#print axioms KroneckerBinaryExchangeCorrespondence.witness_target
#print axioms KroneckerBinaryExchangeCorrespondence.witness_exchange_target
#print axioms KroneckerBinaryExchangeCorrespondence.binary_wrapped_exchange
#print axioms KroneckerBinaryExchangeCorrespondence.segment_source_word
#print axioms KroneckerBinaryExchangeCorrespondence.segment_target_word
#print axioms KroneckerBinaryExchangeCorrespondence.segment_wrapped_exchange
#print axioms KroneckerBinaryExchangeCorrespondence.binary_decomposition_lengths
#print axioms KroneckerBinaryExchangeCorrespondence.arbitrary_binary_decomposition_wrapped_exchange
#print axioms KroneckerBinaryExchangeCorrespondence.geometric_exchange_decomposition_wrapped
