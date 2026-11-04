import KroneckerGeometricBinaryPrograms
import KroneckerBinaryFactorLemmas
import KroneckerManuscriptRunEditList
import KroneckerNaturalPathGradings
import KroneckerCurrentMechanicalNotation

/-! Binary run-edit lists and the actual prescribed-collar map.  Membership
uses the manuscript's equality of insertion outputs: a stored insertion is
permitted when its target is a binary insertion at some legal boundary.
The converse reifies that boundary witness into an indexed binary program. -/
set_option autoImplicit false
noncomputable section

namespace KroneckerPaperPaths
open KroneckerWordCounts KroneckerBinaryExchangeShapes KroneckerRawBinaryEdits

/-- A gap at the end or immediately before a horizontal edge. -/
def RunBoundary (U : TNEPath) (i : ℕ) : Prop :=
  i = U.steps.length ∨ U.steps[i]? = some true

theorem Binary.isRun {U : TNEPath} (h : Binary U) : IsRun U := by
  obtain ⟨rs, hn, he, hr⟩ := h
  exact ⟨rs, hn, by intro r h; rcases hr r h with rfl | rfl <;> omega, he⟩

theorem binary_of_steps {U : TNEPath} {rs : List ℕ} (hs : U.steps = runWord rs)
    (hn : rs ≠ []) (hr : ∀ r ∈ rs, r = 1 ∨ r = 2) : Binary U := by
  refine ⟨rs, hn, ?_, hr⟩
  exact (by simpa only [hs, runPath] using (ofSteps_self U).symm)

theorem runBoundary_prefix (A B : List ℕ) (o : LatticePoint) :
    RunBoundary (runPath (A ++ B) o) (runWord A).length := by
  cases B with
  | nil => exact Or.inl (by simp)
  | cons b B =>
    right
    simp [runWord, KroneckerStack.runShape]

/-- On a binary run, the manuscript's edge condition determines a run split. -/
theorem binary_boundary_split (rs : List ℕ) (i : ℕ)
    (hr : ∀ r ∈ rs, r = 1 ∨ r = 2)
    (hi : i = (runWord rs).length ∨ (runWord rs)[i]? = some true) :
    ∃ A B : List ℕ, rs = A ++ B ∧ i = (runWord A).length := by
  induction rs generalizing i with
  | nil =>
    have hi0 : i = 0 := by simpa [runWord] using hi
    exact ⟨[], [], rfl, hi0⟩
  | cons r rs ih =>
    have ht : ∀ t ∈ rs, t = 1 ∨ t = 2 := fun t h => hr t (by simp [h])
    have hhead := hr r (by simp)
    rcases hhead with rfl | rfl
    · cases i with
      | zero => exact ⟨[], 1 :: rs, rfl, rfl⟩
      | succ i =>
        cases i with
        | zero => simp [runWord, KroneckerStack.runShape] at hi
        | succ i =>
          have hi' : i = (runWord rs).length ∨ (runWord rs)[i]? = some true := by
            change i+1+1 = (runWord rs).length+1+1 ∨ (runWord rs)[i]? = some true at hi
            simpa only [Nat.add_right_cancel_iff] using hi
          obtain ⟨A, B, he, hp⟩ := ih i ht hi'
          refine ⟨1 :: A, B, by simpa using he, ?_⟩
          simp [runWord, KroneckerStack.runShape] at hp ⊢
          omega
    · cases i with
      | zero => exact ⟨[], 2 :: rs, rfl, rfl⟩
      | succ i =>
        cases i with
        | zero => simp [runWord, KroneckerStack.runShape] at hi
        | succ i =>
          cases i with
          | zero => simp [runWord, KroneckerStack.runShape] at hi
          | succ i =>
            have hi' : i = (runWord rs).length ∨ (runWord rs)[i]? = some true := by
              change i+1+1+1 = (runWord rs).length+1+1+1 ∨ (runWord rs)[i]? = some true at hi
              simpa only [Nat.add_right_cancel_iff] using hi
            obtain ⟨A, B, he, hp⟩ := ih i ht hi'
            refine ⟨2 :: A, B, by simpa using he, ?_⟩
            simp [runWord, KroneckerStack.runShape] at hp ⊢
            omega

theorem BinaryProgram.target_binary {U V : TNEPath} {K k : ℕ}
    (p : BinaryProgram U V K k) (hU : Binary U) : Binary V := by
  induction p with
  | nil => exact hU
  | @insert A B o K k p r hr ih =>
    obtain ⟨hn, hl⟩ := (binary_runPath_iff (A ++ B) o).mp ih
    have hs : (KroneckerPaperPaths.insert (runPath (A ++ B) o) (runWord A).length (simpleRun r hr.1)).steps =
        runWord (A ++ r :: B) :=
      congrArg TNEPath.steps (insert_runPath_zero A B r hr.1)
    apply binary_of_steps hs (by simp)
    intro t ht
    simp only [List.mem_append, List.mem_cons] at ht
    rcases ht with h | rfl | h
    · exact hl t (by simp [h])
    · omega
    · exact hl t (by simp [h])
  | @exchange A B o K k right p ih =>
    rw [exchange_pairRuns]
    apply (binary_runPath_iff _ _).mpr
    refine ⟨by cases right <;> simp [pairRuns], ?_⟩
    have hl := ((binary_runPath_iff _ _).mp ih).2
    intro t ht
    apply hl t
    cases right <;> simpa [pairRuns, or_assoc, or_left_comm, or_comm] using ht

def RunEdit.IsBinaryStep {U V : TNEPath} : RunEdit U V → Prop
  | .complete .. => ∃ j s : ℕ, ∃ hs : 1≤s ∧ s≤2,
      j ≤ U.steps.length ∧ RunBoundary U j ∧ V = insert U j (simpleRun s hs.1)
  | .exchange _ _ _ _ r s _ => r ≠ s
  | .north .. => False
  | .delete .. => False

/-- Equal insertion outputs can change the gap, but not the inserted run length. -/
theorem complete_equal_output_length {U : TNEPath} (i j r s : ℕ)
    (hi : i ≤ U.steps.length) (hj : j ≤ U.steps.length) (hr : 0<r) (hs : 0<s)
    (he : insert U i (simpleRun r hr) = insert U j (simpleRun s hs)) : r=s := by
  have hlen := congrArg (fun P : TNEPath => P.steps.length) he
  simp only [insert_steps, List.length_append, List.length_take, List.length_drop,
    simpleRun_steps, List.length_cons, List.length_replicate] at hlen
  omega

theorem RunEdit.IsBinaryStep.complete_length {U : TNEPath} (hU : IsRun U)
    (i r : ℕ) (hi : i ≤ U.steps.length) (hr : 0<r)
    (h : (RunEdit.complete U hU i r hi hr).IsBinaryStep) : r=1 ∨ r=2 := by
  obtain ⟨j, s, hs, hj, _, he⟩ := h
  have heq := complete_equal_output_length i j r s hi hj hr hs.1 he
  omega

/-- The manuscript's output equality genuinely permits a different gap witness. -/
theorem complete_boundary_witness_can_relocate :
    ∃ hU : IsRun (runPath [2] 0),
      (RunEdit.complete (runPath [2] 0) hU 2 1 (by decide) (by decide)).IsBinaryStep ∧
        ¬RunBoundary (runPath [2] 0) 2 := by
  have hU : Binary (runPath [2] 0) := (binary_runPath_iff _ _).mpr (by simp)
  refine ⟨hU.isRun, ⟨0, 1, by decide, by decide, Or.inr rfl, ?_⟩,
    by simp [RunBoundary, runWord, KroneckerStack.runShape]⟩
  rfl

def RunEdit.insertionCount {U V : TNEPath} : RunEdit U V → ℕ
  | .complete .. => 1
  | _ => 0

def RunEdit.exchangeCount {U V : TNEPath} : RunEdit U V → ℕ
  | .exchange .. => 1
  | _ => 0

def RunEditList.IsBinary {U V : TNEPath} {n : ℕ} : RunEditList U V n → Prop
  | .nil _ => Binary U
  | .snoc ts t => ts.IsBinary ∧ t.IsBinaryStep ∧ Binary V

def RunEditList.insertionCount {U V : TNEPath} {n : ℕ} : RunEditList U V n → ℕ
  | .nil _ => 0
  | .snoc ts t => ts.insertionCount + t.insertionCount

def RunEditList.exchangeCount {U V : TNEPath} {n : ℕ} : RunEditList U V n → ℕ
  | .nil _ => 0
  | .snoc ts t => ts.exchangeCount + t.exchangeCount

/-- The actual subset of length K+k run-edit lists in the manuscript. -/
def BinEdit (K k : ℕ) (U V : TNEPath) :=
  {Ω : RunEditList U V (K + k) //
    Ω.IsBinary ∧ Ω.insertionCount = K ∧ Ω.exchangeCount = k}

theorem RunEditList.IsBinary.source {U V : TNEPath} {n : ℕ}
    {Ω : RunEditList U V n} (h : Ω.IsBinary) : Binary U := by
  induction Ω with
  | nil => exact h
  | snoc ts t ih => exact ih h.1

theorem RunEditList.IsBinary.target {U V : TNEPath} {n : ℕ}
    {Ω : RunEditList U V n} (h : Ω.IsBinary) : Binary V := by
  cases Ω with
  | nil => exact h
  | snoc => exact h.2.2

theorem RunEditList.IsBinary.length_eq {U V : TNEPath} {n : ℕ}
    {Ω : RunEditList U V n} (h : Ω.IsBinary) :
    n = Ω.insertionCount + Ω.exchangeCount := by
  induction Ω with
  | nil => rfl
  | snoc ts t ih =>
    have he := ih h.1
    have ht := h.2.1
    cases t <;> simp_all [RunEdit.IsBinaryStep, RunEditList.insertionCount,
      RunEditList.exchangeCount, RunEdit.insertionCount, RunEdit.exchangeCount] <;> omega

theorem BinaryProgram.permitted_list {U V : TNEPath} {K k : ℕ}
    (p : BinaryProgram U V K k) (hU : Binary U) :
    ∃ n, ∃ Ω : RunEditList U V n,
      Ω.IsBinary ∧ Ω.insertionCount = K ∧ Ω.exchangeCount = k := by
  induction p with
  | nil => exact ⟨0, .nil hU.isRun, hU, rfl, rfl⟩
  | @insert A B o K k p r hr ih =>
    obtain ⟨n, Ω, hΩ, hK, hk⟩ := ih
    have hb := p.target_binary hU
    have hi : (runWord A).length ≤ (runPath (A ++ B) o).steps.length := by
      simp [runWord]
    let t := RunEdit.complete _ hb.isRun (runWord A).length r hi hr.1
    refine ⟨n+1, .snoc Ω t, ⟨hΩ, ?_, (BinaryProgram.insert p r hr).target_binary hU⟩,
      by simp [t, RunEditList.insertionCount, RunEdit.insertionCount, hK],
      by simpa [t, RunEditList.exchangeCount, RunEdit.exchangeCount] using hk⟩
    exact ⟨(runWord A).length, r, hr, hi, runBoundary_prefix A B o, rfl⟩
  | @exchange A B o K k right p ih =>
    obtain ⟨n, Ω, hΩ, hK, hk⟩ := ih
    have hb := p.target_binary hU
    have ho : (runPath (A ++ pairRuns right ++ B) o).origin = o :=
      runPath_origin _ o (by cases right <;> simp [pairRuns])
    cases right
    · let t := RunEdit.exchange _ hb.isRun A B 2 1 (by rw [ho]; rfl)
      exact ⟨n+1, .snoc Ω t, ⟨hΩ, by change 2 ≠ 1; omega,
        (BinaryProgram.exchange false p).target_binary hU⟩,
        by simpa [t, RunEditList.insertionCount, RunEdit.insertionCount] using hK,
        by simp [t, RunEditList.exchangeCount, RunEdit.exchangeCount, hk]⟩
    · let t := RunEdit.exchange _ hb.isRun A B 1 2 (by rw [ho]; rfl)
      exact ⟨n+1, .snoc Ω t, ⟨hΩ, by change 1 ≠ 2; omega,
        (BinaryProgram.exchange true p).target_binary hU⟩,
        by simpa [t, RunEditList.insertionCount, RunEdit.insertionCount] using hK,
        by simp [t, RunEditList.exchangeCount, RunEdit.exchangeCount, hk]⟩

/-- Each permitted list yields a program with its exact endpoints and counts. -/
theorem RunEditList.IsBinary.reify {U V : TNEPath} {n : ℕ}
    {Ω : RunEditList U V n} (h : Ω.IsBinary) :
    Nonempty (BinaryProgram U V Ω.insertionCount Ω.exchangeCount) := by
  induction Ω with
  | nil => exact ⟨.nil⟩
  | @snoc V W n Ω t ih =>
    obtain ⟨p⟩ := ih h.1
    have hb := h.1.target
    have ht := h.2.1
    cases t with
    | north => exact ht.elim
    | delete => exact ht.elim
    | complete hRun i r hi hr =>
      obtain ⟨j, s, hs, hj, hboundary, hout⟩ := ht
      obtain ⟨rs, hn, he, hl⟩ := hb
      have hsteps : V.steps = runWord rs := congrArg TNEPath.steps he
      have hboundary' : j = (runWord rs).length ∨ (runWord rs)[j]? = some true := by
        simpa only [RunBoundary, hsteps] using hboundary
      obtain ⟨A, B, hsplit, hpos⟩ := binary_boundary_split rs j hl hboundary'
      have hV : V = runPath (A ++ B) V.origin := by rwa [hsplit] at he
      have hp : BinaryProgram U (runPath (A ++ B) V.origin)
          Ω.insertionCount Ω.exchangeCount := hV ▸ p
      change Nonempty (BinaryProgram U (insert V i (simpleRun r hr))
        (Ω.insertionCount+1) (Ω.exchangeCount+0))
      have heq : insert V i (simpleRun r hr) =
          insert (runPath (A ++ B) V.origin) (runWord A).length (simpleRun s hs.1) :=
        hout.trans (congrArg₂ (fun W b => insert W b (simpleRun s hs.1)) hV hpos)
      exact ⟨heq.symm ▸ (BinaryProgram.insert hp s hs)⟩
    | exchange hRun A B r s he =>
      change r ≠ s at ht
      have hletters := ((binary_runPath_iff _ _).mp (he ▸ hb)).2
      have hr := hletters r (by simp)
      have hs := hletters s (by simp)
      change Nonempty (BinaryProgram U (exchangeRuns V A.length)
        (Ω.insertionCount+0) (Ω.exchangeCount+1))
      rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
      · exact (ht rfl).elim
      · exact ⟨(congrArg (fun W => exchangeRuns W A.length) he).symm ▸
          (BinaryProgram.exchange true (he ▸ p))⟩
      · exact ⟨(congrArg (fun W => exchangeRuns W A.length) he).symm ▸
          (BinaryProgram.exchange false (he ▸ p))⟩
      · exact (ht rfl).elim

theorem binaryProgram_iff_binEdit {U V : TNEPath} {K k : ℕ} :
    (Binary U ∧ Nonempty (BinaryProgram U V K k)) ↔ Nonempty (BinEdit K k U V) := by
  constructor
  · rintro ⟨hU, ⟨p⟩⟩
    obtain ⟨n, Ω, hΩ, hK, hk⟩ := p.permitted_list hU
    have hn : n = K+k := by simpa only [hK, hk] using hΩ.length_eq
    subst n
    exact ⟨⟨Ω, hΩ, hK, hk⟩⟩
  · rintro ⟨⟨Ω, hΩ, hK, hk⟩⟩
    exact ⟨hΩ.source, by simpa only [hK, hk] using hΩ.reify⟩

def BinaryProgram.toBinEdit {U V : TNEPath} {K k : ℕ}
    (p : BinaryProgram U V K k) (hU : Binary U) : BinEdit K k U V :=
  Classical.choice (binaryProgram_iff_binEdit.mp ⟨hU, ⟨p⟩⟩)

def BinEdit.toProgram {U V : TNEPath} {K k : ℕ} (Ω : BinEdit K k U V) :
    BinaryProgram U V K k :=
  Classical.choice (binaryProgram_iff_binEdit.mpr ⟨Ω⟩).2

def BinaryProgram.toRaw {U V : TNEPath} {K k : ℕ}
    (p : BinaryProgram U V K k) :
    RawBinary (decodeRuns U.steps).2 (decodeRuns V.steps).2 K k := by
  induction p with
  | nil => exact .nil
  | @insert A B o K k p r hr ih =>
    have hs : (KroneckerPaperPaths.insert (runPath (A ++ B) o) (runWord A).length
        (simpleRun r hr.1)).steps = runWord (A ++ r :: B) :=
      congrArg TNEPath.steps (insert_runPath_zero A B r hr.1)
    simp only [hs, runPath_steps, decodeRuns_runWord] at ih ⊢
    exact .insert ih r hr
  | @exchange A B o K k right p ih =>
    simp only [exchange_pairRuns, runPath_steps, decodeRuns_runWord] at ih ⊢
    exact .exchange right ih

theorem Binary.steps_decode {U : TNEPath} (h : Binary U) :
    U.steps = runWord (decodeRuns U.steps).2 := by
  obtain ⟨rs, _, he, _⟩ := h
  have hs := congrArg TNEPath.steps he
  simp only [hs, runPath_steps, decodeRuns_runWord]

/-- Insertion after a nonempty run prefix keeps the exact lattice origin. -/
theorem insert_runPath_nonempty_prefix (A B : List ℕ) (o : LatticePoint)
    (r : ℕ) (hr : 0<r) (hA : A ≠ []) :
    insert (runPath (A ++ B) o) (runWord A).length (simpleRun r hr) =
      runPath (A ++ r :: B) o := by
  have hword : runWord A ≠ [] := fun h => hA (runWord_injective h)
  have hlen : (runWord A).length ≠ 0 := fun h => hword (List.length_eq_zero_iff.mp h)
  have hall : runWord (A ++ B) ≠ [] := by
    intro h
    exact hA (List.append_eq_nil_iff.mp (runWord_injective h)).1
  have hs : (runWord (A++B)).take (runWord A).length ++ (simpleRun r hr).steps ++
      (runWord (A++B)).drop (runWord A).length = runWord (A ++ r :: B) :=
    congrArg TNEPath.steps (insert_runPath_zero A B r hr)
  simp only [insert, runPath_steps, hs, hlen, false_and, ↓reduceIte, hall]
  rw [runPath_origin _ o (by intro h; exact hA (List.append_eq_nil_iff.mp h).1)]
  rfl

def BinaryProgram.append {U V W : TNEPath} {K J k j : ℕ}
    (p : BinaryProgram U V K k) (q : BinaryProgram V W J j) :
    BinaryProgram U W (K+J) (k+j) := by
  induction q with
  | nil => simpa using p
  | insert q r hr ih => simpa only [Nat.add_assoc] using BinaryProgram.insert ih r hr
  | exchange right q ih => simpa only [Nat.add_assoc] using BinaryProgram.exchange right ih

open KroneckerBinarySwapRuns KroneckerBinarySwapPrograms

def swapsToBinary {X Y : List Bool} {k : ℕ} (p : Swaps X Y k) (o : LatticePoint) :
    BinaryProgram (runPath (bitRuns X) o) (runPath (bitRuns Y) o) 0 k := by
  induction p with
  | nil => exact .nil
  | @step pre post k right p ih =>
    have q : BinaryProgram (runPath (bitRuns X) o)
        (runPath (bitRuns pre ++ pairRuns right ++ bitRuns post) o) 0 k := by
      simpa only [bitRuns, List.map_append, ← bitRuns_pair] using ih
    have h := BinaryProgram.exchange right q
    rw [exchange_pairRuns] at h
    simpa only [bitRuns, List.map_append, ← bitRuns_pair] using h

def appendBitsFixed (xs as : List Bool) (o : LatticePoint) (hxs : xs ≠ []) :
    BinaryProgram (runPath (bitRuns xs) o) (runPath (bitRuns (xs++as)) o) as.length 0 := by
  induction as with
  | nil => simpa using (BinaryProgram.nil :
      BinaryProgram (runPath (bitRuns xs) o) (runPath (bitRuns xs) o) 0 0)
  | cons b as ih =>
    have hp : BinaryProgram (runPath (bitRuns xs) o)
        (runPath (bitRuns xs ++ bitRuns as) o) as.length 0 := by
      simpa only [bitRuns, List.map_append] using ih
    have hr : 1 ≤ (if b then 2 else 1 : ℕ) ∧ (if b then 2 else 1 : ℕ) ≤ 2 := by
      cases b <;> decide
    have hpre : bitRuns xs ≠ [] := by simpa [bitRuns] using hxs
    have hh := BinaryProgram.insert hp (if b then 2 else 1) hr
    rw [insert_runPath_nonempty_prefix _ _ _ _ _ hpre] at hh
    simpa only [bitRuns, List.map_append, List.map_cons, List.length_cons] using hh

open KroneckerBinaryBalancingLetters KroneckerBinaryGreedyExchange
open KroneckerBinaryPrefixArea KroneckerBinaryBalancedArea

theorem insertion_exchange_fixed (xs ys : List Bool) (o : LatticePoint) (hxs : xs ≠ [])
    (hc : ∀ b : Bool, xs.count b ≤ ys.count b) :
    ∃ k, Nonempty (BinaryProgram (runPath (bitRuns xs) o) (runPath (bitRuns ys) o)
      (ys.length-xs.length) k) ∧ k ≤ ys.length^2 := by
  let as := balancingLetters xs ys
  have hl : (xs++as).length = ys.length := by
    simpa only [List.length_append] using balancing_length xs ys hc
  have ht : (xs++as).count true = ys.count true := balancing_counts xs ys hc true
  have hb : (0 : ℤ)+((xs++as).count true : ℤ)-(ys.count true : ℤ)=0 := by omega
  have hbound := prefixArea_balanced_le_sq 0 (xs++as) ys hl hb
  rw [hl] at hbound
  refine ⟨swapDistance (xs++as) ys, ?_, hbound⟩
  have p := (appendBitsFixed xs as o hxs).append (swapsToBinary (areaProgram (xs++as) ys hl ht) o)
  exact ⟨by simpa only [Nat.add_zero, Nat.zero_add, as, balancing_length_sub xs ys hc] using p⟩

open KroneckerMechanicalWords KroneckerMechanicalBits KroneckerBinaryTerminalWord
open KroneckerBinaryTerminalDomination KroneckerMechanicalLetterBounds KroneckerMechanicalWordShift

theorem exceptional_final_fixed_program (s u t v : ℝ) (a C p z : ℕ)
    (ha : 0<a) (hs : 1<s ∧ s<2) (ht : 1<t ∧ t<2) (hz : z=1 ∨ z=2)
    (hbudget : 3+(a : ℝ)*|s-t| < (C : ℝ)*min (t-1) (2-t)) (o : LatticePoint) :
    ∃ k, Nonempty (BinaryProgram (runPath (mechanicalWord s u 0 (a-1) ++ [z]) o)
      (runPath (mechanicalWord t v p (a+C)) o) C k) ∧ k ≤ (a+C)^2 := by
  have hm : ∀ b : Bool, min (t-1) (2-t) ≤ frequency t b := by
    intro b
    cases b
    · exact min_le_right _ _
    · exact min_le_left _ _
  have hn : a-1+1=a := by omega
  have hfixed (b : Bool) := insertion_exchange_fixed (terminalBits s u (a-1) b)
    (mechanicalBits t (v+(p : ℝ)*t) (a-1+1+C)) o (by simp [terminalBits])
    (terminal_count_domination s u t (v+(p : ℝ)*t) (min (t-1) (2-t)) |s-t|
      (a-1) C b ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ hm le_rfl
      (by simpa only [hn] using hbudget.le))
  rcases hz with rfl | rfl
  · simpa only [terminalBits_runs s u (a-1) false ⟨hs.1.le, hs.2.le⟩,
      mechanicalBits_runs t (v+(p : ℝ)*t) (a+C) ⟨ht.1.le, ht.2.le⟩,
      terminalBits_length, mechanicalBits_length, Nat.add_sub_cancel_left,
      hn, ← word_shift, Bool.false_eq_true, ↓reduceIte] using hfixed false
  · simpa only [terminalBits_runs s u (a-1) true ⟨hs.1.le, hs.2.le⟩,
      mechanicalBits_runs t (v+(p : ℝ)*t) (a+C) ⟨ht.1.le, ht.2.le⟩,
      terminalBits_length, mechanicalBits_length, Nat.add_sub_cancel_left,
      hn, ← word_shift, ↓reduceIte] using hfixed true

theorem exceptional_final_binEdit_fixed (s u t v : ℝ) (a C p z : ℕ)
    (ha : 0<a) (hs : 1<s ∧ s<2) (ht : 1<t ∧ t<2) (hz : z=1 ∨ z=2)
    (hbudget : 3+(a : ℝ)*|s-t| < (C : ℝ)*min (t-1) (2-t)) (o : LatticePoint) :
    ∃ k, Nonempty (BinEdit C k (runPath (mechanicalWord s u 0 (a-1) ++ [z]) o)
      (runPath (mechanicalWord t v p (a+C)) o)) ∧ k ≤ (a+C)^2 := by
  obtain ⟨k, hp, hk⟩ := exceptional_final_fixed_program s u t v a C p z ha hs ht hz hbudget o
  refine ⟨k, binaryProgram_iff_binEdit.mp ⟨?_, hp⟩, hk⟩
  apply (binary_runPath_iff _ _).mpr
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with h | rfl
  · have := mechanicalWord_legal s u 0 (a-1) 2 hs.1.le hs.2.le r h
    omega
  · exact hz

open KroneckerCurrentMechanicalNotation KroneckerManuscriptMechanicalDefinitions

theorem displacement_counts (w : List Bool) :
    displacement w = ((w.count true : ℤ), (w.count false : ℤ)) := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [displacement, stepVector, ih, add_comm]

theorem runWord_displacement (rs : List ℕ) :
    displacement (runWord rs) = ((rs.length : ℤ), (rs.sum : ℤ)) := by
  rw [displacement_counts]
  have he := runPath_east_count rs 0
  have hn := runPath_north_count rs 0
  simp only [runPath_steps] at he hn
  rw [he, hn]

theorem mechRunFactor_origin (s u : ℝ) (p ℓ : ℕ) (hℓ : 0<ℓ)
    (hs : 0≤s) (hu : 0≤u ∧ u<1) :
    (MechRunFactor s u (p+1) ℓ).origin = ((p : ℤ), ⌊u+(p : ℝ)*s⌋) := by
  have htail : mechanicalWord s u p ℓ ≠ [] := by
    intro he
    have := congrArg List.length he
    rw [mechanicalWord_length] at this
    simp only [List.length_nil] at this
    omega
  have hword : 0 < (runWord (mechanicalWord s u p ℓ)).length := by
    apply Nat.pos_of_ne_zero
    intro he
    exact htail (runWord_injective (List.length_eq_zero_iff.mp he))
  unfold MechRunFactor RunFactor ccsRunFactor
  simp only [Nat.add_sub_cancel,
    List.take_of_length_le (Nat.le_of_eq (mechanicalWord_length s u 0 (p+ℓ)))]
  rw [KroneckerNearbyShortFactor.word_take s u (p+ℓ) p (by omega)]
  rw [KroneckerMechanicalWordSums.mechanicalWord_append s u 0 p ℓ]
  simp only [Nat.zero_add]
  rw [subpath_origin _ _ _ (by
    simp only [runWord, List.flatMap_append, List.length_append]
    simpa only [runWord] using Nat.lt_add_of_pos_right hword) (by rfl)]
  simp only [vertex, runPath_steps]
  rw [runPath_origin _ 0 (by intro he; exact htail (List.append_eq_nil_iff.mp he).2)]
  simp only [zero_add]
  rw [show runWord (mechanicalWord s u 0 p ++ mechanicalWord s u p ℓ) =
    runWord (mechanicalWord s u 0 p) ++ runWord (mechanicalWord s u p ℓ) by simp [runWord]]
  rw [List.take_left, runWord_displacement, mechanicalWord_length,
    KroneckerMechanicalWordSums.mechanicalWord_sum_cast s u 0 p hs]
  simp [KroneckerMechanicalRuns.mechanicalPrefix, Int.floor_eq_zero_iff.mpr hu]

theorem mechRunFactor_translate_origin (s u : ℝ) (p ℓ : ℕ) (hℓ : 0<ℓ)
    (hs : 0≤s) (hu : 0≤u ∧ u<1) (o : LatticePoint) :
    translate (MechRunFactor s u (p+1) ℓ) (o-((p : ℤ), ⌊u+(p : ℝ)*s⌋)) =
      runPath (mechanicalWord s u p ℓ) o := by
  rw [← mechRunFactor_origin s u p ℓ hℓ hs hu, translate_to_origin,
    MechRunFactor_steps, Nat.add_sub_cancel]
  rfl

/-- The exceptional conclusion with the manuscript's exact prescribed translation. -/
theorem exceptional_final_binEdit (s u t v : ℝ) (a C p z : ℕ)
    (ha : 0<a) (hs : 1<s ∧ s<2) (ht : 1<t ∧ t<2)
    (hv : 0≤v ∧ v<1) (hz : z=1 ∨ z=2)
    (hbudget : 3+(a : ℝ)*|s-t| < (C : ℝ)*min (t-1) (2-t))
    (X : TNEPath) (hX : X = runPath (mechanicalWord s u 0 (a-1) ++ [z]) X.origin) :
    ∃ k, Nonempty (BinEdit C k X
      (translate (MechRunFactor t v (p+1) (a+C))
        (X.origin-((p : ℤ), ⌊v+(p : ℝ)*t⌋)))) ∧ k ≤ (a+C)^2 := by
  have h := exceptional_final_binEdit_fixed s u t v a C p z ha hs ht hz hbudget X.origin
  rw [mechRunFactor_translate_origin t v p (a+C) (by omega) (by linarith [ht.1]) hv X.origin]
  obtain ⟨k, hp, hk⟩ := h
  refine ⟨k, ?_, hk⟩
  exact Eq.mpr (congrArg (fun W => Nonempty
    (BinEdit C k W (runPath (mechanicalWord t v p (a+C)) X.origin))) hX) hp

/-- The mechanical-factor conclusion with an explicit member of BinEdit. -/
theorem mechanical_factor_binEdit (r η : ℝ) (hr : Irrational r)
    (hrb : 1<r ∧ r<2) (hη : 0<η) (hη4 : η<1/4) :
    ∃ L : ℕ, 0<L ∧ ∃ δ : ℝ, 0<δ ∧
      (KroneckerBinaryFactorLemmas.padding r : ℝ) ≤ η*L ∧
      δ < min (KroneckerBinaryFactorLemmas.margin r) (η/(4*L)) ∧
      ∀ s t u v : ℝ, |s-r|<δ → |t-r|<δ →
      (0≤u ∧ u<1) → (0≤v ∧ v<1) → ∀ p : ℕ, ∀ o : LatticePoint,
      ∃ j k : ℕ, ((KroneckerBinaryFactorLemmas.padding r+j : ℕ) : ℝ) ≤ η*L ∧
        (∃ ζ : LatticePoint, Nonempty (BinEdit (KroneckerBinaryFactorLemmas.padding r+j) k
          (runPath (mechanicalWord s u 0 L) o)
          (translate (MechRunFactor t v (p+1) (L+KroneckerBinaryFactorLemmas.padding r+j)) ζ))) ∧
        (k : ℝ) ≤ 7*η*L := by
  obtain ⟨L, hL, δ, hδ, hC, hd, h⟩ :=
    KroneckerBinaryFactorLemmas.mechanical_factor_comparison r η hr hrb hη hη4
  refine ⟨L, hL, δ, hδ, hC, hd, ?_⟩
  intro s t u v hs ht hu hv p o
  obtain ⟨j, k, hj, ⟨prog⟩, hk⟩ := h s t u v hs ht hu hv p
  obtain ⟨Q, ⟨q⟩, hq⟩ := rawBinary_realization prog o
  have hm := KroneckerBinaryFactorLemmas.margin_pos hrb
  have hsb := KroneckerBinaryFactorLemmas.nearby_margins (hd.trans_le (min_le_left _ _)) hs
  have hU : Binary (runPath (mechanicalWord s u 0 L) o) := by
    apply (binary_runPath_iff _ _).mpr
    refine ⟨?_, ?_⟩
    · intro he
      have := congrArg List.length he
      rw [mechanicalWord_length] at this
      simp only [List.length_nil] at this
      omega
    · intro a ha
      have := mechanicalWord_legal s u 0 L 2 (by linarith [hsb.1])
        (by norm_num; linarith [hsb.2]) a ha
      omega
  let F := MechRunFactor t v (p+1) (L+KroneckerBinaryFactorLemmas.padding r+j)
  have he : translate F (Q.origin-F.origin) = Q := same_steps_translation (by
    simpa only [F, MechRunFactor_steps, Nat.add_sub_cancel] using hq.symm)
  refine ⟨j, k, hj, ⟨Q.origin-F.origin, ?_⟩, hk⟩
  rw [he]
  exact binaryProgram_iff_binEdit.mp ⟨hU, ⟨q⟩⟩

/-- Whole mechanical comparisons, with the manuscript's binary source retained. -/
theorem binary_mechanical_binEdit (r η : ℝ) (hr : Irrational r)
    (hrb : 1<r ∧ r<2) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ ∃ B : ℕ, 0<B ∧ ∀ s t u v : ℝ,
      |s-r|<δ → |t-r|<δ → ∀ l T : ℕ, ∀ R : List ℕ,
      KroneckerBinaryMechanicalSource.BinaryMechanicalSource s u l R →
      (1+η)*(l : ℝ)+(B : ℝ) ≤ T → ∀ U : TNEPath, Binary U → U.steps = runWord R →
      ∃ k, (∃ ζ : LatticePoint, Nonempty (BinEdit (T-l) k U
        (translate (MechRunFactor t v 1 T) ζ))) ∧ (k : ℝ) ≤ 7*η*(l : ℝ)+B := by
  obtain ⟨δ, hδ, B, hB, hall⟩ := binary_mechanical_paths r η hr hrb hη
  refine ⟨δ, hδ, B, hB, ?_⟩
  intro s t u v hs ht l T R hR hT U hU hsteps
  obtain ⟨k, ⟨w, ⟨p⟩⟩, hk⟩ := hall s t hs ht u v l T R hR hT U.origin
  have he : U = runPath R U.origin := by
    exact (by simpa only [hsteps, runPath] using (ofSteps_self U).symm)
  refine ⟨k, ⟨w, ?_⟩, hk⟩
  rw [MechRunFactor_one]
  have hp := binaryProgram_iff_binEdit.mp ⟨he ▸ hU, ⟨p⟩⟩
  exact Eq.mpr (congrArg (fun X => Nonempty (BinEdit (T-l) k X
    (translate (runPath (mechanicalWord t v 0 T) 0) w))) he) hp

end KroneckerPaperPaths

namespace KroneckerManuscriptBinaryEditClaims
open KroneckerPaperPaths KroneckerWordCounts KroneckerColoredShell KroneckerCollarColoring
open KroneckerPrescribedLayerSplit KroneckerPrescribedCollars KroneckerRawBinaryEdits
open KroneckerRawBinaryLift KroneckerThreeLayerBudget KroneckerThreeBufferedCount
open KroneckerThreeMixedPrograms KroneckerThreeMixedRecovery KroneckerBinaryProgramCode

def wordColoringCongr {m c : ℕ} {U V : List Bool} (h : U = V) :
    ConnectedColorings m U c ≃ ConnectedColorings m V c :=
  Equiv.cast (congrArg (fun W => ConnectedColorings m W c) h)

def prescribedPairProgram {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (p : RawBinary R S K k) (pairs : List (ℕ×ℕ))
    (hp : LegalPairs 3 pairs) (hs : K+4*k ≤ pairs.length) :
    ThreeProgram (shellPath u v (runWord R))
      (collarPath (pairs.drop (pairs.length-k)) (shellPath u v (runWord S))) K k :=
  liftRawBinary p (pairs.drop (pairs.length-k)) (three_layer_lengths pairs hs).1
    (legal_pairs_sublist (List.drop_sublist _ pairs) hp)

def prescribedPairMap {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (hs : K+4*k ≤ pairs.length) :
    ConnectedColorings 3 (runWord R) 0 →
      ConnectedColorings 3 (collarPath pairs (shellPath u v (runWord S))) 0 :=
  fun g => wordColoringCongr (by rw [← collarPath_append, List.take_append_drop])
    (bufferedThree hu hv (prescribedPairProgram p pairs hp hs)
      (pairs.take (pairs.length-k)) (legal_pairs_sublist (List.take_sublist _ pairs) hp)
      (three_layer_lengths pairs hs).2 g)

def prescribedPairCode {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (hs : K+4*k ≤ pairs.length)
    (g : ConnectedColorings 3 (runWord R) 0) : Code k :=
  threeCode (prescribedPairProgram p pairs hp hs)
    ⟨0, unaryShell u v 0 (by decide) hu hv (runWord R) g⟩

theorem prescribedPair_target_code_injective {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (hs : K+4*k ≤ pairs.length) :
    Function.Injective (fun g =>
      (prescribedPairMap hu hv p pairs hp hs g, prescribedPairCode hu hv p pairs hp hs g)) := by
  intro g h he
  apply buffered_target_code_injective hu hv (prescribedPairProgram p pairs hp hs)
    (pairs.take (pairs.length-k)) (legal_pairs_sublist (List.take_sublist _ pairs) hp)
    (three_layer_lengths pairs hs).2
  apply Prod.ext
  · exact (wordColoringCongr (by rw [← collarPath_append, List.take_append_drop])).injective
      (congrArg Prod.fst he)
  · exact (Prod.mk.inj he).2

theorem fiber_le_pow {α β : Type} {k : ℕ} (f : α → β) (code : α → Code k)
    (hi : Function.Injective (fun a => (f a, code a))) (b : β) :
    Nat.card {a // f a = b} ≤ 8^k := by
  classical
  have hc : Function.Injective (fun a : {a // f a = b} => code a.val) := by
    intro a a' he
    apply Subtype.ext
    exact hi (Prod.ext (a.property.trans a'.property.symm) he)
  let := Fintype.ofInjective _ hc
  have hh := Fintype.card_le_of_injective _ hc
  simpa only [Nat.card_eq_fintype_card, code_card] using hh

theorem prescribedPair_fiber {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs 3 pairs) (hs : K+4*k ≤ pairs.length)
    (b : ConnectedColorings 3 (collarPath pairs (shellPath u v (runWord S))) 0) :
    Nat.card {a // prescribedPairMap hu hv p pairs hp hs a = b} ≤ 8^k :=
  fiber_le_pow _ _ (prescribedPair_target_code_injective hu hv p pairs hp hs) b

/-- Prescribed left and right collars are paired in their actual traversal order. -/
def prescribedRunMap {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (A B : List ℕ) (hA : ∀ r∈A, 1≤r ∧ r≤2) (hB : ∀ r∈B, 1≤r ∧ r≤2)
    (hlen : A.length = B.length) (hs : K+4*k ≤ A.length) :
    ConnectedColorings 3 (runWord R) 0 →
      ConnectedColorings 3 (runWord (A ++ (u :: S ++ [v]) ++ B)) 0 :=
  fun g => wordColoringCongr (by rw [shellPath_runWord, pairCollars_path A B _ hlen])
    (prescribedPairMap hu hv p (pairCollars A B) (pairCollars_legal 3 A B hA hB)
      (by rwa [pairCollars_length A B hlen]) g)

def prescribedRunCode {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (A B : List ℕ) (hA : ∀ r∈A, 1≤r ∧ r≤2) (hB : ∀ r∈B, 1≤r ∧ r≤2)
    (hlen : A.length = B.length) (hs : K+4*k ≤ A.length) :
    ConnectedColorings 3 (runWord R) 0 → Code k :=
  prescribedPairCode hu hv p (pairCollars A B) (pairCollars_legal 3 A B hA hB)
    (by rwa [pairCollars_length A B hlen])

theorem prescribedRun_target_code_injective {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (A B : List ℕ) (hA : ∀ r∈A, 1≤r ∧ r≤2) (hB : ∀ r∈B, 1≤r ∧ r≤2)
    (hlen : A.length = B.length) (hs : K+4*k ≤ A.length) :
    Function.Injective (fun g =>
      (prescribedRunMap hu hv p A B hA hB hlen hs g,
       prescribedRunCode hu hv p A B hA hB hlen hs g)) := by
  intro g h he
  apply prescribedPair_target_code_injective hu hv p (pairCollars A B)
    (pairCollars_legal 3 A B hA hB) (by rwa [pairCollars_length A B hlen])
  apply Prod.ext
  · exact (wordColoringCongr (by rw [shellPath_runWord, pairCollars_path A B _ hlen])).injective
      (congrArg Prod.fst he)
  · exact (Prod.mk.inj he).2

theorem prescribedRun_fiber {u v : ℕ} {R S : List ℕ} {K k : ℕ}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (p : RawBinary R S K k)
    (A B : List ℕ) (hA : ∀ r∈A, 1≤r ∧ r≤2) (hB : ∀ r∈B, 1≤r ∧ r≤2)
    (hlen : A.length = B.length) (hs : K+4*k ≤ A.length)
    (b : ConnectedColorings 3 (runWord (A ++ (u :: S ++ [v]) ++ B)) 0) :
    Nat.card {a // prescribedRunMap hu hv p A B hA hB hlen hs a = b} ≤ 8^k :=
  fiber_le_pow _ _ (prescribedRun_target_code_injective hu hv p A B hA hB hlen hs) b

/-- Exact natural geometric gradings, through the proved one-based color dictionary. -/
def naturalWordEquiv (m : ℕ) (U : TNEPath) (c : ℕ) :
    KroneckerNaturalPathGradings.ConnectedColorings m U c ≃ ConnectedColorings m U.steps c :=
  (KroneckerNaturalPathGradings.connectedColoringEquiv m U c).trans
    ((KroneckerPaperPathGradings.connectedColoringEquiv m U c).trans
      (KroneckerPaperColors.operationalColoringEquiv (pathShape U.steps) c))

def binaryWordEquiv (m : ℕ) {U : TNEPath} (h : Binary U) (c : ℕ) :
    KroneckerNaturalPathGradings.ConnectedColorings m U c ≃
      ConnectedColorings m (runWord (decodeRuns U.steps).2) c :=
  (naturalWordEquiv m U c).trans (wordColoringCongr h.steps_decode)

theorem binary_decode_letters {U : TNEPath} (h : Binary U) :
    ∀ r ∈ (decodeRuns U.steps).2, 1≤r ∧ r≤2 := by
  obtain ⟨rs, hn, he, hr⟩ := h
  have hs : U.steps = runWord rs := congrArg TNEPath.steps he
  simp only [hs, decodeRuns_runWord]
  intro r ht
  rcases hr r ht with rfl | rfl <;> omega

def prescribedTarget {u v : ℕ} (hu : 0<u) (hv : 0<v) (V L R : TNEPath) : TNEPath :=
  concat L (concat (simpleRun u hu) (concat V (concat (simpleRun v hv) R)))

theorem prescribedTarget_steps {u v : ℕ} (hu : 0<u) (hv : 0<v)
    {V L R : TNEPath} (hV : Binary V) (hL : Binary L) (hR : Binary R) :
    (prescribedTarget hu hv V L R).steps =
      runWord ((decodeRuns L.steps).2 ++ (u :: (decodeRuns V.steps).2 ++ [v]) ++
        (decodeRuns R.steps).2) := by
  simp only [prescribedTarget, concat_steps, simpleRun_steps]
  rw [hL.steps_decode, hV.steps_decode, hR.steps_decode]
  simp only [decodeRuns_runWord]
  simp [runWord, List.append_assoc, KroneckerStack.runShape]

def prescribedTargetEquiv {u v : ℕ} (hu : 0<u) (hv : 0<v)
    {V L R : TNEPath} (hV : Binary V) (hL : Binary L) (hR : Binary R) :
    KroneckerNaturalPathGradings.ConnectedColorings 3 (prescribedTarget hu hv V L R) 0 ≃
      ConnectedColorings 3
        (runWord ((decodeRuns L.steps).2 ++ (u :: (decodeRuns V.steps).2 ++ [v]) ++
          (decodeRuns R.steps).2)) 0 :=
  (naturalWordEquiv 3 _ 0).trans (wordColoringCongr (prescribedTarget_steps hu hv hV hL hR))

/-- The prescribed-collar map for any member of the manuscript's BinEdit set. -/
def prescribedBinaryMap {u v K k : ℕ} {U V L R : TNEPath}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (Ω : BinEdit K k U V)
    (hL : Binary L) (hR : Binary R)
    (hlen : (decodeRuns L.steps).2.length = (decodeRuns R.steps).2.length)
    (hs : K+4*k ≤ (decodeRuns L.steps).2.length) :
    KroneckerNaturalPathGradings.ConnectedColorings 3 U 0 →
      KroneckerNaturalPathGradings.ConnectedColorings 3 (prescribedTarget hu.1 hv.1 V L R) 0 :=
  fun g => (prescribedTargetEquiv hu.1 hv.1 Ω.property.1.target hL hR).symm
    (prescribedRunMap hu hv Ω.toProgram.toRaw (decodeRuns L.steps).2 (decodeRuns R.steps).2
      (binary_decode_letters hL) (binary_decode_letters hR) hlen hs
      (binaryWordEquiv 3 Ω.property.1.source 0 g))

def prescribedBinaryCode {u v K k : ℕ} {U V L R : TNEPath}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (Ω : BinEdit K k U V)
    (hL : Binary L) (hR : Binary R)
    (hlen : (decodeRuns L.steps).2.length = (decodeRuns R.steps).2.length)
    (hs : K+4*k ≤ (decodeRuns L.steps).2.length) :
    KroneckerNaturalPathGradings.ConnectedColorings 3 U 0 → Code k :=
  fun g => prescribedRunCode hu hv Ω.toProgram.toRaw
    (decodeRuns L.steps).2 (decodeRuns R.steps).2
    (binary_decode_letters hL) (binary_decode_letters hR) hlen hs
    (binaryWordEquiv 3 Ω.property.1.source 0 g)

theorem prescribedBinary_target_code_injective {u v K k : ℕ} {U V L R : TNEPath}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (Ω : BinEdit K k U V)
    (hL : Binary L) (hR : Binary R)
    (hlen : (decodeRuns L.steps).2.length = (decodeRuns R.steps).2.length)
    (hs : K+4*k ≤ (decodeRuns L.steps).2.length) :
    Function.Injective (fun g =>
      (prescribedBinaryMap hu hv Ω hL hR hlen hs g,
       prescribedBinaryCode hu hv Ω hL hR hlen hs g)) := by
  intro g h he
  apply (binaryWordEquiv 3 Ω.property.1.source 0).injective
  apply prescribedRun_target_code_injective hu hv Ω.toProgram.toRaw
    (decodeRuns L.steps).2 (decodeRuns R.steps).2
    (binary_decode_letters hL) (binary_decode_letters hR) hlen hs
  apply Prod.ext
  · exact (prescribedTargetEquiv hu.1 hv.1 Ω.property.1.target hL hR).symm.injective
      (congrArg Prod.fst he)
  · exact (Prod.mk.inj he).2

theorem prescribedBinary_fiber {u v K k : ℕ} {U V L R : TNEPath}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (Ω : BinEdit K k U V)
    (hL : Binary L) (hR : Binary R)
    (hlen : (decodeRuns L.steps).2.length = (decodeRuns R.steps).2.length)
    (hs : K+4*k ≤ (decodeRuns L.steps).2.length)
    (b : KroneckerNaturalPathGradings.ConnectedColorings 3 (prescribedTarget hu.1 hv.1 V L R) 0) :
    Nat.card {a // prescribedBinaryMap hu hv Ω hL hR hlen hs a = b} ≤ 8^k :=
  fiber_le_pow _ _ (prescribedBinary_target_code_injective hu hv Ω hL hR hlen hs) b

theorem prescribedBinary_map_exists {u v K k P : ℕ} {U V L R : TNEPath}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (Ω : BinEdit K k U V)
    (hL : Binary L) (hR : Binary R)
    (hleft : (decodeRuns L.steps).2.length = P)
    (hright : (decodeRuns R.steps).2.length = P) (hs : K+4*k ≤ P) :
    ∃ f : KroneckerNaturalPathGradings.ConnectedColorings 3 U 0 →
        KroneckerNaturalPathGradings.ConnectedColorings 3 (prescribedTarget hu.1 hv.1 V L R) 0,
      ∀ b, Nat.card {a // f a = b} ≤ 8^k :=
  ⟨prescribedBinaryMap hu hv Ω hL hR (hleft.trans hright.symm) (by omega),
    prescribedBinary_fiber hu hv Ω hL hR (hleft.trans hright.symm) (by omega)⟩

theorem prescribedBinary_count {u v K k P : ℕ} {U V L R : TNEPath}
    (hu : 1≤u ∧ u≤2) (hv : 1≤v ∧ v≤2) (Ω : BinEdit K k U V)
    (hL : Binary L) (hR : Binary R)
    (hleft : (decodeRuns L.steps).2.length = P)
    (hright : (decodeRuns R.steps).2.length = P) (hs : K+4*k ≤ P) :
    (KroneckerNaturalPathGradings.connectedCount 3 U 0 : ℝ)/(8 : ℝ)^k ≤
      KroneckerNaturalPathGradings.connectedCount 3 (prescribedTarget hu.1 hv.1 V L R) 0 := by
  have hsource : KroneckerNaturalPathGradings.connectedCount 3 U 0 =
      runCount 3 (decodeRuns U.steps).2 0 :=
    Nat.card_congr (binaryWordEquiv 3 Ω.property.1.source 0)
  have htarget : KroneckerNaturalPathGradings.connectedCount 3 (prescribedTarget hu.1 hv.1 V L R) 0 =
      runCount 3 ((decodeRuns L.steps).2 ++ (u :: (decodeRuns V.steps).2 ++ [v]) ++
        (decodeRuns R.steps).2) 0 :=
    Nat.card_congr (prescribedTargetEquiv hu.1 hv.1 Ω.property.1.target hL hR)
  rw [hsource, htarget]
  exact KroneckerThreePrescribedRuns.three_prescribed_run_real _ _ _ _ hu hv Ω.toProgram.toRaw
    (binary_decode_letters hL) (binary_decode_letters hR) hleft hright hs

#print axioms KroneckerPaperPaths.binaryProgram_iff_binEdit
#print axioms KroneckerPaperPaths.mechanical_factor_binEdit
#print axioms KroneckerPaperPaths.exceptional_final_binEdit
#print axioms KroneckerPaperPaths.binary_mechanical_binEdit
#print axioms prescribedBinary_map_exists
#print axioms prescribedBinary_count

end KroneckerManuscriptBinaryEditClaims
