import KroneckerExchangeIntermediateLemma
import KroneckerColoredExchangeRecovery
import KroneckerExplicitShellCorrespondence

/-! The manuscript counter and the first marked-debt deletion in the
list-model exchange, including the protected-root existence hypothesis. -/

noncomputable section
set_option autoImplicit false
namespace KroneckerRepairIndexCorrespondence
open KroneckerStack KroneckerDebtUnits KroneckerMarkedDebtIndex
open KroneckerExchangeIntermediateLemma

def nextCounter (d : ℕ) : Edge → ℕ
  | .H g => g + d
  | .V _ => d - 1

def counter (d : ℕ) : List Edge → ℕ
  | [] => d
  | e :: es => counter (nextCounter d e) es

/-- The edge at k is vertical and the paper's counter vanishes before it. -/
def Candidate (d : ℕ) (es : List Edge) (k : ℕ) : Prop :=
  (∃ h, es[k]? = some (.V h)) ∧ counter d (es.take k) = 0

@[simp] theorem candidate_head_horizontal (d g : ℕ) (es : List Edge) :
    ¬ Candidate d (.H g :: es) 0 := by
  simp [Candidate, counter]

@[simp] theorem candidate_head_vertical (d g : ℕ) (es : List Edge) :
    Candidate d (.V g :: es) 0 ↔ d = 0 := by
  simp [Candidate, counter]

theorem candidate_cons_succ (d : ℕ) (e : Edge) (es : List Edge) (k : ℕ) :
    Candidate d (e :: es) (k+1) ↔ Candidate (nextCounter d e) es k := by
  simp [Candidate, counter]

theorem no_earlier_cons_succ (d : ℕ) (e : Edge) (es : List Edge) (k : ℕ) :
    (∀ j < k+1, ¬ Candidate d (e :: es) j) ↔
      ¬ Candidate d (e :: es) 0 ∧
        ∀ j < k, ¬ Candidate (nextCounter d e) es j := by
  constructor
  · intro h
    refine ⟨h 0 (by omega), ?_⟩
    intro j hj
    have hj' := h (j+1) (by omega)
    exact fun hjc => hj' ((candidate_cons_succ d e es j).mpr hjc)
  · rintro ⟨h0, hs⟩ j hj
    cases j with
    | zero => exact h0
    | succ j =>
        intro hjc
        exact hs j (by omega) ((candidate_cons_succ d e es j).mp hjc)

/-- The existing marked index is precisely the first candidate of the
paper's counter recursion; indices here are zero-based. -/
theorem markedIndex_iff_first_candidate (d : ℕ) (es : List Edge) (k : ℕ) :
    markedIndex d es = some k ↔ Candidate d es k ∧ ∀ j < k, ¬ Candidate d es j := by
  induction es generalizing d k with
  | nil => simp [markedIndex, Candidate, counter]
  | cons e es ih =>
      cases e with
      | H g =>
          cases k with
          | zero => simp [markedIndex]
          | succ k =>
              rw [candidate_cons_succ, no_earlier_cons_succ]
              simp only [candidate_head_horizontal, not_false_eq_true, true_and,
                markedIndex, Option.map_eq_some_iff, nextCounter]
              simpa using ih (g+d) k
      | V g =>
          cases d with
          | zero =>
              cases k with
              | zero => simp [markedIndex]
              | succ k =>
                  rw [no_earlier_cons_succ]
                  simp [markedIndex]
          | succ d =>
              cases k with
              | zero => simp [markedIndex]
              | succ k =>
                  rw [candidate_cons_succ, no_earlier_cons_succ]
                  simp only [candidate_head_vertical, Nat.succ_ne_zero, not_false_eq_true,
                    true_and, markedIndex, Option.map_eq_some_iff, nextCounter, Nat.succ_sub_one]
                  simpa using ih d k

/-- The paper's positive EN case chooses the same vertical ordinal as
`changeIndex`. The ordinal is one-based in the paper. -/
theorem positive_changeIndex_ordinal (pre es : List Edge) (d h k : ℕ)
    (hk : Candidate d es k) (hfirst : ∀ j < k, ¬ Candidate d es j) :
    changeIndex true pre.length (pre ++ .H (d+1) :: .V h :: es) + 1 =
      verticalCount pre + 1 + verticalCount (es.take k) + 1 := by
  have hm := (markedIndex_iff_first_candidate d es k).mpr ⟨hk,hfirst⟩
  rw [changeIndex_prefix]
  simp [changeIndex, hm, Nat.add_assoc]

/-- The protected-root execution used by the exchange proof supplies a
candidate, rather than relying on the default index for an empty set. -/
theorem positive_candidate_exists {es : List Edge} {tail : List ℤ}
    {a b c root : ℤ} {g h : ℕ}
    (ht : tail ≠ []) (ho : KroneckerUnitOrderBounds.OrderedBounded ⟨b,a::tail⟩)
    (he : unitExecute (.H (g+1) :: .V h :: es) ⟨b,a::tail⟩ = some ⟨c,[root]⟩) :
    ∃ k, Candidate g es k ∧ ∀ j < k, ¬ Candidate g es j := by
  obtain ⟨_, _, k, _, _, hk, _, _⟩ :=
    KroneckerPositiveRightExchange.positive_right ht ho he
  exact ⟨k, (markedIndex_iff_first_candidate g es k).mp hk⟩

theorem markedIndex_append_of_some {d k : ℕ} {es : List Edge}
    (h : markedIndex d es = some k) (post : List Edge) :
    markedIndex d (es ++ post) = some k := by
  induction es generalizing d k with
  | nil => simp [markedIndex] at h
  | cons e es ih =>
      cases e with
      | H g =>
          simp only [List.cons_append, markedIndex, Option.map_eq_some_iff] at h ⊢
          obtain ⟨j,hj,rfl⟩ := h
          exact ⟨j,ih hj,rfl⟩
      | V g =>
          cases d with
          | zero => simpa [markedIndex] using h
          | succ d =>
              simp only [List.cons_append, markedIndex, Option.map_eq_some_iff] at h ⊢
              obtain ⟨j,hj,rfl⟩ := h
              exact ⟨j,ih hj,rfl⟩

/-- A positive exchange inside a connected node selects an edge of that
node, and adding the outside shell suffix cannot change that selection. -/
theorem connected_node_candidate_localized {r c g h : ℕ} {pre es : List Edge}
    (hn : NodeRun (.H (r+1) :: (pre ++ .H (g+1) :: .V h :: es)) c)
    (post : List Edge) :
    ∃ k, k < es.length ∧ Candidate g es k ∧
      (∀ j < k, ¬ Candidate g es j) ∧
      markedIndex g (es ++ post) = some k := by
  obtain ⟨b,a,tail,ht,ho,_,he⟩ :=
    KroneckerProtectedNodePrefix.protected_node_prefix hn (by simp)
  obtain ⟨k,hk,hfirst⟩ := positive_candidate_exists ht ho he
  have hm := (markedIndex_iff_first_candidate g es k).mpr ⟨hk,hfirst⟩
  have hlt : k < es.length := by
    obtain ⟨q,hq⟩ := hk.1
    by_contra hn
    have hz : es[k]? = none := List.getElem?_eq_none (by omega)
    rw [hz] at hq
    contradiction
  exact ⟨k,hlt,hk,hfirst,markedIndex_append_of_some hm post⟩

theorem verticalCount_take_mono (es : List Edge) {i j : ℕ} (h : i ≤ j) :
    verticalCount (es.take i) ≤ verticalCount (es.take j) := by
  induction es generalizing i j with
  | nil => simp [verticalCount]
  | cons e es ih =>
      cases i with
      | zero => simp [verticalCount]
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              have hs := ih (i := i) (j := j) (by omega)
              cases e <;> simpa [verticalCount] using hs

/-- One-based vertical ordinals selected by the paper's zero-counter test.
The prefix includes all edges through the exchanged pair. -/
def paperOrdinals (d : ℕ) (pre : List Edge) (es : List Edge) : Set ℕ :=
  {j | ∃ k, Candidate d es k ∧
    j = verticalCount pre + 1 + verticalCount (es.take k) + 1}

theorem positive_changeIndex_isLeast (pre es : List Edge) (d h k : ℕ)
    (hk : Candidate d es k) (hfirst : ∀ j < k, ¬ Candidate d es j) :
    IsLeast (paperOrdinals d pre es)
      (changeIndex true pre.length (pre ++ .H (d+1) :: .V h :: es) + 1) := by
  have he := positive_changeIndex_ordinal pre es d h k hk hfirst
  rw [he]
  constructor
  · exact ⟨k,hk,rfl⟩
  · rintro j ⟨l,hl,rfl⟩
    have hkl : k ≤ l := by
      by_contra hn
      exact hfirst l (by omega) hl
    have hm := verticalCount_take_mono es hkl
    omega

/-- The selected least vertical ordinal for the whole shell is already
encountered before the connected copied node ends. -/
theorem connected_node_paper_index_localized {r c g h : ℕ} {pre es : List Edge}
    (hn : NodeRun (.H (r+1) :: (pre ++ .H (g+1) :: .V h :: es)) c)
    (shellPrefix post : List Edge) :
    ∃ k, k < es.length ∧ Candidate g es k ∧
      IsLeast (paperOrdinals g shellPrefix (es ++ post))
        (changeIndex true shellPrefix.length
          (shellPrefix ++ .H (g+1) :: .V h :: (es ++ post)) + 1) := by
  obtain ⟨k,hlt,hk,_,hm⟩ := connected_node_candidate_localized hn post
  obtain ⟨hfull,hfirst⟩ := (markedIndex_iff_first_candidate g (es ++ post) k).mp hm
  exact ⟨k,hlt,hk,positive_changeIndex_isLeast shellPrefix (es ++ post) g h k hfull hfirst⟩

/-- The connected node in the localization theorem can be the manuscript's
geometric graded path; the prefix and suffix are its ordered edge lists. -/
theorem geometric_connected_node_paper_index
    (X : KroneckerPaperPaths.TNEPath) (f : KroneckerNaturalPathGradings.Grading X)
    (hf : KroneckerNaturalPathGradings.ConnectedGrading f)
    (r g h : ℕ) (pre es shellPrefix post : List Edge)
    (hword : KroneckerExplicitShellCorrespondence.gradedWord X f =
      .H (r+1) :: (pre ++ .H (g+1) :: .V h :: es)) :
    ∃ k, k < es.length ∧ Candidate g es k ∧
      IsLeast (paperOrdinals g shellPrefix (es ++ post))
        (changeIndex true shellPrefix.length
          (shellPrefix ++ .H (g+1) :: .V h :: (es ++ post)) + 1) := by
  have hn := KroneckerPaperConnected.connected_nodeRun hf
  rw [← KroneckerExplicitShellCorrespondence.gradedWord_trace] at hn
  rw [hword] at hn
  exact connected_node_paper_index_localized hn shellPrefix post

/-- The marked-baseline construction can choose the paper's explicit
repair grade, using the balance immediately before the selected edge. -/
theorem marked_baseline_repair_exact {es : List Edge} {pre tail : List ℤ}
    {a β b c root : ℤ} (ht : tail ≠ []) (hb : β ≤ b)
    (hp : ∀ x ∈ pre, β ≤ x)
    (he : unitExecute es ⟨b,pre ++ a :: tail⟩ = some ⟨c,[root]⟩) :
    ∃ es' j h k w, markedIndex pre.length es = some j ∧
      KroneckerVerticalRepair.RepairAt j es es' h k ∧
      unitExecute (es.take j) ⟨b,pre ++ a :: tail⟩ = some w ∧
      k = KroneckerRepairGrade.repairGrade h w.balance β ∧
      unitExecute es' ⟨b,pre ++ β :: tail⟩ = some ⟨c + (h-k : ℕ),[root]⟩ := by
  induction es generalizing pre b with
  | nil =>
      simp only [unitExecute,Option.some.injEq,UnitState.mk.injEq] at he
      have hl := congrArg List.length he.2
      have htlen : 0 < tail.length := List.length_pos_iff.mpr ht
      simp only [List.length_append,List.length_cons,List.length_nil] at hl
      omega
  | cons e es ih =>
      cases e with
      | H g =>
          have hs : unitStep ⟨b,pre ++ a :: tail⟩ (.H g) =
              some ⟨b+1,List.replicate g (b+1) ++ (pre ++ a :: tail)⟩ := by
            cases pre <;> rfl
          have hu : unitExecute es ⟨b+1,(List.replicate g (b+1) ++ pre) ++ a :: tail⟩ =
              some ⟨c,[root]⟩ := by simpa [unitExecute,hs,List.append_assoc] using he
          have hp' : ∀ x ∈ List.replicate g (b+1) ++ pre, β ≤ x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · have hx' := (List.mem_replicate.mp hx).2
              omega
            · exact hp x hx
          obtain ⟨ys,j,h,k,w,hj,hr,hw,hk,hy⟩ := ih (by omega) hp' hu
          refine ⟨.H g :: ys,j+1,h,k,w,?_,.there (.H g) hr,?_,hk,?_⟩
          · simpa [markedIndex] using congrArg (Option.map Nat.succ) hj
          · simpa [unitExecute,hs,List.append_assoc] using hw
          · have hs' : unitStep ⟨b,pre ++ β :: tail⟩ (.H g) =
                some ⟨b+1,List.replicate g (b+1) ++ (pre ++ β :: tail)⟩ := by
              cases pre <;> rfl
            simpa [unitExecute,hs',List.append_assoc] using hy
      | V h =>
          cases pre with
          | nil =>
              have hs : a ≤ b-(h : ℤ) := by
                by_contra hn
                simp [unitExecute,unitStep,hn] at he
              have hu : unitExecute es ⟨b-(h : ℤ),tail⟩ = some ⟨c,[root]⟩ := by
                simpa [unitExecute,unitStep,hs] using he
              let k := KroneckerRepairGrade.repairGrade h b β
              have hk : k ≤ h := KroneckerRepairGrade.repair_grade_le h b β
              have hguard : β ≤ b-(k : ℤ) := KroneckerRepairGrade.repair_grade_guard h b β hb
              have hy := KroneckerUnitSingletonSimulation.execute_raised_singleton hu (h-k : ℕ)
                (by positivity)
              refine ⟨.V k :: es,0,h,k,⟨b,a :: tail⟩,rfl,.here es h k hk,by rfl,rfl,?_⟩
              simp only [unitExecute,unitStep,List.nil_append,ite_eq_left hguard,Option.bind_some]
              convert hy using 1
              simp [KroneckerUnitBalanceRaise.raiseBalance,k,KroneckerRepairGrade.repair_grade_balance]
          | cons z zs =>
              have hs : z ≤ b-(h : ℤ) := by
                by_contra hn
                simp [unitExecute,unitStep,hn] at he
              have hu : unitExecute es ⟨b-(h : ℤ),zs ++ a :: tail⟩ = some ⟨c,[root]⟩ := by
                simpa [unitExecute,unitStep,hs] using he
              have hb' : β ≤ b-(h : ℤ) := le_trans (hp z (by simp)) hs
              obtain ⟨ys,j,h',k,w,hj,hr,hw,hk,hy⟩ :=
                ih hb' (fun x hx => hp x (by simp [hx])) hu
              refine ⟨.V h :: ys,j+1,h',k,w,?_,.there (.V h) hr,?_,hk,?_⟩
              · simpa [markedIndex] using congrArg (Option.map Nat.succ) hj
              · simpa [unitExecute,unitStep,hs] using hw
              · simpa [unitExecute,unitStep,hs] using hy

theorem positive_reduction_formula (h : ℕ) (b θ : ℤ) :
    ((h - KroneckerRepairGrade.repairGrade h b θ : ℕ) : ℤ) =
      (h : ℤ) - min (h : ℤ) (max (b-θ) 0) := by
  rw [Int.natCast_sub (KroneckerRepairGrade.repair_grade_le h b θ)]
  unfold KroneckerRepairGrade.repairGrade
  rw [Nat.cast_min]
  by_cases hb : 0 ≤ b-θ
  · rw [max_eq_left hb, Int.toNat_of_nonneg hb]
  · have hn : b-θ ≤ 0 := by omega
    rw [max_eq_right hn, Int.toNat_of_nonpos hn]
    simp

/-- In the positive EN case, a valid exchange exists with the exact
manuscript reduction, not just an unspecified reduction at the marked edge. -/
theorem positive_right_exact {es : List Edge} {tail : List ℤ}
    {a b c root : ℤ} {g h : ℕ} (ht : tail ≠ [])
    (ho : KroneckerUnitOrderBounds.OrderedBounded ⟨b,a :: tail⟩)
    (he : unitExecute (.H (g+1) :: .V h :: es) ⟨b,a :: tail⟩ = some ⟨c,[root]⟩) :
    h = 0 ∧ ∃ es' j q k w, markedIndex g es = some j ∧
      KroneckerVerticalRepair.RepairAt j es es' q k ∧
      unitExecute (es.take j) ⟨b+1,List.replicate g (b+1) ++ a :: tail⟩ = some w ∧
      ((q-k : ℕ) : ℤ) = (q : ℤ) - min (q : ℤ) (max (w.balance-(b+1)) 0) ∧
      unitExecute (.V 0 :: .H (g+1) :: es') ⟨b,a :: tail⟩ =
        some ⟨c + (q-k : ℕ),[root]⟩ := by
  have hz : h = 0 := by
    by_contra hn
    have hh : ¬ b+1 ≤ b+1-(h : ℤ) := by omega
    simp [unitExecute,unitStep,List.replicate_succ,hh] at he
  subst h
  have hu : unitExecute es ⟨b+1,List.replicate g (b+1) ++ a :: tail⟩ =
      some ⟨c,[root]⟩ := by
    simpa [unitExecute,unitStep,List.replicate_succ] using he
  obtain ⟨es',j,q,k,w,hj,hr,hw,hk,hy⟩ := marked_baseline_repair_exact ht le_rfl
    (fun x hx => (List.mem_replicate.mp hx).2.ge) hu
  have ha : a ≤ b := ho.2 a (by simp)
  refine ⟨rfl,es',j,q,k,w,by simpa using hj,hr,hw,?_,?_⟩
  · rw [hk]
    exact positive_reduction_formula q w.balance (b+1)
  · cases tail with
    | nil => contradiction
    | cons z zs =>
        simpa [unitExecute,unitStep,ha,List.replicate_succ',List.append_assoc] using hy

/-- The paper's counter set, stated directly using absolute edge positions
in the exchanged shell word. Positions are zero-based here; the set entries
are the paper's one-based vertical ordinals. -/
def exchangedWord (pre : List Edge) (h s : ℕ) (es : List Edge) := pre ++ (.V h :: .H s :: es)
def cutoff (pre : List Edge) := pre.length + 2

def literalOrdinals (d : ℕ) (pre : List Edge) (h s : ℕ) (es : List Edge) : Set ℕ :=
  {j | ∃ p q, cutoff pre ≤ p ∧ (exchangedWord pre h s es)[p]? = some (.V q) ∧
    counter d (((exchangedWord pre h s es).drop (cutoff pre)).take (p - cutoff pre)) = 0 ∧
    j = verticalCount ((exchangedWord pre h s es).take (p+1))}

theorem verticalCount_append (xs ys : List Edge) :
    verticalCount (xs ++ ys) = verticalCount xs + verticalCount ys := by
  induction xs with
  | nil => simp [verticalCount]
  | cons x xs ih => cases x <;> simp [verticalCount,ih,Nat.add_assoc,Nat.add_comm]

theorem exchanged_drop (pre : List Edge) (h s : ℕ) (es : List Edge) :
    (exchangedWord pre h s es).drop (cutoff pre) = es := by
  simp [exchangedWord,cutoff,List.drop_append]

theorem exchanged_get (pre : List Edge) (h s k : ℕ) (es : List Edge) :
    (exchangedWord pre h s es)[cutoff pre + k]? = es[k]? := by
  unfold exchangedWord cutoff
  rw [List.getElem?_append_right (by omega)]
  have hidx : pre.length+2+k-pre.length = k+2 := by omega
  rw [hidx]
  simp

theorem exchanged_ordinal (pre : List Edge) (h s k q : ℕ) (es : List Edge)
    (hq : es[k]? = some (.V q)) :
    verticalCount ((exchangedWord pre h s es).take (cutoff pre+k+1)) =
      verticalCount pre + 1 + verticalCount (es.take k) + 1 := by
  unfold exchangedWord cutoff
  rw [List.take_append]
  have htake : List.take (pre.length+2+k+1) pre = pre := (List.take_eq_self_iff pre).2 (by omega)
  have hsub : pre.length+2+k+1-pre.length = (k+1)+2 := by omega
  rw [htake,hsub]
  have hcount : verticalCount (es.take (k+1)) = verticalCount (es.take k)+1 := by
    rw [List.take_add_one,hq]
    simp [verticalCount_append,verticalCount]
  simp only [List.take,verticalCount_append,verticalCount,hcount]
  omega

theorem literal_eq_paperOrdinals (d : ℕ) (pre : List Edge) (h s : ℕ) (es : List Edge) :
    literalOrdinals d pre h s es = paperOrdinals d pre es := by
  ext j
  constructor
  · rintro ⟨p,q,hp,hget,hcounter,rfl⟩
    let k := p-cutoff pre
    have hp' : p = cutoff pre+k := by dsimp [k]; omega
    rw [hp',exchanged_get] at hget
    rw [hp',exchanged_drop] at hcounter
    simp only [Nat.add_sub_cancel_left] at hcounter
    refine ⟨k,⟨⟨q,hget⟩,hcounter⟩,?_⟩
    rw [hp',exchanged_ordinal pre h s k q es hget]
  · rintro ⟨k,⟨⟨q,hget⟩,hcounter⟩,rfl⟩
    refine ⟨cutoff pre+k,q,by omega,?_,?_,?_⟩
    · rw [exchanged_get];exact hget
    · rw [exchanged_drop];simpa using hcounter
    · exact (exchanged_ordinal pre h s k q es hget).symm

/-- The literal position-based candidate set has a least element selected
inside the geometric copied node, before the outside shell suffix. -/
theorem geometric_connected_node_literal_index
    (X : KroneckerPaperPaths.TNEPath) (f : KroneckerNaturalPathGradings.Grading X)
    (hf : KroneckerNaturalPathGradings.ConnectedGrading f)
    (r g h : ℕ) (pre es shellPrefix post : List Edge)
    (hword : KroneckerExplicitShellCorrespondence.gradedWord X f =
      .H (r+1) :: (pre ++ .H (g+1) :: .V h :: es)) :
    ∃ k, k < es.length ∧ Candidate g es k ∧
      IsLeast (literalOrdinals g shellPrefix h (g+1) (es ++ post))
        (changeIndex true shellPrefix.length
          (shellPrefix ++ .H (g+1) :: .V h :: (es ++ post)) + 1) := by
  obtain ⟨k,hk,hc,hl⟩ :=
    geometric_connected_node_paper_index X f hf r g h pre es shellPrefix post hword
  exact ⟨k,hk,hc,by simpa [literal_eq_paperOrdinals] using hl⟩

def geometricShellPrefix (u r : ℕ) (pre : List Edge) : List Edge :=
  [.H (u+1)] ++ List.replicate u (.V 0) ++ (.H (r+1) :: pre)

def geometricShellPost (v : ℕ) : List Edge :=
  [.H (v-1)] ++ List.replicate (v-1) (.V 0) ++ [.V 2]

theorem geometric_shell_literal_index
    (X : KroneckerPaperPaths.TNEPath) (f : KroneckerNaturalPathGradings.Grading X)
    (hf : KroneckerNaturalPathGradings.ConnectedGrading f)
    (r g h u v : ℕ) (hv : 1 ≤ v) (pre es : List Edge)
    (hword : KroneckerExplicitShellCorrespondence.gradedWord X f =
      .H (r+1) :: (pre ++ .H (g+1) :: .V h :: es)) :
    KroneckerExplicitShellCorrespondence.gradedWord
        (KroneckerManuscriptShell.path X u v)
        (KroneckerManuscriptShell.GShell X f u v 1 0) =
      geometricShellPrefix u r pre ++ .H (g+1) :: .V h :: (es ++ geometricShellPost v) ∧
    ∃ k, k < es.length ∧ Candidate g es k ∧
      IsLeast (literalOrdinals g (geometricShellPrefix u r pre) h (g+1)
        (es ++ geometricShellPost v))
        (changeIndex true (geometricShellPrefix u r pre).length
          (geometricShellPrefix u r pre ++ .H (g+1) :: .V h ::
            (es ++ geometricShellPost v)) + 1) := by
  constructor
  · rw [KroneckerExplicitShellCorrespondence.gradedWord_shell X f u v 1 0 hv, hword]
    simp [geometricShellPrefix,geometricShellPost,List.append_assoc]
  · exact geometric_connected_node_literal_index X f hf r g h pre es
      (geometricShellPrefix u r pre) (geometricShellPost v) hword

end KroneckerRepairIndexCorrespondence

#print axioms KroneckerRepairIndexCorrespondence.markedIndex_iff_first_candidate
#print axioms KroneckerRepairIndexCorrespondence.positive_changeIndex_ordinal
#print axioms KroneckerRepairIndexCorrespondence.positive_candidate_exists
#print axioms KroneckerRepairIndexCorrespondence.connected_node_candidate_localized
#print axioms KroneckerRepairIndexCorrespondence.positive_changeIndex_isLeast
#print axioms KroneckerRepairIndexCorrespondence.connected_node_paper_index_localized
#print axioms KroneckerRepairIndexCorrespondence.geometric_connected_node_paper_index
#print axioms KroneckerRepairIndexCorrespondence.marked_baseline_repair_exact
#print axioms KroneckerRepairIndexCorrespondence.positive_reduction_formula
#print axioms KroneckerRepairIndexCorrespondence.positive_right_exact
#print axioms KroneckerRepairIndexCorrespondence.literal_eq_paperOrdinals
#print axioms KroneckerRepairIndexCorrespondence.geometric_connected_node_literal_index
#print axioms KroneckerRepairIndexCorrespondence.geometric_shell_literal_index
