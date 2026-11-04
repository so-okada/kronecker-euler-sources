import KroneckerPaperTraceBridge
import KroneckerPaperNodeShadow
import KroneckerPaperExecutionTrace

/-!
# Literal connected gradings and guarded execution

The connected predicate uses the predecessor map, completed literal nodes,
owned-edge balance inequalities, and a node spanning the entire word. Colors
do not enter this predicate. The execution comparison below includes the
balance hypotheses explicitly; an arbitrary completed node is not a NodeRun.
-/
set_option autoImplicit false
namespace KroneckerPaperConnected
noncomputable section
open KroneckerStack KroneckerShadow KroneckerCompatibility
open KroneckerPredecessor KroneckerPaperTraceBridge

/-- The list of edge occurrences in character order. -/
def wordList (E : ℕ → Edge) (n : ℕ) : List Edge := (List.range' 0 n).map E

/-- A root starts and ends at the endpoints of the whole ambient word. -/
def FullRoot {n : ℕ} (U : Word n) (p : Fin n → Fin n) : Prop :=
  ∃ x v : Fin n, IsNode U p x v ∧ x.val = 0 ∧ v.val + 1 = n

/-- Literal connectedness of a finite graded word. -/
def FiniteConnected {n : ℕ} (U : Word n) : Prop :=
  ∃ p : Fin n → Fin n,
    ValidThrough U p n ∧ OwnedBalance U p ∧ FullRoot U p

/-- The same finite predicate for the first `n` occurrences of a stream. -/
def Connected (E : ℕ → Edge) (n : ℕ) : Prop := FiniteConnected (sample E n)

theorem finite_balance_eq {E : ℕ → Edge} {n k : ℕ} (hk : k ≤ n) :
    KroneckerPredecessor.balance (sample E n) k =
      KroneckerCompatibility.balance E k := by
  induction k with
  | zero => simp [KroneckerCompatibility.balance, walk]
  | succ k ih =>
      rw [KroneckerPredecessor.balance_succ (sample E n) (by omega),
        ih (by omega), KroneckerCompatibility.balance_step]
      rfl

theorem fullRoot_rootComponent {E : ℕ → Edge} {n : ℕ} {p : Fin n → Fin n}
    (hp : ValidThrough (sample E n) p n) (hr : FullRoot (sample E n) p) :
    RootComponent E n := by
  obtain ⟨x, v, hn, hx, hv⟩ := hr
  exact full_node_root_component hn hp hx hv

/-- Every vertical edge of a full root has a completed node as its owner. -/
theorem fullRoot_owner_node {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n) (hr : FullRoot U p) (w : Fin n)
    (hw : ¬ IsHorizontal U w) : ∃ z, IsNode U p (p w) z := by
  obtain ⟨x, v, hn, hx, hv⟩ := hr
  by_cases he : p w = x
  · exact ⟨v, he.symm ▸ hn⟩
  · obtain ⟨hh, hbefore, hload, _⟩ := hp w w.isLt hw
    have hneq : (p w).val ≠ x.val := fun h => he (Fin.ext h)
    have hstart : x.val < (p w).val := by omega
    have hend : (p w).val ≤ v.val := by omega
    have hgrade : 0 < (U (p w)).grade := by omega
    obtain ⟨z, hz, _⟩ := hn.interior_node hp hh hstart hend hgrade
    exact ⟨z, hz⟩

/-- Literal inequalities supply exactly the vertical guards of the executor. -/
theorem literal_guarded {E : ℕ → Edge} {n : ℕ} {p : Fin n → Fin n}
    {f : ℕ → List Entry} (hp : ValidThrough (sample E n) p n)
    (hb : OwnedBalance (sample E n) p) (hr : FullRoot (sample E n) p)
    (ht : RawTrace E n f) (hf : FollowsTrace E p f) : Guarded E n f := by
  have hroot := fullRoot_rootComponent hp hr
  intro k hk hkn
  have hne : f k ≠ [] := by
    obtain ⟨x, hx, _⟩ := trace_root_open hroot ht (by omega) hkn
    intro he
    simp [he] at hx
  apply raw_step_correct (ht.2 k hkn) hne
  intro x xs he hv
  let w : Fin n := ⟨k, hkn⟩
  have hw : ¬ IsHorizontal (sample E n) w := by
    obtain ⟨g, hgv⟩ := hv
    simp [IsHorizontal, sample, w, hgv]
  obtain ⟨z, hz⟩ := fullRoot_owner_node hp hr w hw
  have hbound := hb (p w) z hz w hw rfl
  unfold baseline at hbound
  rw [finite_balance_eq (by omega), finite_balance_eq (by dsimp [w]; omega)] at hbound
  have horigin := follows_head hf hkn hw he
  simpa [w, ← horigin] using hbound

theorem literal_final_balance {E : ℕ → Edge} {n : ℕ} {p : Fin n → Fin n}
    (hp : ValidThrough (sample E n) p n) (hb : OwnedBalance (sample E n) p)
    (hr : FullRoot (sample E n) p) : 1 ≤ KroneckerCompatibility.balance E n := by
  have hroot := fullRoot_rootComponent hp hr
  obtain ⟨x, v, hn, hx, hv⟩ := hr
  have hbound := hb x v hn v hn.end_vertical hn.end_assigned
  unfold baseline at hbound
  rw [hx, hv, finite_balance_eq (by omega), finite_balance_eq le_rfl] at hbound
  obtain ⟨g, _, he⟩ := hroot.2.1
  simpa [KroneckerCompatibility.balance, walk, he, Edge.credit] using hbound

/-- A guarded execution satisfies the literal inequality at every owned edge. -/
theorem guarded_ownedBalance {E : ℕ → Edge} {n : ℕ} {p : Fin n → Fin n}
    {f : ℕ → List Entry} (hr : RootComponent E n) (ht : RawTrace E n f)
    (hg : Guarded E n f) (hf : FollowsTrace E p f) :
    OwnedBalance (sample E n) p := by
  have hp := followsTrace_valid ht hf
  intro x v _hn w hwV hpw
  obtain ⟨y, ys, hy, horigin⟩ := hf w hwV
  have hprior := (hp w w.isLt hwV).2.1
  have hwpos : 1 ≤ w.val := by omega
  obtain ⟨ho, hb⟩ := guarded_state_invariants hr ht hg hwpos (Nat.le_of_lt w.isLt)
  have hs := step_invariants ho hb (hg w.val hwpos w.isLt)
  have hmem : (⟨y.debt, KroneckerCompatibility.balance E (y.origin+1)⟩ :
      KroneckerStack.Node) ∈ (eraseState E w.val (f w.val)).stack := by
    simp [eraseState, hy]
  have hbound := hs.2.2 _ hmem
  unfold baseline
  rw [finite_balance_eq (by omega), finite_balance_eq (by omega)]
  simpa [eraseState, horigin, hpw] using hbound

/-- Pointwise guarded trace transitions compose to the existing executor. -/
theorem execute_trace_segment {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (hg : Guarded E n f) (s len : ℕ) (hs : 1 ≤ s) (hsl : s + len ≤ n) :
    execute ((List.range' s len).map E) (eraseState E s (f s)) =
      some (eraseState E (s + len) (f (s + len))) := by
  induction len generalizing s with
  | zero => simp [execute]
  | succ len ih =>
      simp only [List.range'_succ, List.map_cons, execute]
      rw [hg s hs (by omega)]
      simp only [Option.bind_some]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (s+1) (by omega) (by omega)

/-- The terminal balance of a guarded complete root specifies its NodeRun
surplus. The numerical lower bound is proved from literal owned-edge
inequalities when this lemma is applied to a connected grading. -/
theorem guarded_nodeRun {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (hr : RootComponent E n) (ht : RawTrace E n f) (hg : Guarded E n f)
    (hb : 1 ≤ KroneckerCompatibility.balance E n) :
    NodeRun (wordList E n) (KroneckerCompatibility.balance E n - 1).toNat := by
  obtain ⟨g, he, hf⟩ := trace_first hr ht
  have hz := trace_final_empty hr ht
  have hc : (((KroneckerCompatibility.balance E n - 1).toNat : ℕ) : ℤ) + 1 =
      KroneckerCompatibility.balance E n := by omega
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hr.1).elim
  | succ n =>
      refine ⟨g, (List.range' 1 n).map E, ?_, ?_⟩
      · simp [wordList, List.range'_succ, he]
      · have hx := execute_trace_segment hg 1 n (by omega) (by omega)
        have hfirst : KroneckerCompatibility.balance E 1 = 1 := by
          simp [KroneckerCompatibility.balance, walk, he, Edge.credit]
        rw [hc]
        simpa only [Nat.add_comm 1 n, eraseState, hf, hz, List.map_cons,
          List.map_nil, Nat.zero_add, hfirst] using hx

/-- A literal connected grading is a guarded NodeRun. No such conclusion is
asserted for a node without its owned-edge balance inequalities. -/
theorem connected_nodeRun {E : ℕ → Edge} {n : ℕ} (h : Connected E n) :
    NodeRun (wordList E n) (KroneckerCompatibility.balance E n - 1).toNat := by
  obtain ⟨p, hp, hb, hr⟩ := h
  obtain ⟨f, ht, hf⟩ := valid_has_trace hp
  exact guarded_nodeRun (fullRoot_rootComponent hp hr) ht
    (literal_guarded hp hb hr ht hf) (literal_final_balance hp hb hr)

theorem connected_operational {E : ℕ → Edge} {n m : ℕ}
    (h : Connected E n) (hlegal : ∀ e ∈ wordList E n, e.grade ≤ m) :
    KroneckerStack.Connected m (wordList E n)
      (KroneckerCompatibility.balance E n - 1).toNat :=
  node_connected (connected_nodeRun h) hlegal

theorem connected_surplus {E : ℕ → Edge} {n : ℕ} (h : Connected E n) :
    credit (wordList E n) =
      (((KroneckerCompatibility.balance E n - 1).toNat : ℕ) : ℤ) + 1 :=
  node_credit (connected_nodeRun h)

/-- Accepted execution supplies all three parts of literal connectedness. -/
theorem nodeRun_connected {E : ℕ → Edge} {n c : ℕ}
    (hn : NodeRun (wordList E n) c) : Connected E n := by
  have hr := KroneckerPaperExecutionTrace.nodeRun_rootComponent hn
  obtain ⟨f, ht, hg⟩ := KroneckerPaperExecutionTrace.nodeRun_guardedTrace hn
  obtain ⟨p, hf⟩ := followsTrace_exists ht
  have hp := followsTrace_valid ht hf
  exact ⟨p, hp, guarded_ownedBalance hr ht hg hf, root_component_full_node hr hp⟩

theorem nodeRun_balance {E : ℕ → Edge} {n c : ℕ}
    (hn : NodeRun (wordList E n) c) :
    KroneckerCompatibility.balance E n = (c : ℤ) + 1 := by
  have hc := nodeRun_connected hn
  have hcredit := node_credit hn
  have hcredit' := connected_surplus hc
  obtain ⟨p, hp, hb, hr⟩ := hc
  have hbalance := literal_final_balance hp hb hr
  omega

/-- Surplus-specific equivalence with the established operational predicate.
The only additional hypothesis is the finite palette's grade bound. -/
theorem connected_surplus_iff {E : ℕ → Edge} {n m c : ℕ}
    (hlegal : ∀ e ∈ wordList E n, e.grade ≤ m) :
    (Connected E n ∧ KroneckerCompatibility.balance E n = (c : ℤ) + 1) ↔
      KroneckerStack.Connected m (wordList E n) c := by
  constructor
  · rintro ⟨hc, hb⟩
    have hres : (KroneckerCompatibility.balance E n - 1).toNat = c := by
      rw [hb]
      simp
    simpa [hres] using connected_operational hc hlegal
  · intro hc
    have hn := KroneckerStack.connected_node hc
    exact ⟨nodeRun_connected hn, nodeRun_balance hn⟩

theorem connected_iff_operational {E : ℕ → Edge} {n m : ℕ}
    (hlegal : ∀ e ∈ wordList E n, e.grade ≤ m) :
    Connected E n ↔ ∃ c, KroneckerStack.Connected m (wordList E n) c := by
  constructor
  · intro hc
    exact ⟨_, connected_operational hc hlegal⟩
  · rintro ⟨c, hc⟩
    exact (connected_surplus_iff hlegal).mpr hc |>.1

/-- The surplus is the horizontal length minus one minus the vertical grades,
with all counts taken over the full word. -/
theorem operational_surplus_formula {E : ℕ → Edge} {n m c : ℕ}
    (hc : KroneckerStack.Connected m (wordList E n) c) :
    (c : ℤ) = intervalSum hCount E 0 n - 1 - intervalSum vGrade E 0 n := by
  have hb := nodeRun_balance (KroneckerStack.connected_node hc)
  have hi := balance_interval E 0 n
  simp only [Nat.zero_add, KroneckerCompatibility.balance, walk, sub_zero] at hi
  change KroneckerCompatibility.balance E n = _ at hi
  omega

#print axioms connected_nodeRun
#print axioms nodeRun_connected
#print axioms connected_surplus_iff
#print axioms operational_surplus_formula

end
end KroneckerPaperConnected
