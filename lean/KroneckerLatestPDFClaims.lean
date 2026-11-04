import KroneckerExplicitShellCorrespondence
import KroneckerBalanceTraceCorrespondence
import KroneckerNearbyShortFactor
import KroneckerChainRecoveredSkeleton
import KroneckerRepairIndexCorrespondence

/-! Explicit claims in the 148-page manuscript at main b16dc59.
Occurrence indices are zero-based. Boundary indices count completed edges.
The geometric shell encoding is `gradedWord_shell`.
-/
set_option autoImplicit false
noncomputable section

namespace KroneckerRationalZeroIntercept

/-- Lemma 5.3 Claim 4, including the index zero. The run bounds and the
intercept are unnecessary for this floor identity. -/
theorem floor_eq (p q i : ℕ) (hq : 0 < q) (hc : p.Coprime q)
    (hi : i < q) (s : ℝ) (hs : |s - (p : ℝ) / q| < 1 / (q : ℝ)^2) :
    ⌊(i : ℝ) * s⌋ = ⌊(i : ℝ) * ((p : ℝ) / q)⌋ := by
  by_cases hi0 : i = 0
  · subst i
    simp
  let z : ℤ := ⌊(i : ℝ) * ((p : ℝ) / q)⌋
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hid : (q : ℝ) * ((i : ℝ) * ((p : ℝ) / q)) = (i : ℝ) * p := by
    field_simp
  have hlo := mul_le_mul_of_nonneg_left (Int.floor_le ((i : ℝ) * ((p : ℝ) / q))) hqR.le
  have hhi := mul_lt_mul_of_pos_left (Int.lt_floor_add_one ((i : ℝ) * ((p : ℝ) / q))) hqR
  change (q : ℝ) * (z : ℝ) ≤ _ at hlo
  change _ < (q : ℝ) * ((z : ℝ) + 1) at hhi
  rw [hid] at hlo hhi
  have hloZ : (q : ℤ) * z ≤ (i : ℤ) * p := by exact_mod_cast hlo
  have hhiZ : (i : ℤ) * p < (q : ℤ) * (z + 1) := by exact_mod_cast hhi
  have hne : (i : ℤ) * p ≠ (q : ℤ) * z := by
    intro he
    apply hi0
    apply KroneckerCoprimeIndexGap.coprime_cancel_indices p q i 0 hc hi hq
    exact ⟨z, by simpa using he⟩
  have hlower : (q : ℝ) * (z : ℝ) + 1 ≤ (i : ℝ) * p := by
    exact_mod_cast (show (q : ℤ) * z + 1 ≤ (i : ℤ) * p by omega)
  have hupper : (i : ℝ) * p + 1 ≤ (q : ℝ) * ((z : ℝ) + 1) := by
    exact_mod_cast (show (i : ℤ) * p + 1 ≤ (q : ℤ) * (z + 1) by omega)
  have herr := KroneckerPhasePerturbation.index_slope_error q i 0 hq hi hq
    s ((p : ℝ) / q) hs
  simp only [Nat.cast_zero, sub_zero] at herr
  have herr' : |(q : ℝ) * ((i : ℝ) * s) - (i : ℝ) * p| < 1 := by
    convert herr using 1
    congr 1
    nlinarith [hid]
  obtain ⟨hminus, hplus⟩ := abs_lt.mp herr'
  apply Int.floor_eq_iff.mpr
  constructor
  · nlinarith
  · nlinarith

end KroneckerRationalZeroIntercept

namespace KroneckerChainRecoveredSkeleton
open Module SimpleGraph KroneckerChainIncidence KroneckerChainPortColors
open KroneckerChainSlotAssignments KroneckerChainRepresentativeIndependence
open KroneckerChainIntrinsicTransport KroneckerColoredIncidenceIso
open KroneckerBipartiteIncidence

/-- Lemma 7.50 Claim 3: the connector and component maps form an actual
bipartition-preserving graph isomorphism of the recovered chain skeletons. -/
def recoveredSkeletonIso {n m : ℕ} {d : Block n → ℕ} {d' : Block m → ℕ}
    {σ : ColorChoices n} {τ : ColorChoices m}
    (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
    (hd : ∀ j, 0 < d j) (hd' : ∀ j, 0 < d' j)
    (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
    (he : ∀ s, finrank ℂ ((gluedRepresentative N).block.Space (e.source s)) =
      finrank ℂ ((gluedRepresentative M).block.Space s)) :
    incidenceGraph (@incidence n) ≃g incidenceGraph (@incidence m) where
  toEquiv := Equiv.sumCongr (recoveredConnectorEquiv M N hd hd' e he)
    (chainBlockEquiv M N hd hd' e he)
  map_rel_iff' := by
    intro a b
    cases a <;> cases b
    · rfl
    · exact recovered_chain_incidence M N hd hd' e he _ _
    · exact recovered_chain_incidence M N hd hd' e he _ _
    · rfl

end KroneckerChainRecoveredSkeleton

namespace KroneckerShellTraceClaims
open KroneckerStack KroneckerShadow KroneckerPaperTraceBridge
open KroneckerPredecessor

def copyEntry (r : ℕ) (x : Entry) : Entry := ⟨r + x.origin, x.debt⟩

theorem rawStep_unique {E : ℕ → Edge} {k : ℕ} {xs ys zs : List Entry}
    (h : RawStep E k xs ys) (h' : RawStep E k xs zs) : ys = zs := by
  cases h <;> cases h' <;> simp_all

theorem rawStep_copy {E F : ℕ → Edge} {r k : ℕ} {xs ys : List Entry}
    (h : RawStep E k xs ys) (hcopy : F (r + k) = E k) (outer : List Entry) :
    RawStep F (r + k) (xs.map (copyEntry r) ++ outer)
      (ys.map (copyEntry r) ++ outer) := by
  cases h with
  | hz he => exact RawStep.hz (hcopy.trans he)
  | hp he => exact RawStep.hp (hcopy.trans he)
  | one he hd => exact RawStep.one (hcopy.trans he) hd
  | many he hd => exact RawStep.many (hcopy.trans he) hd

/-- A copied path executes above the entire outer trace. The origins of
its entries increase by exactly the copy offset. -/
theorem trace_copy {E F : ℕ → Edge} {n N r : ℕ} {f g : ℕ → List Entry}
    (hf : RawTrace E n f) (hg : RawTrace F N g) (hr : r + n ≤ N)
    (hcopy : ∀ k < n, F (r + k) = E k) (k : ℕ) (hk : k ≤ n) :
    g (r + k) = (f k).map (copyEntry r) ++ g r := by
  induction k with
  | zero => simp [hf.1]
  | succ k ih =>
    have hk' : k < n := by omega
    have ht := rawStep_copy (hf.2 k hk') (hcopy k hk') (g r)
    rw [← ih (by omega)] at ht
    exact rawStep_unique (hg.2 (r + k) (by omega)) ht

/-- Lemma 3.3 Claim 5 in occurrence indices. Any valid h-precursor maps on
the copy and the full path agree after adding the copy offset. -/
theorem copied_precursor {E F : ℕ → Edge} {n N r : ℕ}
    (p : Fin n → Fin n) (q : Fin N → Fin N)
    (hp : ValidThrough (sample E n) p n) (hq : ValidThrough (sample F N) q N)
    (hr : r + n ≤ N) (hcopy : ∀ k < n, F (r + k) = E k)
    (v : Fin n) (hv : ¬ IsHorizontal (sample E n) v) :
    (q ⟨r + v.val, by omega⟩).val = r + (p v).val := by
  obtain ⟨f, hf, hpf⟩ := valid_has_trace hp
  obtain ⟨g, hg, hqg⟩ := valid_has_trace hq
  obtain ⟨x, xs, hx, hpx⟩ := hpf v hv
  have htrace := trace_copy hf hg hr hcopy v.val v.isLt.le
  rw [hx] at htrace
  have hv' : ¬ IsHorizontal (sample F N) ⟨r + v.val, by omega⟩ := by
    simpa only [IsHorizontal, sample, hcopy v.val v.isLt] using hv
  have hhead := follows_head hqg (show r + v.val < N by omega) hv' htrace
  change r + x.origin = _ at hhead
  rw [hpx] at hhead
  exact hhead.symm

/-- The copied connected path has no open horizontal debt at its end,
so its execution restores the complete outer trace. -/
theorem connected_copy_boundary {E F : ℕ → Edge} {n N r c : ℕ}
    {g : ℕ → List Entry} (hg : RawTrace F N g)
    (hn : NodeRun ((List.range' 0 n).map E) c) (hr : r + n ≤ N)
    (hcopy : ∀ k < n, F (r + k) = E k) : g (r + n) = g r := by
  have hroot := KroneckerPaperExecutionTrace.nodeRun_rootComponent hn
  obtain ⟨f, hf⟩ := root_trace_exists hroot
  simpa [trace_final_empty hroot hf] using trace_copy hf hg hr hcopy n le_rfl

end KroneckerShellTraceClaims

namespace KroneckerRepairCounterInvariant
open KroneckerStack KroneckerDebtUnits KroneckerRepairIndexCorrespondence

/-- Lemma 9.6 before repair: both lists have the same complete prefix
and fixed tail. Only the distinguished baseline differs. -/
theorem common_prefix_before_candidate {es : List Edge} {pre tail : List ℤ}
    {a β b : ℤ} {t : UnitState} (hb : β ≤ b) (hp : ∀ x ∈ pre, β ≤ x)
    (he : unitExecute es ⟨b, pre ++ a :: tail⟩ = some t)
    (hno : ∀ k < es.length, ¬ Candidate pre.length es k) :
    ∃ H B, t = ⟨B, H ++ a :: tail⟩ ∧ H.length = counter pre.length es ∧
      (∀ x ∈ H, β ≤ x) ∧ β ≤ B ∧
      unitExecute es ⟨b, pre ++ β :: tail⟩ = some ⟨B, H ++ β :: tail⟩ := by
  induction es generalizing pre b with
  | nil =>
    simp only [unitExecute, Option.some.injEq] at he
    exact ⟨pre, b, he.symm, rfl, hp, hb, rfl⟩
  | cons e es ih =>
    have hno' : ∀ k < es.length, ¬ Candidate (nextCounter pre.length e) es k := by
      intro k hk hcan
      exact hno (k+1) (by simp; omega)
        ((candidate_cons_succ pre.length e es k).mpr hcan)
    cases e with
    | H g =>
      have hs : unitStep ⟨b, pre ++ a :: tail⟩ (.H g) =
          some ⟨b+1, (List.replicate g (b+1) ++ pre) ++ a :: tail⟩ := by
        cases pre <;> simp [unitStep, List.append_assoc]
      have ht : unitExecute es ⟨b+1, (List.replicate g (b+1) ++ pre) ++ a :: tail⟩ =
          some t := by simpa [unitExecute, hs] using he
      have hp' : ∀ x ∈ List.replicate g (b+1) ++ pre, β ≤ x := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have := (List.mem_replicate.mp hx).2
          omega
        · exact hp x hx
      obtain ⟨H, B, ht', hlen, hH, hB, he'⟩ := ih (by omega) hp' ht
        (by simpa [nextCounter] using hno')
      refine ⟨H, B, ht', ?_, hH, hB, ?_⟩
      · simpa [counter, nextCounter] using hlen
      · have hs' : unitStep ⟨b, pre ++ β :: tail⟩ (.H g) =
            some ⟨b+1, (List.replicate g (b+1) ++ pre) ++ β :: tail⟩ := by
          cases pre <;> simp [unitStep, List.append_assoc]
        simpa [unitExecute, hs'] using he'
    | V g =>
      cases pre with
      | nil => exact False.elim (hno 0 (by simp) (by simp))
      | cons z zs =>
        have hz : z ≤ b - (g : ℤ) := by
          by_contra h
          simp [unitExecute, unitStep, h] at he
        have ht : unitExecute es ⟨b-(g : ℤ), zs ++ a :: tail⟩ = some t := by
          simpa [unitExecute, unitStep, hz] using he
        obtain ⟨H, B, ht', hlen, hH, hB, he'⟩ := ih
          (le_trans (hp z (by simp)) hz) (fun x hx => hp x (by simp [hx])) ht
          (by simpa [nextCounter] using hno')
        exact ⟨H, B, ht', by simpa [counter, nextCounter] using hlen, hH, hB,
          by simpa [unitExecute, unitStep, hz] using he'⟩

end KroneckerRepairCounterInvariant

namespace KroneckerIntrinsicSkeletonIso
open Module SimpleGraph KroneckerReflectedSupportClasses KroneckerColoredIncidenceIso
open KroneckerIntrinsicConnectors KroneckerIntrinsicBlockDeletion
open KroneckerIntrinsicDeletionTransport KroneckerChainIntrinsicTransport
open KroneckerRetainedBlockSupport KroneckerBipartiteIncidence

abbrev Connector (X : ColoredBlock) := {s // IsConnector X.block s}
abbrev Component (X : ColoredBlock) := (intrinsicDeletion X.block).ConnectedComponent

def incidence (X : ColoredBlock) (s : Connector X) (c : Component X) : Prop :=
  ∃ v : {v // Survives X.block v}, (intrinsicDeletion X.block).connectedComponentMk v = c ∧
    (supportGraph X.block).Adj (.inl s.val) v.val

variable {X Y : ColoredBlock} (e : ColoredIso X.coloring Y.coloring)
  (he : ∀ s, finrank ℂ (Y.block.Space (e.source s)) = finrank ℂ (X.block.Space s))

def connectorEquiv : Connector X ≃ Connector Y :=
  Equiv.subtypeEquiv e.source (fun s => (connector_transport X Y e he s).symm)

def componentEquiv : Component X ≃ Component Y :=
  (deletionIso e he).connectedComponentEquiv

theorem incidence_transport (s : Connector X) (c : Component X) :
    incidence Y (connectorEquiv e he s) (componentEquiv e he c) ↔ incidence X s c := by
  constructor
  · rintro ⟨w, hw, hadj⟩
    obtain ⟨v, rfl⟩ := (deletionIso e he).surjective w
    refine ⟨v, ?_, ?_⟩
    · apply (componentEquiv e he).injective
      exact hw
    · exact e.graphIso.map_rel_iff.mp hadj
  · rintro ⟨v, hv, hadj⟩
    refine ⟨deletionIso e he v, ?_, ?_⟩
    · exact congrArg (componentEquiv e he) hv
    · exact e.graphIso.map_rel_iff.mpr hadj

/-- Lemma 7.50 Claim 3 for arbitrary dimensioned support representatives.
The two summands are the intrinsic connectors and the components after
their deletion. The isomorphism therefore preserves the bipartition. -/
def skeletonIso : incidenceGraph (incidence X) ≃g incidenceGraph (incidence Y) where
  toEquiv := Equiv.sumCongr (connectorEquiv e he) (componentEquiv e he)
  map_rel_iff' := by
    intro a b
    cases a <;> cases b
    · rfl
    · exact incidence_transport e he _ _
    · exact incidence_transport e he _ _
    · rfl

theorem connector_natural (s : Connector X) :
    (connectorEquiv e he s).val = e.source s.val := rfl

theorem component_natural (v : {v // Survives X.block v}) :
    (deletionIso e he v).val = e.graphIso v.val := rfl

end KroneckerIntrinsicSkeletonIso

namespace KroneckerIntrinsicSkeletonIso
open Module SimpleGraph KroneckerReflectedSupportClasses KroneckerColoredIncidenceIso
open KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerChainIntrinsicTransport
open KroneckerChainDeletionTransport KroneckerChainRecoveredSkeleton
open KroneckerIntrinsicBlockDeletion KroneckerRecoveredBlockComponents
open KroneckerDeletedConnectorGraph KroneckerActualSlotGluing
open KroneckerRetainedBlockSupport KroneckerGluedSupportGraph KroneckerBipartiteIncidence

variable {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
  (M : RepresentativeFamily d σ) (hd : ∀ j, 0 < d j)

def chainComponentEquiv : Block n ≃ Component (gluedRepresentative M) :=
  (recoveredBlockEquiv (familyBlock M) (block_connected M hd)).symm.trans
    (chainDeletionIso M hd).connectedComponentEquiv

theorem chain_component_label (v : RemainingVertex (familyBlock M)) :
    (intrinsicDeletion (gluedRepresentative M).block).connectedComponentMk
      (chainDeletionIso M hd v) = chainComponentEquiv M hd v.1 := by
  have h := (recoveredBlockEquiv (familyBlock M) (block_connected M hd)).symm_apply_apply
    ((remainingGraph (familyBlock M)).connectedComponentMk v)
  change (recoveredBlockEquiv (familyBlock M) (block_connected M hd)).symm v.1 = _ at h
  exact (congrArg (chainDeletionIso M hd).connectedComponentEquiv h).symm

theorem chain_incidence (i : KroneckerChainIncidence.Connector n) (j : Block n) :
    incidence (gluedRepresentative M) (insertedConnectorEquiv M hd i)
      (chainComponentEquiv M hd j) ↔ KroneckerChainIncidence.incidence i j := by
  rw [incidence_iff_block_adj M]
  constructor
  · rintro ⟨v, hv, hadj⟩
    obtain ⟨w, rfl⟩ := (chainDeletionIso M hd).surjective v
    have hwj : w.1 = j := (chainComponentEquiv M hd).injective
      ((chain_component_label M hd w).symm.trans hv)
    rcases w with ⟨k, w⟩
    dsimp at hwj
    subst k
    exact ⟨w, hadj⟩
  · rintro ⟨w, hw⟩
    exact ⟨chainDeletionIso M hd ⟨j, w⟩, chain_component_label M hd ⟨j, w⟩, hw⟩

def chainIntrinsicIso : incidenceGraph (@KroneckerChainIncidence.incidence n) ≃g
    incidenceGraph (incidence (gluedRepresentative M)) where
  toEquiv := Equiv.sumCongr (insertedConnectorEquiv M hd) (chainComponentEquiv M hd)
  map_rel_iff' := by
    intro a b
    cases a <;> cases b
    · rfl
    · exact chain_incidence M hd _ _
    · exact chain_incidence M hd _ _
    · rfl

/-- The induced map S → S_X of Lemma 7.50 Claim 3, for any chosen
dimension-preserving colored support isomorphism into X. -/
def inducedSkeletonIso (X : ColoredBlock)
    (e : ColoredIso (gluedRepresentative M).coloring X.coloring)
    (he : ∀ s, finrank ℂ (X.block.Space (e.source s)) =
      finrank ℂ ((gluedRepresentative M).block.Space s)) :
    incidenceGraph (@KroneckerChainIncidence.incidence n) ≃g incidenceGraph (incidence X) :=
  (chainIntrinsicIso M hd).trans (skeletonIso e he)

end KroneckerIntrinsicSkeletonIso



namespace KroneckerShellBoundaryClaims
open KroneckerStack KroneckerManuscriptShell

/-- Lemma 3.3 Claims 6 and 7 at every child boundary, including i = 0.
The only open node is the shell root, of debt one and baseline one. -/
theorem boundary_state (u : ℕ) (xs : List (List Edge × ℕ))
    (hx : ∀ p ∈ xs, NodeRun p.1 p.2) (i : ℕ) (hi : i ≤ xs.length) :
    execute (List.replicate u (.V 0) ++ (xs.take i).flatMap Prod.fst)
      ⟨1, [⟨u + 1, 1⟩]⟩ =
        some ⟨1 + (i : ℤ) + (((xs.take i).map Prod.snd).sum : ℤ), [⟨1, 1⟩]⟩ := by
  rw [execute_append, zeros_leave_one u 1 1 [] le_rfl]
  simp only [Option.bind_some]
  have hc := execute_children (xs.take i)
    (fun p hp => hx p (List.mem_of_mem_take hp)) (⟨1, [⟨1, 1⟩]⟩ : State) (by simp)
  simpa only [List.length_take, Nat.min_eq_left hi, add_comm, add_left_comm, add_assoc] using hc

/-- The boundary prefix contains the shell root and exactly i children. -/
theorem boundary_balance (u : ℕ) (xs : List (List Edge × ℕ))
    (hx : ∀ p ∈ xs, NodeRun p.1 p.2) (i : ℕ) (hi : i ≤ xs.length) :
    credit ([.H (u + 1)] ++ List.replicate u (.V 0) ++
      (xs.take i).flatMap Prod.fst) =
        1 + (i : ℤ) + (((xs.take i).map Prod.snd).sum : ℤ) := by
  have hb := execute_balance (boundary_state u xs hx i hi)
  simpa [credit, List.map_append, List.sum_append, Edge.credit] using hb.symm

end KroneckerShellBoundaryClaims

namespace KroneckerRepairCounterInvariant
open KroneckerStack KroneckerDebtUnits KroneckerRepairIndexCorrespondence

/-- Before the first zero-counter vertical edge, the source-list length
is the counter plus the length of the fixed tail. -/
theorem length_of_no_candidate {es : List Edge} {s t : UnitState} {d l : ℕ}
    (he : unitExecute es s = some t) (hlen : s.stack.length = d + l)
    (hno : ∀ k < es.length, ¬ Candidate d es k) :
    t.stack.length = counter d es + l := by
  induction es generalizing s d with
  | nil =>
    simp only [unitExecute, Option.some.injEq] at he
    subst t
    exact hlen
  | cons e es ih =>
    cases hstep : unitStep s e with
    | none => simp [unitExecute, hstep] at he
    | some s' =>
      have htail : unitExecute es s' = some t := by simpa [unitExecute, hstep] using he
      have hno' : ∀ k < es.length, ¬ Candidate (nextCounter d e) es k := by
        intro k hk hcan
        exact hno (k+1) (by simp; omega) ((candidate_cons_succ d e es k).mpr hcan)
      have hlen' : s'.stack.length = nextCounter d e + l := by
        cases s with
        | mk b st =>
          cases st with
          | nil => simp [unitStep] at hstep
          | cons a st =>
            cases e with
            | H g =>
              simp only [unitStep, Option.some.injEq] at hstep
              subst s'
              simp only [List.length_cons] at hlen
              simp only [List.length_append, List.length_replicate, List.length_cons, nextCounter]
              omega
            | V g =>
              have hd : d ≠ 0 := by
                intro hd
                exact hno 0 (by simp) ((candidate_head_vertical d g es).mpr hd)
              simp only [unitStep] at hstep
              split at hstep
              · cases hstep
                simp only [List.length_cons] at hlen
                simp only [nextCounter]
                omega
              · contradiction
      exact ih htail hlen' hno'

/-- Lemma 9.5: a source list with a fixed tail of length at least two
cannot end as a singleton unless a zero-counter vertical edge occurs. -/
theorem candidate_of_singleton {es : List Edge} {s : UnitState}
    {d l : ℕ} {b root : ℤ} (he : unitExecute es s = some ⟨b, [root]⟩)
    (hlen : s.stack.length = d + l) (hl : 2 ≤ l) :
    ∃ k, k < es.length ∧ Candidate d es k := by
  by_contra h
  push Not at h
  have hfinal := length_of_no_candidate he hlen h
  simp only [List.length_singleton] at hfinal
  omega

end KroneckerRepairCounterInvariant

namespace KroneckerShellTraceClaims
open KroneckerStack KroneckerShadow KroneckerPaperTraceBridge
open KroneckerPaperExecutionTrace KroneckerPaperConnected KroneckerCompatibility

/-- Decode the shell's execution state as the literal indexed debt trace.
The prefix consists of the initial root, its u zero-grade vertical edges,
and the first i connected children. -/
theorem boundary_trace {E : ℕ → Edge} {N c : ℕ} {f : ℕ → List Entry}
    (hn : NodeRun ((List.range' 0 N).map E) c) (hf : RawTrace E N f)
    (u : ℕ) (xs : List (List Edge × ℕ))
    (hx : ∀ p ∈ xs, NodeRun p.1 p.2) (i : ℕ) (hi : i ≤ xs.length)
    (r : ℕ) (hr : r < N)
    (hprefix : (List.range' 0 r).map E =
      .H (u + 1) :: (List.replicate u (.V 0) ++ (xs.take i).flatMap Prod.fst)) :
    f r = [⟨0, 1⟩] ∧
      balance E r = 1 + (i : ℤ) + (((xs.take i).map Prod.snd).sum : ℤ) := by
  have hrpos : 0 < r := by
    by_contra h
    have hz : r = 0 := by omega
    simp [hz] at hprefix
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  simp only [List.range'_succ, List.map_cons] at hprefix
  obtain ⟨hfirst, htail⟩ := List.cons.inj hprefix
  have hf1 : f 1 = [⟨0, u + 1⟩] := by
    have h := hf.2 0 (by omega)
    rw [hf.1] at h
    exact rawStep_unique h (RawStep.hp hfirst)
  have hb1 : balance E 1 = 1 := by
    simp [balance, walk, hfirst, Edge.credit]
  have he := execute_trace_segment (nodeRun_guarded_of_trace hn hf) 1 k (by omega) (by omega)
  have hinit : eraseState E 1 (f 1) = ⟨1, [⟨u + 1, 1⟩]⟩ := by
    simp [eraseState, hf1, hb1]
  rw [hinit, htail, KroneckerShellBoundaryClaims.boundary_state u xs hx i hi] at he
  have heq := Option.some.inj he
  have hb := congrArg State.balance heq
  have hst := congrArg State.stack heq
  change [(⟨1, 1⟩ : Node)] = (f (1 + k)).map
    (fun x => (⟨x.debt, balance E (x.origin + 1)⟩ : Node)) at hst
  have hlen : (f (1 + k)).length = 1 := by
    have h := congrArg List.length hst
    simpa using h.symm
  obtain ⟨x, hxf⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨y, hy, hy0⟩ := trace_root_open (nodeRun_rootComponent hn) hf
    (show 0 < 1 + k by omega) (by omega)
  rw [hxf] at hy hst
  have hyx : y = x := List.mem_singleton.mp hy
  have hx0 : x.origin = 0 := hyx ▸ hy0
  have hx1 : x.debt = 1 := by
    have hh := List.cons.inj hst
    exact (congrArg Node.debt hh.1).symm
  have hxe : x = ⟨0, 1⟩ := by cases x; simp_all
  constructor
  · simpa [Nat.add_comm, hxe] using hxf
  · simpa [eraseState, Nat.add_comm] using hb.symm

/-- Lemma 3.3 Claim 6 in the literal h-precursor debt definition. -/
theorem boundary_debt {E : ℕ → Edge} {N r : ℕ} {f : ℕ → List Entry}
    {P : KroneckerPredecessor.Vertical (sample E N) →
      KroneckerPredecessor.Horizontal (sample E N)}
    (hf : RawTrace E N f) (hp : KroneckerPredecessor.IsHorizontalPredecessor (sample E N) P)
    (hr : r ≤ N) (hboundary : f r = [⟨0, 1⟩])
    (x : KroneckerPredecessor.Horizontal (sample E N)) (hx : x.val.val < r) :
    KroneckerPredecessor.Debt (sample E N) P x r = if x.val.val = 0 then 1 else 0 := by
  rw [← KroneckerBalanceTraceCorrespondence.trace_remaining_eq_debt hf hp hr x hx, hboundary]
  simp [remaining, eq_comm]

end KroneckerShellTraceClaims

namespace KroneckerShellBoundaryClaims
open KroneckerStack KroneckerManuscriptShell KroneckerShadow KroneckerPaperTraceBridge
open KroneckerShellTraceClaims

/-- The boundary index r_i counts the initial run and the first i copies. -/
def boundaryIndex (u : ℕ) (xs : List (List Edge × ℕ)) (i : ℕ) : ℕ :=
  u + 1 + ((xs.take i).flatMap Prod.fst).length

theorem shell_prefix {E : ℕ → Edge} {N : ℕ} (u v ε : ℕ)
    (xs : List (List Edge × ℕ))
    (hw : (List.range' 0 N).map E = Shell xs u v ε) (i : ℕ) :
    boundaryIndex u xs i < N ∧
      (List.range' 0 (boundaryIndex u xs i)).map E =
        .H (u+1) :: (List.replicate u (.V 0) ++ (xs.take i).flatMap Prod.fst) := by
  have hsplit : xs.flatMap Prod.fst =
      (xs.take i).flatMap Prod.fst ++ (xs.drop i).flatMap Prod.fst := by
    rw [← List.flatMap_append, List.take_append_drop]
  let pre := .H (u+1) :: (List.replicate u (.V 0) ++ (xs.take i).flatMap Prod.fst)
  let post := (xs.drop i).flatMap Prod.fst ++ [.H (v-1)] ++
    List.replicate (v-1) (.V 0) ++ [.V (xs.length+1+ε)]
  have hpre : pre.length = boundaryIndex u xs i := by
    simp [pre, boundaryIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hfull : (List.range' 0 N).map E = pre ++ post := by
    rw [hw, Shell_eq, hsplit]
    simp [pre, post, List.append_assoc]
  have hlen := congrArg List.length hfull
  have hpost : 0 < post.length := by simp [post]
  simp only [List.length_map, List.length_range', List.length_append] at hlen
  have hr : boundaryIndex u xs i < N := by omega
  refine ⟨hr, ?_⟩
  have ht := congrArg (List.take (boundaryIndex u xs i)) hfull
  rw [← List.map_take, List.take_range'_of_length_ge hr.le, ← hpre, List.take_left] at ht
  simpa only [hpre] using ht

/-- Lemma 3.3 Claims 6 and 7 for the full shell encoding and every valid
h-precursor map. The debt is zero at every earlier horizontal edge except
the shell root. No terminal connectedness is assumed: it follows from hx
and the surplus inequality he. -/
theorem shell_boundary_claims {E : ℕ → Edge} {N : ℕ} (u v ε : ℕ)
    (xs : List (List Edge × ℕ)) (hx : ∀ p ∈ xs, NodeRun p.1 p.2)
    (he : ε ≤ (xs.map Prod.snd).sum)
    (hw : (List.range' 0 N).map E = Shell xs u v ε)
    (P : KroneckerPredecessor.Vertical (sample E N) →
      KroneckerPredecessor.Horizontal (sample E N))
    (hp : KroneckerPredecessor.IsHorizontalPredecessor (sample E N) P)
    (i : ℕ) (hi : i ≤ xs.length) :
    (∀ x : KroneckerPredecessor.Horizontal (sample E N), x.val.val < boundaryIndex u xs i →
      KroneckerPredecessor.Debt (sample E N) P x (boundaryIndex u xs i) =
        if x.val.val = 0 then 1 else 0) ∧
    KroneckerCompatibility.balance E (boundaryIndex u xs i) =
      1 + (i : ℤ) + (((xs.take i).map Prod.snd).sum : ℤ) := by
  have hn : NodeRun ((List.range' 0 N).map E) ((xs.map Prod.snd).sum-ε) := by
    rw [hw]
    exact shell_node u (v-1) ε xs hx he
  obtain ⟨f, hf, _⟩ := valid_has_trace hp
  obtain ⟨hr, hprefix⟩ := shell_prefix u v ε xs hw i
  obtain ⟨hboundary, hb⟩ := boundary_trace hn hf u xs hx i hi _ hr hprefix
  exact ⟨fun x hx => boundary_debt hf hp hr.le hboundary x hx, hb⟩

end KroneckerShellBoundaryClaims
