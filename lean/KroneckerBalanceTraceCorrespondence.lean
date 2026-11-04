import KroneckerManuscriptNotationSync
import KroneckerPaperTraceBridge
import KroneckerPaperExecutionTrace

/-! The indexed trace records the manuscript's predecessor debts at every
prefix. The recorded order is the most-recent-horizontal-first order. -/

noncomputable section
set_option autoImplicit false
namespace KroneckerBalanceTraceCorrespondence
open KroneckerStack KroneckerShadow KroneckerPredecessor KroneckerPaperTraceBridge

/-- The debt recorded at an earlier horizontal occurrence equals the paper's
grade minus the number of vertical edges assigned to it. -/
theorem trace_remaining_eq_debt {E : ℕ → Edge} {n r : ℕ}
    {f : ℕ → List Entry}
    {P : Vertical (sample E n) → Horizontal (sample E n)}
    (ht : RawTrace E n f) (hp : IsHorizontalPredecessor (sample E n) P)
    (hr : r ≤ n) (x : Horizontal (sample E n)) (hx : x.val.val < r) :
    remaining (f r) x.val.val = Debt (sample E n) P x r := by
  have hf := predecessor_followsTrace ht hp
  have hc := trace_counts ht hf hr x.val
  have hcap : capacity (sample E n) r x.val = ((sample E n) x.val).grade := by
    simp [capacity, hx, x.property]
  rw [hcap] at hc
  unfold Debt assignedBefore
  omega

/-- A positive geometric debt is represented by an actual trace entry. -/
theorem positive_debt_has_entry {E : ℕ → Edge} {n r : ℕ}
    {f : ℕ → List Entry}
    {P : Vertical (sample E n) → Horizontal (sample E n)}
    (ht : RawTrace E n f) (hp : IsHorizontalPredecessor (sample E n) P)
    (hr : r ≤ n) (x : Horizontal (sample E n)) (hx : x.val.val < r)
    (hd : 0 < Debt (sample E n) P x r) :
    ∃ y ∈ f r, y.origin = x.val.val ∧ y.debt = Debt (sample E n) P x r := by
  have hc := trace_remaining_eq_debt ht hp hr x hx
  obtain ⟨y,hy,hid⟩ := remaining_pos_origin (by omega : 0 < remaining (f r) x.val.val)
  refine ⟨y,hy,hid, ?_⟩
  exact predecessor_entry_debt ht hp hr hy x (by simpa using hid.symm)

/-- Trace entries are ordered by their horizontal occurrence, with the
latest first, and have exactly their predecessor debt. -/
theorem trace_entry_dictionary {E : ℕ → Edge} {n r : ℕ}
    {f : ℕ → List Entry}
    {P : Vertical (sample E n) → Horizontal (sample E n)}
    (ht : RawTrace E n f) (hp : IsHorizontalPredecessor (sample E n) P)
    (hr : r ≤ n) :
    Descending (f r) ∧ Before r (f r) ∧
      ∀ x ∈ f r, ∃ h : Horizontal (sample E n),
        h.val.val = x.origin ∧ x.debt = Debt (sample E n) P h r := by
  obtain ⟨hb,ho⟩ := trace_order ht hr
  refine ⟨ho,hb, ?_⟩
  intro x hx
  have hor : x.origin < n := (hb x hx).trans_le hr
  obtain ⟨_, grade, _, he⟩ := floors_member (trace_invariants ht hr).1 hx
  have hh : IsHorizontal (sample E n) ⟨x.origin,hor⟩ := by
    simp [IsHorizontal, sample, he]
  let y : Horizontal (sample E n) := ⟨⟨x.origin,hor⟩,hh⟩
  exact ⟨y,rfl,predecessor_entry_debt ht hp hr hx y rfl⟩

/-- The positive-debt entries obtained directly from the manuscript's
horizontal occurrences, listed in reverse path order. -/
def occurrenceEntry (E : ℕ → Edge) (n r : ℕ)
    (P : Vertical (sample E n) → Horizontal (sample E n)) (i : Fin n) : Option Entry := by
  classical
  exact if h : IsHorizontal (sample E n) i then
    let d := Debt (sample E n) P ⟨i,h⟩ r
    if d = 0 then none else some ⟨i.val,d⟩
  else none

def occurrenceEntries (E : ℕ → Edge) (n r : ℕ)
    (P : Vertical (sample E n) → Horizontal (sample E n)) : List Entry :=
  ((List.finRange n).take r).reverse.filterMap (occurrenceEntry E n r P)

theorem occurrenceEntry_origin {E : ℕ → Edge} {n r : ℕ}
    {P : Vertical (sample E n) → Horizontal (sample E n)}
    {i : Fin n} {x : Entry} (h : occurrenceEntry E n r P i = some x) :
    x.origin = i.val := by
  classical
  unfold occurrenceEntry at h
  split at h
  · dsimp only at h
    split at h
    · contradiction
    · cases h
      rfl
  · contradiction

theorem mem_finRange_take {n r : ℕ} (i : Fin n) :
    i ∈ (List.finRange n).take r ↔ i.val < r := by
  rw [List.mem_take_iff_getElem]
  simp only [List.length_finRange, List.getElem_finRange]
  constructor
  · rintro ⟨j,hj,h⟩
    have he := congrArg Fin.val h
    simp at he
    omega
  · intro hi
    exact ⟨i.val, by omega, Fin.ext rfl⟩

theorem occurrenceEntries_descending (E : ℕ → Edge) (n r : ℕ)
    (P : Vertical (sample E n) → Horizontal (sample E n)) :
    Descending (occurrenceEntries E n r P) := by
  unfold Descending occurrenceEntries
  apply List.pairwise_filterMap.mpr
  have hs : (((List.finRange n).take r).reverse).Pairwise (fun i j : Fin n => j.val < i.val) := by
    rw [List.pairwise_reverse]
    exact (List.pairwise_lt_finRange n).take
  apply hs.imp
  intro i j hij x hx y hy
  rw [occurrenceEntry_origin hx, occurrenceEntry_origin hy]
  exact hij

theorem occurrenceEntry_spec {E : ℕ → Edge} {n r : ℕ}
    {P : Vertical (sample E n) → Horizontal (sample E n)}
    {i : Fin n} {x : Entry} :
    occurrenceEntry E n r P i = some x ↔
      ∃ hi : IsHorizontal (sample E n) i,
        x.origin = i.val ∧ x.debt = Debt (sample E n) P ⟨i,hi⟩ r ∧
          0 < Debt (sample E n) P ⟨i,hi⟩ r := by
  classical
  by_cases hi : IsHorizontal (sample E n) i
  · by_cases hd : Debt (sample E n) P ⟨i,hi⟩ r = 0
    · simp [occurrenceEntry,hi,hd]
    · simp [occurrenceEntry,hi,hd, Nat.pos_of_ne_zero hd]
      constructor
      · intro h
        cases h
        simp
      · rintro ⟨h1,h2⟩
        cases x
        simp_all
  · simp [occurrenceEntry,hi]

theorem mem_occurrenceEntries_iff {E : ℕ → Edge} {n r : ℕ}
    {P : Vertical (sample E n) → Horizontal (sample E n)} {x : Entry} :
    x ∈ occurrenceEntries E n r P ↔
      ∃ i : Horizontal (sample E n), i.val.val < r ∧ x.origin = i.val.val ∧
        x.debt = Debt (sample E n) P i r ∧ 0 < Debt (sample E n) P i r := by
  classical
  simp only [occurrenceEntries, List.mem_filterMap, List.mem_reverse, mem_finRange_take]
  constructor
  · rintro ⟨i,hi,hx⟩
    obtain ⟨hh,ho,hd,hp⟩ := occurrenceEntry_spec.mp hx
    exact ⟨⟨i,hh⟩,hi,ho,hd,hp⟩
  · rintro ⟨⟨i,hi⟩,hr,ho,hd,hp⟩
    exact ⟨i,hr,occurrenceEntry_spec.mpr ⟨hi,ho,hd,hp⟩⟩

theorem descending_nodup {xs : List Entry} (h : Descending xs) : xs.Nodup := by
  apply h.imp
  intro a b hab he
  subst b
  exact (Nat.lt_irrefl a.origin) hab

/-- The complete indexed trace is the ordered list of all positive debts. -/
theorem trace_eq_occurrenceEntries {E : ℕ → Edge} {n r : ℕ}
    {f : ℕ → List Entry}
    {P : Vertical (sample E n) → Horizontal (sample E n)}
    (ht : RawTrace E n f) (hp : IsHorizontalPredecessor (sample E n) P)
    (hr : r ≤ n) : f r = occurrenceEntries E n r P := by
  classical
  obtain ⟨hs,hbefore,hdict⟩ := trace_entry_dictionary ht hp hr
  have hg := occurrenceEntries_descending E n r P
  have hm : ∀ x, x ∈ f r ↔ x ∈ occurrenceEntries E n r P := by
    intro x
    constructor
    · intro hx
      obtain ⟨i,ho,hd⟩ := hdict x hx
      obtain ⟨hpos, _⟩ := floors_member (trace_invariants ht hr).1 hx
      apply mem_occurrenceEntries_iff.mpr
      exact ⟨i,by rw [ho]; exact hbefore x hx,ho.symm,hd,by omega⟩
    · intro hx
      obtain ⟨i,hi,ho,hd,hpos⟩ := mem_occurrenceEntries_iff.mp hx
      obtain ⟨y,hy,hyo,hyd⟩ := positive_debt_has_entry ht hp hr i hi hpos
      have heq : x = y := by
        cases x
        cases y
        simp_all
      rw [heq]
      exact hy
  have hperm : List.Perm (f r) (occurrenceEntries E n r P) :=
    (List.perm_ext_iff_of_nodup (descending_nodup hs) (descending_nodup hg)).mpr hm
  apply List.Perm.eq_of_pairwise
    (le := fun a b : Entry => b.origin < a.origin ∨ a = b)
    ?_ (hs.imp (fun h => Or.inl h)) (hg.imp (fun h => Or.inl h)) hperm
  intro a b _ _ hab hba
  rcases hab with hab | hab
  · rcases hba with hba | hba
    · omega
    · exact hba.symm
  · exact hab

/-- Expand the geometric debt at each horizontal occurrence into its
repeated boundary balance, in reverse occurrence order. -/
def occurrenceBoundary (E : ℕ → Edge) (n r : ℕ)
    (P : Vertical (sample E n) → Horizontal (sample E n)) : List ℤ := by
  classical
  exact ((List.finRange n).take r).reverse.flatMap fun i =>
    if h : IsHorizontal (sample E n) i then
      List.replicate (Debt (sample E n) P ⟨i,h⟩ r)
        (KroneckerCompatibility.balance E (i.val+1))
    else []

theorem entries_flatMap_boundary (E : ℕ → Edge) (n r : ℕ)
    (P : Vertical (sample E n) → Horizontal (sample E n)) :
    (occurrenceEntries E n r P).flatMap
      (fun x => List.replicate x.debt (KroneckerCompatibility.balance E (x.origin+1))) =
        occurrenceBoundary E n r P := by
  classical
  unfold occurrenceEntries occurrenceBoundary
  generalize ((List.finRange n).take r).reverse = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      by_cases hi : IsHorizontal (sample E n) i
      · by_cases hd : Debt (sample E n) P ⟨i,hi⟩ r = 0
        · simp [occurrenceEntry,hi,hd,ih]
        · simp [occurrenceEntry,hi,hd,ih]
      · simp [occurrenceEntry,hi,ih]

/-- The literal predecessor-based boundary list is the flattened compressed
stack, for every prefix of every valid predecessor trace. -/
theorem occurrenceBoundary_eq_trace_units {E : ℕ → Edge} {n r : ℕ}
    {f : ℕ → List Entry}
    {P : Vertical (sample E n) → Horizontal (sample E n)}
    (ht : RawTrace E n f) (hp : IsHorizontalPredecessor (sample E n) P)
    (hr : r ≤ n) :
    occurrenceBoundary E n r P =
      KroneckerDebtUnits.units (eraseState E r (f r)).stack := by
  rw [trace_eq_occurrenceEntries ht hp hr]
  simpa [eraseState,KroneckerDebtUnits.units,List.flatMap_map] using
    (entries_flatMap_boundary E n r P).symm

open KroneckerPaperPaths
open KroneckerPaperPathGradings (Horizontal Vertical edgeIndex)

def horizontalAt {Y : TNEPath} (i : Fin Y.steps.length)
    (hi : Y.steps.get i = true) : Horizontal Y :=
  ⟨edgeEquiv Y i, by simpa using hi⟩

def geometricIndexBoundary {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y)
    (p : Vertical Y → Horizontal Y) (r : ℕ) : List ℤ := by
  classical
  exact ((List.finRange Y.steps.length).take r).reverse.flatMap fun i =>
    if hi : Y.steps.get i = true then
      let x := horizontalAt i hi
      List.replicate (KroneckerNaturalPathGradings.Debt g p x r).toNat
        (KroneckerNaturalPathGradings.eBal g x.val)
    else []

theorem geometricBalList_by_index {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y)
    (p : Vertical Y → Horizontal Y) (r : ℕ) :
    KroneckerNaturalPathGradings.BalList g p r = geometricIndexBoundary g p r := by
  classical
  unfold KroneckerNaturalPathGradings.BalList KroneckerNaturalPathGradings.horizontalPrefix
    geometricIndexBoundary
  rw [List.ofFn_eq_map, ← List.map_take, List.filterMap_map, ← List.filterMap_reverse]
  generalize ((List.finRange Y.steps.length).take r).reverse = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      by_cases hi : Y.steps.get i = true
      · simp only [List.get_eq_getElem] at hi ⊢ ih
        simp [List.filterMap,Function.comp_apply,hi,horizontalAt]
        simpa [Function.comp_apply, horizontalAt] using ih
      · simp only [List.get_eq_getElem] at hi ⊢ ih
        simp [List.filterMap,Function.comp_apply,hi]
        simpa [Function.comp_apply, horizontalAt] using ih

def castPrecursor {n : ℕ} {U V : Word n} (h : U = V)
    (p : KroneckerPredecessor.Vertical U → KroneckerPredecessor.Horizontal U) :
    KroneckerPredecessor.Vertical V → KroneckerPredecessor.Horizontal V := h ▸ p

def castHorizontal {n : ℕ} {U V : Word n} (h : U = V)
    (x : KroneckerPredecessor.Horizontal U) : KroneckerPredecessor.Horizontal V := h ▸ x

theorem castPrecursor_valid {n : ℕ} {U V : Word n} (h : U = V)
    (p : KroneckerPredecessor.Vertical U → KroneckerPredecessor.Horizontal U)
    (hp : IsHorizontalPredecessor U p) : IsHorizontalPredecessor V (castPrecursor h p) := by
  cases h
  exact hp

theorem castHorizontal_val {n : ℕ} {U V : Word n} (h : U = V)
    (x : KroneckerPredecessor.Horizontal U) : (castHorizontal h x).val = x.val := by
  cases h
  rfl

theorem castDebt {n : ℕ} {U V : Word n} (h : U = V)
    (p : KroneckerPredecessor.Vertical U → KroneckerPredecessor.Horizontal U)
    (x : KroneckerPredecessor.Horizontal U) (r : ℕ) :
    Debt V (castPrecursor h p) (castHorizontal h x) r = Debt U p x r := by
  cases h
  rfl

theorem geometricWord_eq {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y) :
    KroneckerPaperPathGradings.occurrenceWord (KroneckerNaturalPathGradings.bounded g) =
      sample (KroneckerNaturalPathGradings.geometricTrace g) Y.steps.length := by
  rw [← KroneckerNaturalPathGradings.trace_bounded]
  exact KroneckerPaperPathGradings.occurrenceWord_raw (KroneckerNaturalPathGradings.bounded g)

def geometricPrecursor {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y)
    (p : Vertical Y → Horizontal Y) :
    KroneckerPredecessor.Vertical (sample (KroneckerNaturalPathGradings.geometricTrace g)
      Y.steps.length) →
    KroneckerPredecessor.Horizontal (sample (KroneckerNaturalPathGradings.geometricTrace g)
      Y.steps.length) :=
  castPrecursor (geometricWord_eq g)
    (KroneckerPaperPathGradings.predecessorOccurrences (KroneckerNaturalPathGradings.bounded g) p)

theorem geometricPrecursor_valid {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y)
    (p : Vertical Y → Horizontal Y) (hp : KroneckerNaturalPathGradings.IsHPrecursor g p) :
    IsHorizontalPredecessor (sample (KroneckerNaturalPathGradings.geometricTrace g)
      Y.steps.length) (geometricPrecursor g p) := by
  apply castPrecursor_valid
  exact (KroneckerPaperPathGradings.isPredecessor_iff _ p).mp
    ((KroneckerPaperPathGradings.isHPrecursor_iff _ p).mp hp)

theorem geometric_horizontal_iff {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y)
    (i : Fin Y.steps.length) :
    IsHorizontal (sample (KroneckerNaturalPathGradings.geometricTrace g) Y.steps.length) i ↔
      Y.steps.get i = true := by
  rw [← geometricWord_eq g]
  exact KroneckerPaperPathGradings.occurrenceWord_horizontal
    (KroneckerNaturalPathGradings.bounded g) i

theorem geometric_occurrence_index {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y)
    (i : Fin Y.steps.length) (hi : Y.steps.get i = true) :
    (castHorizontal (geometricWord_eq g)
      (KroneckerPaperPathGradings.horizontalEquiv (KroneckerNaturalPathGradings.bounded g)
        (horizontalAt i hi))).val = i := by
  rw [castHorizontal_val]
  simp [KroneckerPaperPathGradings.horizontalEquiv, Equiv.subtypeEquiv, horizontalAt]

theorem geometric_occurrence_debt {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y)
    (p : Vertical Y → Horizontal Y) (hp : KroneckerNaturalPathGradings.IsHPrecursor g p)
    (r : ℕ) (hr : r ≤ Y.steps.length) (i : Fin Y.steps.length)
    (hi : Y.steps.get i = true) :
    Debt (sample (KroneckerNaturalPathGradings.geometricTrace g) Y.steps.length)
      (geometricPrecursor g p)
      ⟨i,(geometric_horizontal_iff g i).mpr hi⟩ r =
        (KroneckerNaturalPathGradings.Debt g p (horizontalAt i hi) r).toNat := by
  let x := horizontalAt i hi
  have hx : (⟨i,(geometric_horizontal_iff g i).mpr hi⟩ :
      KroneckerPredecessor.Horizontal
        (sample (KroneckerNaturalPathGradings.geometricTrace g) Y.steps.length)) =
      castHorizontal (geometricWord_eq g)
        (KroneckerPaperPathGradings.horizontalEquiv (KroneckerNaturalPathGradings.bounded g) x) := by
    apply Subtype.ext
    exact (geometric_occurrence_index g i hi).symm
  rw [hx]
  change Debt _ (castPrecursor (geometricWord_eq g) _) (castHorizontal (geometricWord_eq g) _) _ = _
  rw [castDebt]
  have hf := KroneckerPaperPathGradings.hPrecursor_debt_formula
    (KroneckerNaturalPathGradings.bounded g) p hp x r hr
  change ((KroneckerPaperPathGradings.Debt (KroneckerNaturalPathGradings.bounded g) p x r : ℕ) : ℤ) =
    KroneckerNaturalPathGradings.Debt g p x r at hf
  rw [← hf, Int.toNat_natCast]
  unfold KroneckerPaperPathGradings.Debt KroneckerPredecessor.Debt
  rw [← KroneckerPaperPathGradings.assignmentCount_occurrences]
  simp [KroneckerPaperPathGradings.horizontalEquiv, Equiv.subtypeEquiv]

theorem geometric_occurrence_balance {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y)
    (i : Fin Y.steps.length) (hi : Y.steps.get i = true) :
    KroneckerNaturalPathGradings.eBal g (horizontalAt i hi).val =
      KroneckerCompatibility.balance (KroneckerNaturalPathGradings.geometricTrace g) (i.val+1) := by
  simp [KroneckerNaturalPathGradings.eBal, KroneckerNaturalPathGradings.bBal, horizontalAt]

theorem geometricIndexBoundary_eq_occurrenceBoundary {Y : TNEPath}
    (g : KroneckerNaturalPathGradings.Grading Y) (p : Vertical Y → Horizontal Y)
    (hp : KroneckerNaturalPathGradings.IsHPrecursor g p) (r : ℕ) (hr : r ≤ Y.steps.length) :
    geometricIndexBoundary g p r = occurrenceBoundary (KroneckerNaturalPathGradings.geometricTrace g)
      Y.steps.length r (geometricPrecursor g p) := by
  classical
  unfold geometricIndexBoundary occurrenceBoundary
  generalize ((List.finRange Y.steps.length).take r).reverse = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      by_cases hi : Y.steps.get i = true
      · have hi' := (geometric_horizontal_iff g i).mpr hi
        simp only [List.get_eq_getElem] at hi ⊢ ih
        simp [hi,hi', ← geometric_occurrence_debt g p hp r hr i hi,
          geometric_occurrence_balance g i hi,ih]
      · have hi' : ¬ IsHorizontal (sample (KroneckerNaturalPathGradings.geometricTrace g)
            Y.steps.length) i := by simpa [geometric_horizontal_iff] using hi
        simp only [List.get_eq_getElem] at hi ⊢ ih
        simp [hi,hi',ih]

/-- The manuscript's geometric balance list is exactly the flattened
compressed predecessor trace at every prefix. -/
theorem geometricBalList_eq_trace_units {Y : TNEPath}
    (g : KroneckerNaturalPathGradings.Grading Y) (p : Vertical Y → Horizontal Y)
    (hp : KroneckerNaturalPathGradings.IsHPrecursor g p) (r : ℕ) (hr : r ≤ Y.steps.length)
    {f : ℕ → List Entry}
    (ht : RawTrace (KroneckerNaturalPathGradings.geometricTrace g) Y.steps.length f) :
    KroneckerNaturalPathGradings.BalList g p r =
      KroneckerDebtUnits.units
        (eraseState (KroneckerNaturalPathGradings.geometricTrace g) r (f r)).stack := by
  rw [geometricBalList_by_index, geometricIndexBoundary_eq_occurrenceBoundary g p hp r hr]
  exact occurrenceBoundary_eq_trace_units ht (geometricPrecursor_valid g p hp) hr

theorem geometricBalList_zero {Y : TNEPath} (g : KroneckerNaturalPathGradings.Grading Y)
    (p : Vertical Y → Horizontal Y) : KroneckerNaturalPathGradings.BalList g p 0 = [] := by
  simp [geometricBalList_by_index, geometricIndexBoundary]

/-- For a connected geometric grading the actual guarded stack executor,
started at the first edge, produces precisely the paper's boundary list. -/
theorem geometricBalList_eq_guarded_execution {Y : TNEPath}
    (g : KroneckerNaturalPathGradings.Grading Y) (p : Vertical Y → Horizontal Y)
    (hp : KroneckerNaturalPathGradings.IsHPrecursor g p)
    (hg : KroneckerNaturalPathGradings.ConnectedGrading g)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ Y.steps.length) :
    ∃ k s, KroneckerNaturalPathGradings.geometricTrace g 0 = .H (k+1) ∧
      execute ((List.range' 1 (r-1)).map (KroneckerNaturalPathGradings.geometricTrace g))
        ⟨1,[⟨k+1,1⟩]⟩ = some s ∧
      KroneckerNaturalPathGradings.BalList g p r = KroneckerDebtUnits.units s.stack := by
  let E := KroneckerNaturalPathGradings.geometricTrace g
  have hn := KroneckerPaperConnected.connected_nodeRun hg
  obtain ⟨f, ht, hguard⟩ := KroneckerPaperExecutionTrace.nodeRun_guardedTrace hn
  have hroot := KroneckerPaperExecutionTrace.nodeRun_rootComponent hn
  obtain ⟨k, he, hf⟩ := trace_first hroot ht
  change E 0 = .H (k+1) at he
  have hbal : KroneckerCompatibility.balance E 1 = 1 := by
    simp [KroneckerCompatibility.balance, KroneckerCompatibility.walk, he, Edge.credit]
  have hex := KroneckerPaperConnected.execute_trace_segment hguard 1 (r-1) (by omega) (by omega)
  have hstart : eraseState E 1 (f 1) = ⟨1,[⟨k+1,1⟩]⟩ := by
    simp [eraseState,hf,hbal]
  rw [hstart] at hex
  have hend : 1 + (r-1) = r := by omega
  rw [hend] at hex
  exact ⟨k, eraseState E r (f r), he, hex, geometricBalList_eq_trace_units g p hp r hr ht⟩

end KroneckerBalanceTraceCorrespondence

#print axioms KroneckerBalanceTraceCorrespondence.trace_remaining_eq_debt
#print axioms KroneckerBalanceTraceCorrespondence.positive_debt_has_entry
#print axioms KroneckerBalanceTraceCorrespondence.trace_entry_dictionary
#print axioms KroneckerBalanceTraceCorrespondence.trace_eq_occurrenceEntries
#print axioms KroneckerBalanceTraceCorrespondence.occurrenceBoundary_eq_trace_units
#print axioms KroneckerBalanceTraceCorrespondence.geometricBalList_by_index
#print axioms KroneckerBalanceTraceCorrespondence.geometricBalList_eq_trace_units
#print axioms KroneckerBalanceTraceCorrespondence.geometricBalList_eq_guarded_execution
