import KroneckerTight

/- Original module: KroneckerSourceIntervalCounts -/
section
/-! Edge counts and grading sums on literal inclusive source subpaths.
These are the quantities in BLM-MR Definition 4.5, expressed independently
of the manuscript's cumulative debt and balance functions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceIntervalCounts
open KroneckerStack KroneckerCompatibility KroneckerColoring
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def hFlag : Edge → ℤ | .H _ => 1 | .V _ => 0
def vFlag : Edge → ℤ | .H _ => 0 | .V _ => 1
def hCount (E : ℕ → Edge) (s t : ℕ) : ℤ := ∑ i ∈ Finset.Ico s t, hFlag (E i)
def vCount (E : ℕ → Edge) (s t : ℕ) : ℤ := ∑ i ∈ Finset.Ico s t, vFlag (E i)
def hWeight (E : ℕ → Edge) (s t : ℕ) : ℤ := ∑ i ∈ Finset.Ico s t, hGrade (E i)
def vWeight (E : ℕ → Edge) (s t : ℕ) : ℤ := ∑ i ∈ Finset.Ico s t, vGrade (E i)

theorem hFlag_nonnegative (e : Edge) : 0 ≤ hFlag e := by cases e <;> simp [hFlag]

theorem vFlag_nonnegative (e : Edge) : 0 ≤ vFlag e := by cases e <;> simp [vFlag]

theorem flags_sum (e : Edge) : hFlag e + vFlag e = 1 := by cases e <;> rfl

theorem grade_split (e : Edge) : hGrade e + vGrade e = (e.grade : ℤ) := by
  cases e <;> simp [hGrade,vGrade,Edge.grade]

theorem debt_change (e : Edge) : e.debtChange = hGrade e-vFlag e := by
  cases e <;> simp [Edge.debtChange,hGrade,vFlag]

theorem credit_change (e : Edge) : e.credit = hFlag e-vGrade e := by
  cases e <;> simp [Edge.credit,vGrade,hFlag]

theorem walk_sum (f : Edge → ℤ) (E : ℕ → Edge) (n : ℕ) :
    walk f E n = ∑ i ∈ Finset.range n, f (E i) := by
  induction n with
  | zero => simp [walk]
  | succ n ih => simp only [walk,Finset.sum_range_succ,ih]

theorem interval_walk (f : Edge → ℤ) (E : ℕ → Edge) (s t : ℕ) (hst : s ≤ t) :
    ∑ i ∈ Finset.Ico s t, f (E i) = walk f E t-walk f E s := by
  rw [Finset.sum_Ico_eq_sub _ hst,walk_sum,walk_sum]

theorem debt_interval (E : ℕ → Edge) (s t : ℕ) (hst : s ≤ t) :
    hWeight E s t-vCount E s t = debt E t-debt E s := by
  unfold debt
  rw [← interval_walk Edge.debtChange E s t hst]
  simp only [hWeight,vCount,← Finset.sum_sub_distrib,debt_change]

theorem balance_interval (E : ℕ → Edge) (s t : ℕ) (hst : s ≤ t) :
    hCount E s t-vWeight E s t = balance E t-balance E s := by
  unfold balance
  rw [← interval_walk Edge.credit E s t hst]
  simp only [hCount,vWeight,← Finset.sum_sub_distrib,credit_change]

theorem horizontal_count_card (E : ℕ → Edge) (s t : ℕ) :
    hCount E s t = ((Finset.Ico s t).filter (fun i => Horizontal E i)).card := by
  classical
  simp only [hCount,Finset.card_eq_sum_ones, Nat.cast_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases he : E i <;> simp [hFlag,Horizontal,he]

theorem vertical_count_card (E : ℕ → Edge) (s t : ℕ) :
    vCount E s t = ((Finset.Ico s t).filter (fun i => Vertical E i)).card := by
  classical
  simp only [vCount,Finset.card_eq_sum_ones, Nat.cast_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases he : E i <;> simp [vFlag,Vertical,he]

theorem counts_length (E : ℕ → Edge) (s t : ℕ) :
    hCount E s t + vCount E s t = (t-s : ℕ) := by
  simp only [hCount,vCount,← Finset.sum_add_distrib,flags_sum]
  simp

theorem hCount_nonnegative (E : ℕ → Edge) (s t : ℕ) : 0 ≤ hCount E s t :=
  Finset.sum_nonneg fun i _ => hFlag_nonnegative (E i)

theorem vCount_nonnegative (E : ℕ → Edge) (s t : ℕ) : 0 ≤ vCount E s t :=
  Finset.sum_nonneg fun i _ => vFlag_nonnegative (E i)

theorem interval_add (f : Edge → ℤ) (E : ℕ → Edge) (s u t : ℕ) (hsu : s ≤ u) (hut : u ≤ t) :
    (∑ i ∈ Finset.Ico s u, f (E i)) + (∑ i ∈ Finset.Ico u t, f (E i)) =
      ∑ i ∈ Finset.Ico s t, f (E i) := by
  rw [interval_walk f E s u hsu,interval_walk f E u t hut,
    interval_walk f E s t (hsu.trans hut)]
  ring

end KroneckerSourceIntervalCounts
end
end

/- Original module: KroneckerSourceCompatibility -/
section
/-! Literal Definition 4.5, including both endpoint exclusions.
The source intervals include their edges; Ico s (t+1) is that interval.
The dictionary proves, rather than assumes, the debt/balance translation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceCompatibility
open KroneckerStack KroneckerCompatibility KroneckerColoring
open KroneckerSourceIntervalCounts

def HEquality (E : ℕ → Edge) (u e : ℕ) : Prop :=
  vCount E u (e+1) = hWeight E u (e+1)
def VEquality (E : ℕ → Edge) (e v : ℕ) : Prop :=
  hCount E e (v+1) = vWeight E e (v+1)
def SourceH (E : ℕ → Edge) (u v : ℕ) : Prop :=
  ∃ e, u≤e ∧ e<v ∧ Vertical E e ∧ HEquality E u e
def SourceV (E : ℕ → Edge) (u v : ℕ) : Prop :=
  ∃ e, u<e ∧ e≤v ∧ Horizontal E e ∧ VEquality E e v

def Linear (E : ℕ → Edge) (N : ℕ) : Prop :=
  ∀ u v,u<v→v<N→PositiveH E u→PositiveV E v→SourceH E u v ∨ SourceV E u v

def lift (N u v : ℕ) := if u≤v then v else v+N

def Cyclic (E : ℕ → Edge) (N : ℕ) : Prop :=
  ∀ u v,u<N→v<N→PositiveH E u→PositiveV E v→
    SourceH E u (lift N u v) ∨ SourceV E u (lift N u v)

theorem hEquality_iff_debt (E : ℕ → Edge) (u e : ℕ) (hue : u≤e+1) :
    HEquality E u e ↔ debt E (e+1)=debt E u := by
  have h := debt_interval E u (e+1) hue
  unfold HEquality
  omega

theorem vEquality_iff_balance (E : ℕ → Edge) (e v : ℕ) (hev : e≤v+1) :
    VEquality E e v ↔ balance E e=balance E (v+1) := by
  have h := balance_interval E e (v+1) hev
  unfold VEquality
  omega

theorem source_h_iff {E : ℕ → Edge} {u v : ℕ} (hu : PositiveH E u) :
    SourceH E u v ↔ HWitness E u v := by
  constructor
  · rintro ⟨e,he,hev,hV,hEq⟩
    have hne : u≠e := by
      rintro rfl
      obtain ⟨g,_,hg⟩ := hu
      obtain ⟨k,hk⟩ := hV
      rw [hg] at hk
      contradiction
    exact ⟨e,lt_of_le_of_ne he hne,hev,hV,(hEquality_iff_debt E u e (by omega)).mp hEq⟩
  · rintro ⟨e,he,hev,hV,hEq⟩
    exact ⟨e,he.le,hev,hV,(hEquality_iff_debt E u e (by omega)).mpr hEq⟩

theorem source_v_iff {E : ℕ → Edge} {u v : ℕ} (hv : PositiveV E v) :
    SourceV E u v ↔ VWitness E u v := by
  constructor
  · rintro ⟨e,he,hev,hH,hEq⟩
    have hne : e≠v := by
      rintro rfl
      obtain ⟨g,_,hg⟩ := hv
      obtain ⟨k,hk⟩ := hH
      rw [hg] at hk
      contradiction
    exact ⟨e,he,lt_of_le_of_ne hev hne,hH,(vEquality_iff_balance E e v (by omega)).mp hEq⟩
  · rintro ⟨e,he,hev,hH,hEq⟩
    exact ⟨e,he,hev.le,hH,(vEquality_iff_balance E e v (by omega)).mpr hEq⟩

theorem linear_iff (E : ℕ → Edge) (N : ℕ) : Linear E N ↔ LinearCompatible E N := by
  constructor <;> intro h u v huv hv huP hvP
  · exact (or_congr (source_h_iff huP) (source_v_iff hvP)).mp (h u v huv hv huP hvP)
  · exact (or_congr (source_h_iff huP) (source_v_iff hvP)).mpr (h u v huv hv huP hvP)

theorem trace_periodic {m N : ℕ} (shape : ℕ → Bool) (g : Coloring m N) (i : ℕ) :
    trace shape g (i+N)=trace shape g i := by
  simp only [trace,Nat.add_mod_right]

theorem lift_trace {m N : ℕ} (shape : ℕ → Bool) (g : Coloring m N) (u v : ℕ) :
    trace shape g (lift N u v)=trace shape g v := by
  unfold lift
  split_ifs <;> simp [trace_periodic]

theorem cyclic_iff {E : ℕ → Edge} {N : ℕ} (hp : ∀i,E (i+N)=E i) :
    Cyclic E N ↔ CyclicCompatible E N := by
  have hV : ∀u v, PositiveV E v→PositiveV E (lift N u v) := by
    intro u v hv
    unfold lift
    split_ifs
    · exact hv
    · simpa [PositiveV,hp] using hv
  constructor <;> intro h u v hu hv huP hvP
  · exact (or_congr (source_h_iff huP) (source_v_iff (hV u v hvP))).mp
      (h u v hu hv huP hvP)
  · exact (or_congr (source_h_iff huP) (source_v_iff (hV u v hvP))).mpr
      (h u v hu hv huP hvP)

end KroneckerSourceCompatibility
end
end

/- Original module: KroneckerSourceHorizontalShadow -/
section
/-! Definition 4.7's first equality, with the whole-path fallback.
These statements only translate literal source data; Lemmas 4.12 and 4.13
are not smuggled into the definitions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceHorizontalShadow
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerTight
open KroneckerSourceIntervalCounts KroneckerSourceCompatibility

def Shadow (E : ℕ → Edge) (u v : ℕ) : Prop :=
  ∀e,u≤e→e<v→Vertical E e→¬HEquality E u e

def FirstClosure (E : ℕ → Edge) (u e : ℕ) : Prop :=
  u≤e ∧ Vertical E e ∧ HEquality E u e ∧ Shadow E u e

def Support (E : ℕ → Edge) (N : ℕ) : Prop :=
  ∀v,v<N→PositiveV E v→∃u,u<N ∧ PositiveH E u ∧ Shadow E u (lift N u v)

theorem shadow_iff_not_source (E : ℕ → Edge) (u v : ℕ) :
    Shadow E u v ↔ ¬SourceH E u v := by
  simp only [Shadow,SourceH,not_exists,not_and]

theorem shadow_iff_internal {E : ℕ → Edge} {u v : ℕ} (hu : PositiveH E u) :
    Shadow E u v ↔ InHShadow E u v := by
  rw [shadow_iff_not_source,source_h_iff hu]
  rfl

theorem shadow_iff_active {E : ℕ → Edge} {u v : ℕ} (hu : PositiveH E u) :
    Shadow E u v ↔ Active E u v :=
  (shadow_iff_internal hu).trans (KroneckerTight.shadow_iff_active hu)

theorem shadow_of_no_closure {E : ℕ → Edge} {u t : ℕ}
    (h : ∀e,u≤e→e<t→Vertical E e→¬HEquality E u e) :
    ∀v,v≤t→Shadow E u v := by
  intro v hv e hue hev heV
  exact h e hue (hev.trans_le hv) heV

theorem first_in_shadow {E : ℕ → Edge} {u e : ℕ} (h : FirstClosure E u e) :
    Vertical E e ∧ Shadow E u e := ⟨h.2.1,h.2.2.2⟩

theorem first_unique {E : ℕ → Edge} {u e f : ℕ}
    (he : FirstClosure E u e) (hf : FirstClosure E u f) : e=f := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact hf.2.2.2 e he.1 hlt he.2.1 he.2.2.1
  · exact he.2.2.2 f hf.1 hgt hf.2.1 hf.2.2.1

theorem beyond_first_not_shadow {E : ℕ → Edge} {u e v : ℕ}
    (h : FirstClosure E u e) (hev : e<v) : ¬Shadow E u v := by
  intro hs
  exact hs e h.1 hev h.2.1 h.2.2.1

theorem first_return_debt {E : ℕ → Edge} {u e : ℕ}
    (hu : PositiveH E u) (h : FirstClosure E u e) :
    debt E (e+1)=debt E u ∧ ∀j,u<j→j<e+1→debt E j≠debt E u := by
  refine ⟨(hEquality_iff_debt E u e (by have := h.1; omega)).mp h.2.2.1,?_⟩
  intro j huj hje
  exact ne_of_gt ((shadow_iff_active hu).mp h.2.2.2 j huj (by omega))

theorem closure_exists {E : ℕ → Edge} {u N : ℕ} (hN : 1≤N)
    (hu : PositiveH E u) (hTotal : hWeight E u (u+N)≤vCount E u (u+N)) :
    ∃e,u≤e ∧ e<u+N ∧ Vertical E e ∧ HEquality E u e := by
  have hEnd : debt E (u+N)≤debt E u := by
    have h := debt_interval E u (u+N) (by omega)
    omega
  have hStart : debt E u<debt E (u+1) := by
    obtain ⟨g,hg,he⟩ := hu
    rw [debt_step,he]
    simp only [Edge.debtChange]
    exact lt_add_of_pos_right _ (by exact_mod_cast hg)
  obtain ⟨e,hue,heN,heV,hEq⟩ := debt_crossing E (debt E u) (by omega : u+1≤u+N) hStart hEnd
  exact ⟨e,by omega,heN,heV,(hEquality_iff_debt E u e (by omega)).mpr hEq⟩

theorem first_exists {E : ℕ → Edge} {u N : ℕ} (hN : 1≤N)
    (hu : PositiveH E u) (hTotal : hWeight E u (u+N)≤vCount E u (u+N)) :
    ∃e,e<u+N ∧ FirstClosure E u e := by
  classical
  let hex := closure_exists hN hu hTotal
  let e := Nat.find hex
  have he := Nat.find_spec hex
  refine ⟨e,he.2.1,he.1,he.2.2.1,he.2.2.2,?_⟩
  intro f huf hfe hfV hfEq
  exact Nat.find_min hex hfe ⟨huf,hfe.trans he.2.1,hfV,hfEq⟩

theorem support_iff_internal (E : ℕ → Edge) (N : ℕ) :
    Support E N ↔ ShadowSupport E N := by
  constructor <;> intro h v hv hvP
  · obtain ⟨u,hu,huP,hs⟩ := h v hv hvP
    exact ⟨u,hu,huP,(shadow_iff_internal huP).mp hs⟩
  · obtain ⟨u,hu,huP,hs⟩ := h v hv hvP
    exact ⟨u,hu,huP,(shadow_iff_internal huP).mpr hs⟩

theorem vertical_witness_on_shadow {E : ℕ → Edge} {u v : ℕ}
    (hc : SourceH E u v ∨ SourceV E u v) (hs : Shadow E u v) : SourceV E u v := by
  exact hc.resolve_left ((shadow_iff_not_source E u v).mp hs)

end KroneckerSourceHorizontalShadow
end
end
