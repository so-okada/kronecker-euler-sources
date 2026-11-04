import KroneckerCompatibility

/-!
The debt parser with the opening edge retained on each node. This information
identifies each node with a horizontal shadow; it does not change any grade.
-/
set_option autoImplicit false
namespace KroneckerShadow
open KroneckerStack KroneckerCompatibility

structure Entry where
  origin : ℕ
  debt : ℕ
  deriving DecidableEq, Repr

def mass (ns : List Entry) : ℤ := (ns.map fun x => (x.debt : ℤ)).sum

inductive Floors (E : ℕ → Edge) : List Entry → Prop where
  | nil : Floors E []
  | cons {x : Entry} {xs : List Entry} : Floors E xs → 0 < x.debt →
      PositiveH E x.origin → debt E x.origin = mass xs → Floors E (x::xs)

def Open (E : ℕ → Edge) (u k : ℕ) : Prop :=
  u < k ∧ PositiveH E u ∧ Active E u k

def Lives (E : ℕ → Edge) (k : ℕ) (ns : List Entry) : Prop :=
  ∀ u, (∃ x ∈ ns, x.origin = u) ↔ Open E u k

inductive RawStep (E : ℕ → Edge) (k : ℕ) : List Entry → List Entry → Prop where
  | hz {xs} : E k = .H 0 → RawStep E k xs xs
  | hp {xs g} : E k = .H (g+1) → RawStep E k xs (⟨k,g+1⟩::xs)
  | one {x xs g} : E k = .V g → x.debt = 1 → RawStep E k (x::xs) xs
  | many {x xs g} : E k = .V g → 1 < x.debt →
      RawStep E k (x::xs) (⟨x.origin,x.debt-1⟩::xs)

theorem mass_nonneg (ns : List Entry) : 0 ≤ mass ns := by
  exact List.sum_nonneg (by intro z hz; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hz; positivity)

theorem floor_lt_mass {E : ℕ → Edge} {ns : List Entry}
    (hf : Floors E ns) {x : Entry} (hx : x ∈ ns) : debt E x.origin < mass ns := by
  induction hf with
  | nil => simp at hx
  | @cons y ys hf hd hh he ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [mass, List.map_cons, List.sum_cons]
      change debt E x.origin < (x.debt : ℤ) + mass ys
      omega
    · have hi := ih hx
      simp only [mass, List.map_cons, List.sum_cons]
      change debt E x.origin < (y.debt : ℤ) + mass ys
      omega

theorem active_succ {E : ℕ → Edge} {u k : ℕ} (huk : u < k) :
    Active E u (k+1) ↔ Active E u k ∧ debt E u < debt E (k+1) := by
  constructor
  · intro ha
    exact ⟨fun j huj hjk => ha j huj (by omega), ha (k+1) (by omega) (by omega)⟩
  · rintro ⟨ha, hd⟩ j huj hjk
    by_cases h : j ≤ k
    · exact ha j huj h
    · have : j=k+1 := by omega
      simpa [this] using hd

theorem open_succ (E : ℕ → Edge) (u k : ℕ) :
    Open E u (k+1) ↔
      (u=k ∧ PositiveH E k) ∨ (Open E u k ∧ debt E u < debt E (k+1)) := by
  constructor
  · rintro ⟨huk, hh, ha⟩
    by_cases h : u=k
    · exact Or.inl ⟨h, h ▸ hh⟩
    · have hu : u<k := by omega
      obtain ⟨hb, hd⟩ := (active_succ hu).mp ha
      exact Or.inr ⟨⟨hu,hh,hb⟩,hd⟩
  · rintro (⟨rfl,hh⟩ | ⟨ho,hd⟩)
    · refine ⟨by omega,hh,?_⟩
      intro j hkj hjk
      have : j=u+1 := by omega
      subst j
      obtain ⟨g,hg,he⟩ := hh
      rw [debt_step,he]
      simp only [Edge.debtChange]
      omega
    · exact ⟨Nat.lt_trans ho.1 (Nat.lt_succ_self k),ho.2.1,(active_succ ho.1).mpr ⟨ho.2.2,hd⟩⟩

theorem floors_cons_iff (E : ℕ → Edge) (x : Entry) (xs : List Entry) :
    Floors E (x::xs) ↔ Floors E xs ∧ 0 < x.debt ∧
      PositiveH E x.origin ∧ debt E x.origin = mass xs := by
  constructor
  · intro h
    cases h with
    | cons ht hd hh ho => exact ⟨ht,hd,hh,ho⟩
  · rintro ⟨ht,hd,hh,ho⟩
    exact Floors.cons ht hd hh ho

theorem raw_preserves_floors {E : ℕ → Edge} {k : ℕ} {xs ys : List Entry}
    (hr : RawStep E k xs ys) (hf : Floors E xs) (hm : mass xs = debt E k) :
    Floors E ys ∧ mass ys = debt E (k+1) := by
  cases hr with
  | hz he =>
    refine ⟨hf,?_⟩
    simpa [debt_step,he,Edge.debtChange] using hm
  | @hp xs g he =>
    constructor
    · exact Floors.cons hf (by simp) ⟨g+1,by omega,he⟩ hm.symm
    · simp only [mass,List.map_cons,List.sum_cons]
      change ((g+1 : ℕ) : ℤ) + mass xs = debt E (k+1)
      rw [debt_step,he]
      simp only [Edge.debtChange,Nat.cast_add,Nat.cast_one]
      omega
  | @one x xs g he hd =>
    obtain ⟨ht, _, _, _⟩ := (floors_cons_iff E x ys).mp hf
    refine ⟨ht,?_⟩
    simp only [mass,List.map_cons,List.sum_cons,hd,Nat.cast_one] at hm
    change 1 + mass ys = debt E k at hm
    rw [debt_step,he]
    simp only [Edge.debtChange]
    omega
  | @many x xs g he hd =>
    obtain ⟨ht, _, hh, ho⟩ := (floors_cons_iff E x xs).mp hf
    constructor
    · exact Floors.cons ht (by simp; omega) hh ho
    · simp only [mass,List.map_cons,List.sum_cons] at hm ⊢
      change (x.debt : ℤ) + mass xs = debt E k at hm
      change ((x.debt-1 : ℕ) : ℤ) + mass xs = debt E (k+1)
      rw [debt_step,he]
      simp only [Edge.debtChange]
      have hn : 1 ≤ x.debt := by omega
      rw [Nat.cast_sub hn,Nat.cast_one]
      omega

theorem raw_preserves_lives {E : ℕ → Edge} {k : ℕ} {xs ys : List Entry}
    (hr : RawStep E k xs ys) (hf : Floors E xs) (hm : mass xs = debt E k)
    (hl : Lives E k xs) : Lives E (k+1) ys := by
  intro u
  rw [open_succ]
  cases hr with
  | hz he =>
    have hn : ¬ PositiveH E k := by
      rintro ⟨g,hg,hgE⟩
      rw [he] at hgE
      cases hgE
      omega
    simp only [hn,and_false,false_or]
    rw [hl u]
    constructor
    · intro ho
      refine ⟨ho,?_⟩
      rw [debt_step,he]
      simpa [Edge.debtChange] using ho.2.2 k ho.1 (by omega)
    · exact And.left
  | @hp xs g he =>
    have hh : PositiveH E k := ⟨g+1,by omega,he⟩
    simp only [List.mem_cons,exists_eq_or_imp,hh,and_true]
    rw [hl u]
    constructor
    · rintro (h | ho)
      · exact Or.inl h.symm
      · right
        refine ⟨ho,?_⟩
        have := ho.2.2 k ho.1 (by omega)
        rw [debt_step,he]
        simp only [Edge.debtChange]
        omega
    · rintro (h | ⟨ho,_⟩)
      · exact Or.inl h.symm
      · exact Or.inr ho
  | @one x xs g he hd =>
    have hn : ¬ PositiveH E k := by
      rintro ⟨j,_,hj⟩; rw [he] at hj; cases hj
    simp only [hn,and_false,false_or]
    obtain ⟨ht, _, _, ho⟩ := (floors_cons_iff E x ys).mp hf
    have hm' : mass ys + 1 = debt E k := by simpa [mass,hd,add_comm] using hm
    have hnext : debt E (k+1) = mass ys := by
      rw [debt_step,he]; simp only [Edge.debtChange]; omega
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨(hl y.origin).mp ⟨y,by simp [hy],rfl⟩,?_⟩
      rw [hnext]
      exact floor_lt_mass ht hy
    · rintro ⟨hop,hlt⟩
      obtain ⟨y,hy,hyu⟩ := (hl u).mpr hop
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · rw [← hyu,ho,hnext] at hlt
        omega
      · exact ⟨y,hy,hyu⟩
  | @many x xs g he hd =>
    have hn : ¬ PositiveH E k := by
      rintro ⟨j,_,hj⟩; rw [he] at hj; cases hj
    simp only [hn,and_false,false_or]
    obtain ⟨ht, _, hh, ho⟩ := (floors_cons_iff E x xs).mp hf
    have hm' : (x.debt : ℤ) + mass xs = debt E k := hm
    have hnext : debt E (k+1) = (x.debt : ℤ) + mass xs - 1 := by
      rw [debt_step,he]; simp only [Edge.debtChange]; omega
    have hnmem : (∃ y ∈ (⟨x.origin,x.debt-1⟩::xs : List Entry),y.origin=u) ↔
        ∃ y ∈ x::xs,y.origin=u := by simp
    rw [hnmem,hl u]
    constructor
    · intro hop
      refine ⟨hop,?_⟩
      obtain ⟨y,hy,hyu⟩ := (hl u).mpr hop
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · rw [← hyu,ho,hnext]; omega
      · have hlt := floor_lt_mass ht hy
        rw [← hyu,hnext]
        omega
    · exact And.left

def RawTrace (E : ℕ → Edge) (n : ℕ) (f : ℕ → List Entry) : Prop :=
  f 0 = [] ∧ ∀ k, k < n → RawStep E k (f k) (f (k+1))

theorem trace_invariants {E : ℕ → Edge} {n k : ℕ} {f : ℕ → List Entry}
    (ht : RawTrace E n f) (hk : k ≤ n) :
    Floors E (f k) ∧ mass (f k) = debt E k ∧ Lives E k (f k) := by
  induction k with
  | zero =>
    rw [ht.1]
    refine ⟨Floors.nil,by simp [mass,debt,walk],?_⟩
    intro u
    simp [Open]
  | succ k ih =>
    obtain ⟨hf,hm,hl⟩ := ih (by omega)
    have hr := ht.2 k (by omega)
    obtain ⟨hf',hm'⟩ := raw_preserves_floors hr hf hm
    exact ⟨hf',hm',raw_preserves_lives hr hf hm hl⟩

theorem raw_next_exists {E : ℕ → Edge} {k : ℕ} {xs : List Entry}
    (hf : Floors E xs) (hm : mass xs = debt E k)
    (hp : Vertical E k → 0 < debt E k) : ∃ ys, RawStep E k xs ys := by
  cases he : E k with
  | H g =>
    cases g with
    | zero => exact ⟨xs,RawStep.hz he⟩
    | succ g => exact ⟨⟨k,g+1⟩::xs,RawStep.hp he⟩
  | V g =>
    have hd := hp ⟨g,he⟩
    cases xs with
    | nil => simp [mass] at hm; omega
    | cons x xs =>
      have hpos := ((floors_cons_iff E x xs).mp hf).2.1
      by_cases h : x.debt=1
      · exact ⟨xs,RawStep.one he h⟩
      · exact ⟨⟨x.origin,x.debt-1⟩::xs,RawStep.many he (by omega)⟩

theorem extend_trace {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (ht : RawTrace E n f) {ys : List Entry} (hr : RawStep E n (f n) ys) :
    ∃ g, RawTrace E (n+1) g := by
  let g := fun k => if k=n+1 then ys else f k
  refine ⟨g,?_,?_⟩
  · simpa [g] using ht.1
  · intro k hk
    by_cases h : k=n
    · subst k
      simpa [g] using hr
    · have hkn : k<n := by omega
      have h1 : k≠n+1 := by omega
      have h2 : k+1≠n+1 := by omega
      simpa [g,h1,h2,h] using ht.2 k hkn

theorem trace_exists (E : ℕ → Edge) (n : ℕ)
    (hp : ∀ k, k<n → Vertical E k → 0 < debt E k) :
    ∃ f, RawTrace E n f := by
  induction n with
  | zero => exact ⟨fun _ => [],rfl,by intro k hk; omega⟩
  | succ n ih =>
    obtain ⟨f,ht⟩ := ih (by intro k hk; exact hp k (by omega))
    obtain ⟨hf,hm,_⟩ := trace_invariants ht (le_refl n)
    obtain ⟨ys,hr⟩ := raw_next_exists hf hm (hp n (by omega))
    exact extend_trace ht hr

theorem root_trace_exists {E : ℕ → Edge} {n : ℕ} (hr : RootComponent E n) :
    ∃ f, RawTrace E n f := by
  apply trace_exists
  intro k hk hv
  by_cases h : k=0
  · subst k
    obtain ⟨g,_,he⟩ := hr.2.1
    obtain ⟨j,hj⟩ := hv
    rw [he] at hj
    cases hj
  · exact hr.2.2.2 k (by omega) hk

def eraseState (E : ℕ → Edge) (k : ℕ) (xs : List Entry) : State :=
  ⟨balance E k,xs.map fun x => ⟨x.debt,balance E (x.origin+1)⟩⟩

def Guarded (E : ℕ → Edge) (n : ℕ) (f : ℕ → List Entry) : Prop :=
  ∀ k, 1 ≤ k → k < n →
    step (eraseState E k (f k)) (E k) = some (eraseState E (k+1) (f (k+1)))

theorem raw_step_correct {E : ℕ → Edge} {k : ℕ} {xs ys : List Entry}
    (hr : RawStep E k xs ys) (hne : xs ≠ [])
    (hb : ∀ x zs, xs=x::zs → Vertical E k →
      balance E (x.origin+1) ≤ balance E (k+1)) :
    step (eraseState E k xs) (E k) = some (eraseState E (k+1) ys) := by
  cases hr with
  | hz he =>
    cases xs with
    | nil => contradiction
    | cons x xs => simp [eraseState,step,he,balance_step,Edge.credit]
  | @hp xs g he =>
    cases xs with
    | nil => contradiction
    | cons x xs => simp [eraseState,step,he,balance_step,Edge.credit]
  | @one x xs g he hd =>
    have hbound := hb x ys rfl ⟨g,he⟩
    rw [balance_step E k,he] at hbound
    simp only [Edge.credit] at hbound
    simp [eraseState,step,he,hd,hbound,balance_step E k,Edge.credit,sub_eq_add_neg]
  | @many x xs g he hd =>
    have hbound := hb x xs rfl ⟨g,he⟩
    rw [balance_step E k,he] at hbound
    simp only [Edge.credit] at hbound
    have hpos : 0<x.debt := by omega
    have hnot : x.debt≠1 := by omega
    simp [eraseState,step,he,hpos,hnot,hbound,balance_step E k,Edge.credit,sub_eq_add_neg]

theorem baselines_imply_guarded {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (hr : RootComponent E n) (ht : RawTrace E n f) (hb : ShadowBaselines E n) :
    Guarded E n f := by
  intro k hk hkn
  obtain ⟨_,hm,hl⟩ := trace_invariants ht (by omega : k ≤ n)
  have hne : f k ≠ [] := by
    intro he
    rw [he] at hm
    have hpos := hr.2.2.2 k (by omega) hkn
    simp [mass] at hm
    omega
  apply raw_step_correct (ht.2 k hkn) hne
  intro x xs he hv
  have ho := (hl x.origin).mp ⟨x,by simp [he],rfl⟩
  exact hb x.origin k ho.1 hkn ho.2.1 hv ho.2.2

def Ordered (s : State) : Prop :=
  s.stack.Pairwise (fun x y => y.baseline ≤ x.baseline)

def Bounded (s : State) : Prop := ∀ x ∈ s.stack, x.baseline ≤ s.balance

theorem step_invariants {s t : State} {e : Edge}
    (ho : Ordered s) (hb : Bounded s) (hs : step s e = some t) :
    Ordered t ∧ Bounded t ∧ ∀ x ∈ s.stack, x.baseline ≤ t.balance := by
  cases s with
  | mk b xs =>
    cases xs with
    | nil => simp [step] at hs
    | cons x xs =>
      have ho' := List.pairwise_cons.mp ho
      have hall : ∀ y ∈ x::xs, y.baseline ≤ b := hb
      cases e with
      | H g =>
        simp only [step] at hs
        cases hs
        have hold : ∀ y ∈ x::xs, y.baseline ≤ b+1 := by
          intro y hy
          have := hall y hy
          omega
        by_cases hg : g=0
        · simp only [Ordered,Bounded,ite_eq_left hg]
          exact ⟨ho,hold,hold⟩
        · simp only [Ordered,Bounded,ite_eq_right hg]
          refine ⟨?_,?_,hold⟩
          · exact List.pairwise_cons.mpr ⟨hold,ho⟩
          · intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact le_refl _
            · exact hold y (List.mem_cons.mpr hy)
      | V g =>
        simp only [step] at hs
        split at hs
        next h =>
          cases hs
          have hold : ∀ y ∈ x::xs, y.baseline ≤ b-(g:ℤ) := by
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact h.2
            · exact le_trans (ho'.1 y hy) h.2
          by_cases hd : x.debt=1
          · simp only [Ordered,Bounded,ite_eq_left hd]
            exact ⟨ho'.2,fun y hy => hold y (by simp [hy]),hold⟩
          · simp only [Ordered,Bounded,ite_eq_right hd]
            refine ⟨?_,?_,hold⟩
            · exact List.pairwise_cons.mpr ⟨ho'.1,ho'.2⟩
            · intro y hy
              simp only [List.mem_cons] at hy
              rcases hy with rfl | hy
              · exact h.2
              · exact hold y (by simp [hy])
        next h => contradiction

theorem trace_first {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (hr : RootComponent E n) (ht : RawTrace E n f) :
    ∃ g, E 0 = .H (g+1) ∧ f 1 = [⟨0,g+1⟩] := by
  have hs := ht.2 0 hr.1
  rw [ht.1] at hs
  change RawStep E 0 [] (f 1) at hs
  generalize hys : f 1 = ys at hs ⊢
  cases hs with
  | hz he =>
    obtain ⟨g,hg,hgE⟩ := hr.2.1
    rw [he] at hgE
    cases hgE
    omega
  | @hp xs g he => exact ⟨g,he,rfl⟩

theorem guarded_state_invariants {E : ℕ → Edge} {n k : ℕ} {f : ℕ → List Entry}
    (hr : RootComponent E n) (ht : RawTrace E n f) (hg : Guarded E n f)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    Ordered (eraseState E k (f k)) ∧ Bounded (eraseState E k (f k)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : k=0
    · subst k
      obtain ⟨g,_,he⟩ := trace_first hr ht
      simp [eraseState,he,Ordered,Bounded]
    · obtain ⟨ho,hb⟩ := ih (by omega) (by omega)
      have hs := step_invariants ho hb (hg k (by omega) (by omega))
      exact ⟨hs.1,hs.2.1⟩

theorem guarded_implies_baselines {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (hr : RootComponent E n) (ht : RawTrace E n f) (hg : Guarded E n f) :
    ShadowBaselines E n := by
  intro u v huv hvn hu _ ha
  obtain ⟨_,_,hl⟩ := trace_invariants ht (by omega : v ≤ n)
  obtain ⟨x,hx,hxu⟩ := (hl u).mpr ⟨huv,hu,ha⟩
  obtain ⟨ho,hb⟩ := guarded_state_invariants hr ht hg (by omega : 1 ≤ v) (by omega)
  have hs := step_invariants ho hb (hg v (by omega) hvn)
  have hm : (⟨x.debt,balance E (x.origin+1)⟩ : Node) ∈ (eraseState E v (f v)).stack :=
    List.mem_map.mpr ⟨x,hx,rfl⟩
  have hh := hs.2.2 _ hm
  simpa [eraseState,hxu] using hh

/-- The cyclic witness condition is equivalent to the actual `step` tests
on the debt parse of a complete horizontal-shadow component. -/
theorem compatibility_iff_guarded {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (hr : RootComponent E n) (ht : RawTrace E n f) :
    CyclicCompatible E n ↔ Guarded E n f := by
  rw [cyclic_iff_shadow_baselines hr]
  exact ⟨baselines_imply_guarded hr ht,guarded_implies_baselines hr ht⟩

/-- No existence of a parse is assumed: it follows from the component's
strictly positive proper debt prefixes and zero final debt. -/
theorem component_compatibility {E : ℕ → Edge} {n : ℕ} (hr : RootComponent E n) :
    CyclicCompatible E n ↔ ∃ f, RawTrace E n f ∧ Guarded E n f := by
  constructor
  · intro hc
    obtain ⟨f,ht⟩ := root_trace_exists hr
    exact ⟨f,ht,(compatibility_iff_guarded hr ht).mp hc⟩
  · rintro ⟨f,ht,hg⟩
    exact (compatibility_iff_guarded hr ht).mpr hg

theorem trace_final_empty {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (hr : RootComponent E n) (ht : RawTrace E n f) : f n = [] := by
  obtain ⟨hf,hm,_⟩ := trace_invariants ht (le_refl n)
  rw [hr.2.2.1] at hm
  cases he : f n with
  | nil => rfl
  | cons x xs =>
    rw [he] at hf hm
    have hp := ((floors_cons_iff E x xs).mp hf).2.1
    have hn := mass_nonneg xs
    change (x.debt : ℤ) + mass xs = 0 at hm
    omega

theorem trace_root_open {E : ℕ → Edge} {n k : ℕ} {f : ℕ → List Entry}
    (hr : RootComponent E n) (ht : RawTrace E n f) (hk : 0 < k) (hkn : k < n) :
    ∃ x ∈ f k, x.origin=0 := by
  have hl := (trace_invariants ht (by omega : k ≤ n)).2.2
  apply (hl 0).mpr
  refine ⟨hk,hr.2.1,?_⟩
  intro j hj hjk
  have hp := hr.2.2.2 j hj (by omega)
  simpa [debt,walk] using hp

end KroneckerShadow
