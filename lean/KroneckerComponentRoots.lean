import KroneckerShadow

/- Original module: KroneckerComponent -/
section
/-!
The stack/compatibility dictionary on one complete shadow component.
The finite Euler/frame identity is a separate, still unformalized result.
-/
set_option autoImplicit false
namespace KroneckerComponent
open KroneckerStack KroneckerCompatibility KroneckerShadow

def segment (E : ℕ → Edge) : ℕ → ℕ → List Edge
  | _, 0 => []
  | s, len+1 => E s :: segment E (s+1) len

theorem segment_head (E : ℕ → Edge) {n : ℕ} (hn : 0<n) :
    segment E 0 n = E 0 :: segment E 1 (n-1) := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem execute_segment (E : ℕ → Edge) (S : ℕ → State) (s len : ℕ)
    (hs : ∀ k, s ≤ k → k < s+len → step (S k) (E k) = some (S (k+1))) :
    execute (segment E s len) (S s) = some (S (s+len)) := by
  induction len generalizing s with
  | zero => simp [segment,execute]
  | succ len ih =>
    simp only [segment,execute]
    rw [hs s (le_refl _) (by omega)]
    simp only [Option.bind_some]
    have ht := ih (s+1) (by intro k hk hk'; exact hs k (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem vertical_step_bound {b : ℤ} {x : Node} {xs : List Node} {g : ℕ} {t : State}
    (hs : step ⟨b,x::xs⟩ (.V g) = some t) : x.baseline ≤ b-(g:ℤ) := by
  simp only [step] at hs
  split at hs
  next h => exact h.2
  next h => contradiction

theorem raw_step_agrees {E : ℕ → Edge} {k : ℕ} {xs ys : List Entry} {t : State}
    (hr : RawStep E k xs ys) (hs : step (eraseState E k xs) (E k) = some t) :
    t = eraseState E (k+1) ys := by
  have hne : xs≠[] := by
    intro h
    simp [h,eraseState,step] at hs
  have hb : ∀ x zs, xs=x::zs → Vertical E k →
      balance E (x.origin+1) ≤ balance E (k+1) := by
    rintro x zs rfl ⟨g,he⟩
    have hv := vertical_step_bound (by simpa [eraseState,he] using hs)
    rw [balance_step E k,he]
    simpa [Edge.credit,sub_eq_add_neg] using hv
  have hh := raw_step_correct hr hne hb
  exact Option.some.inj (hs.symm.trans hh)

theorem execution_gives_guards {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (ht : RawTrace E n f) (s len : ℕ) (hbound : s+len ≤ n) {t : State}
    (he : execute (segment E s len) (eraseState E s (f s)) = some t) :
    t = eraseState E (s+len) (f (s+len)) ∧
      ∀ k, s ≤ k → k < s+len → step (eraseState E k (f k)) (E k) =
        some (eraseState E (k+1) (f (k+1))) := by
  induction len generalizing s t with
  | zero =>
    simp only [segment,execute,Option.some.injEq] at he
    refine ⟨by simpa using he.symm,?_⟩
    intro k hk hk'
    omega
  | succ len ih =>
    simp only [segment,execute] at he
    cases hs : step (eraseState E s (f s)) (E s) with
    | none => simp [hs] at he
    | some u =>
      have hu := raw_step_agrees (ht.2 s (by omega)) hs
      subst u
      simp only [hs,Option.bind_some] at he
      obtain ⟨hf,hguards⟩ := ih (s+1) (by omega) he
      refine ⟨by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf,?_⟩
      intro k hk hk'
      by_cases h : k=s
      · simpa [h] using hs
      · exact hguards k (by omega) (by omega)

theorem root_length {E : ℕ → Edge} {n : ℕ} (hr : RootComponent E n) : 2 ≤ n := by
  have hn := hr.1
  by_contra h
  have he : n=1 := by omega
  obtain ⟨g,hg,hgE⟩ := hr.2.1
  have hd := hr.2.2.1
  rw [he,debt_step,hgE] at hd
  simp [debt,walk,Edge.debtChange] at hd
  omega

theorem guarded_final_balance {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (hr : RootComponent E n) (ht : RawTrace E n f) (hg : Guarded E n f) :
    1 ≤ balance E n := by
  have hn := root_length hr
  obtain ⟨x,hx,hxo⟩ := trace_root_open hr ht (by omega : 0<n-1) (by omega)
  obtain ⟨ho,hb⟩ := guarded_state_invariants hr ht hg (by omega : 1≤n-1) (by omega)
  have hs := step_invariants ho hb (hg (n-1) (by omega) (by omega))
  have hm : (⟨x.debt,balance E (x.origin+1)⟩ : Node) ∈
      (eraseState E (n-1) (f (n-1))).stack := List.mem_map.mpr ⟨x,hx,rfl⟩
  have hh := hs.2.2 _ hm
  obtain ⟨g,_,he⟩ := hr.2.1
  have hend : n-1+1=n := by omega
  change balance E (x.origin+1) ≤ balance E (n-1+1) at hh
  rw [hxo,hend] at hh
  have hfirst : balance E 1 = 1 := by simp [balance,walk,he,Edge.credit]
  simpa only [Nat.zero_add,hfirst] using hh

theorem initial_state {E : ℕ → Edge} {g : ℕ} {f : ℕ → List Entry}
    (he : E 0 = .H (g+1)) (hf : f 1 = [⟨0,g+1⟩]) :
    eraseState E 1 (f 1) = ⟨1,[⟨g+1,1⟩]⟩ := by
  simp [eraseState,hf,balance,walk,he,Edge.credit]

theorem compatible_node {E : ℕ → Edge} {n : ℕ} (hr : RootComponent E n)
    (hc : CyclicCompatible E n) : ∃ c, NodeRun (segment E 0 n) c := by
  obtain ⟨f,ht,hg⟩ := (component_compatibility hr).mp hc
  obtain ⟨g,he,hf⟩ := trace_first hr ht
  have hb := guarded_final_balance hr ht hg
  let c := (balance E n - 1).toNat
  have hc' : (c:ℤ)+1=balance E n := by dsimp [c]; omega
  have hlast : eraseState E n (f n) = ⟨(c:ℤ)+1,[]⟩ := by
    simp [eraseState,trace_final_empty hr ht,hc']
  have hs := execute_segment E (fun k => eraseState E k (f k)) 1 (n-1)
    (by intro k hk hkn; exact hg k hk (by omega))
  have hend : 1+(n-1)=n := by have := hr.1; omega
  rw [hend,initial_state he hf,hlast] at hs
  refine ⟨c,g,segment E 1 (n-1),?_,hs⟩
  rw [segment_head E hr.1,he]

theorem node_compatible {E : ℕ → Edge} {n c : ℕ} (hr : RootComponent E n)
    (hn : NodeRun (segment E 0 n) c) : CyclicCompatible E n := by
  obtain ⟨f,ht⟩ := root_trace_exists hr
  obtain ⟨g,he,hf⟩ := trace_first hr ht
  obtain ⟨j,rest,hword,hex⟩ := hn
  rw [segment_head E hr.1,he] at hword
  have hparts := List.cons.inj hword
  have hj : g=j := by simpa using hparts.1
  subst j
  rw [← hparts.2] at hex
  have hs : execute (segment E 1 (n-1)) (eraseState E 1 (f 1)) =
      some ⟨(c:ℤ)+1,[]⟩ := by simpa [initial_state he hf] using hex
  have hbounds := (execution_gives_guards ht 1 (n-1) (by have := hr.1; omega) hs).2
  apply (compatibility_iff_guarded hr ht).mpr
  intro k hk hkn
  exact hbounds k hk (by have := hr.1; omega)

/-- The component criterion used in Lemma 2.24, for the literal stack implementation, retaining both excluded
witness endpoints. Root closure and a nonnegative surplus follow from the
component hypotheses and compatibility. -/
theorem compatibility_iff_node {E : ℕ → Edge} {n : ℕ} (hr : RootComponent E n) :
    CyclicCompatible E n ↔ ∃ c, NodeRun (segment E 0 n) c :=
  ⟨compatible_node hr,fun ⟨_,hn⟩ => node_compatible hr hn⟩

theorem compatibility_iff_connected {E : ℕ → Edge} {n m : ℕ}
    (hr : RootComponent E n) :
    (CyclicCompatible E n ∧ ∀ e ∈ segment E 0 n, e.grade ≤ m) ↔
      ∃ c, Connected m (segment E 0 n) c := by
  constructor
  · rintro ⟨hc,hg⟩
    obtain ⟨c,hn⟩ := compatible_node hr hc
    exact ⟨c,connected_iff.mpr ⟨hn,hg⟩⟩
  · rintro ⟨c,hc⟩
    obtain ⟨hn,hg⟩ := connected_iff.mp hc
    exact ⟨node_compatible hr hn,hg⟩

theorem positive_inside {E : ℕ → Edge} {n N i : ℕ}
    (hz : ∀ j, n≤j → j<N → (E j).grade=0) (hi : i<N)
    (hp : PositiveH E i ∨ PositiveV E i) : i<n := by
  by_contra h
  have hg := hz i (by omega) hi
  rcases hp with ⟨g,hg',he⟩ | ⟨g,hg',he⟩ <;>
    simp [he,Edge.grade] at hg <;> omega

/-- Extending a complete component by grade-zero edges preserves cyclic
compatibility, even though the cyclic interval has a different length. -/
theorem zero_extension_compatible {E : ℕ → Edge} {n N : ℕ}
    (hr : RootComponent E n) (hn : n≤N)
    (hz : ∀ j, n≤j → j<N → (E j).grade=0) :
    CyclicCompatible E N ↔ CyclicCompatible E n := by
  constructor
  · intro hc
    apply (cyclic_iff_linear hr).mpr
    intro u v huv hvn hu hv
    simpa [ite_eq_left (by omega : u≤v)] using
      hc u v (by omega) (by omega) hu hv
  · intro hc u v huN hvN hu hv
    have hun := positive_inside hz huN (Or.inl hu)
    have hvn := positive_inside hz hvN (Or.inr hv)
    by_cases h : u≤v
    · simpa [ite_eq_left h] using hc u v hun hvn hu hv
    · simp only [ite_eq_right h]
      left
      obtain ⟨e,hue,hen,hh,hd⟩ := wrapping_witness (v:=0) hr hun hu
      exact ⟨e,hue,by omega,hh,hd⟩

end KroneckerComponent
end

/- Original module: KroneckerComponentRoots -/
section
/-! An accepted connected word itself supplies the component hypotheses. -/
set_option autoImplicit false
namespace KroneckerComponentRoots
open KroneckerStack KroneckerCompatibility KroneckerShadow KroneckerComponent

def PositiveDebts (s : State) : Prop := ∀ x ∈ s.stack, 0<x.debt

theorem step_positive_debts {s t : State} {e : Edge}
    (hp : PositiveDebts s) (hs : step s e=some t) : PositiveDebts t := by
  cases s with
  | mk b xs =>
    cases xs with
    | nil => simp [step] at hs
    | cons x xs =>
      have hx : 0<x.debt := hp x (by simp)
      have ht : ∀ y ∈ xs,0<y.debt := fun y hy => hp y (by simp [hy])
      cases e with
      | H g =>
        simp only [step] at hs
        cases hs
        by_cases h : g=0
        · simpa only [PositiveDebts,ite_eq_left h] using hp
        · simp only [PositiveDebts,ite_eq_right h,List.mem_cons,forall_eq_or_imp]
          exact ⟨by omega,hx,ht⟩
      | V g =>
        simp only [step] at hs
        split at hs
        next h =>
          cases hs
          by_cases hd : x.debt=1
          · simpa only [PositiveDebts,ite_eq_left hd] using ht
          · simp only [PositiveDebts,ite_eq_right hd,List.mem_cons,forall_eq_or_imp]
            exact ⟨by omega,ht⟩
        next h => contradiction

theorem execute_positive_debts {es : List Edge} {s t : State}
    (hp : PositiveDebts s) (he : execute es s=some t) : PositiveDebts t := by
  induction es generalizing s with
  | nil => simp only [execute,Option.some.injEq] at he; simpa [← he] using hp
  | cons e es ih =>
    cases hs : step s e with
    | none => simp [execute,hs] at he
    | some u =>
      have hu : execute es u=some t := by simpa [execute,hs] using he
      exact ih (step_positive_debts hp hs) hu

theorem debt_total_positive {s : State} (hp : PositiveDebts s) (hne : s.stack≠[]) :
    0<debtTotal s := by
  cases s with
  | mk b xs =>
    cases xs with
    | nil => contradiction
    | cons x xs =>
      have hx : 0<x.debt := hp x (by simp)
      have ht : 0 ≤ (xs.map fun y => (y.debt:ℤ)).sum := by
        apply List.sum_nonneg
        intro z hz
        obtain ⟨y,_,rfl⟩ := List.mem_map.mp hz
        positivity
      simp only [debtTotal,List.map_cons,List.sum_cons]
      omega

theorem segment_append (E : ℕ → Edge) (s a b : ℕ) :
    KroneckerComponent.segment E s (a+b) = KroneckerComponent.segment E s a ++ KroneckerComponent.segment E (s+a) b := by
  induction a generalizing s with
  | zero => simp [KroneckerComponent.segment]
  | succ a ih =>
    rw [Nat.succ_add]
    change E s :: KroneckerComponent.segment E (s+1) (a+b) =
      (E s :: KroneckerComponent.segment E (s+1) a) ++
        KroneckerComponent.segment E (s + a.succ) b
    rw [ih (s+1)]
    simp only [List.cons_append]
    have hs : s + 1 + a = s + a.succ := by omega
    rw [hs]

theorem segment_debt (E : ℕ → Edge) (s len : ℕ) :
    ((KroneckerComponent.segment E s len).map Edge.debtChange).sum = debt E (s+len)-debt E s := by
  induction len generalizing s with
  | zero => simp [KroneckerComponent.segment]
  | succ len ih =>
    simp only [KroneckerComponent.segment,List.map_cons,List.sum_cons,ih]
    have hidx : s+1+len=s+(len+1) := by omega
    rw [hidx]
    have hs := debt_step E s
    omega

theorem execution_segment_nonempty {E : ℕ → Edge} {s len : ℕ} {u v : State}
    (hlen : 0<len) (he : execute (KroneckerComponent.segment E s len) u=some v) : u.stack≠[] := by
  intro h
  cases len with
  | zero => omega
  | succ len => simp [KroneckerComponent.segment,execute,step,h] at he

/-- Root positivity, first closure, and positive proper debt prefixes follow
from the literal acceptance rules. They need not be postulated separately. -/
theorem node_root_component {E : ℕ → Edge} {n c : ℕ}
    (hn : NodeRun (KroneckerComponent.segment E 0 n) c) : RootComponent E n := by
  have htotal := node_debt_balance hn
  have hpos : 0<n := by
    by_contra h
    have hz : n=0 := by omega
    obtain ⟨g,rest,hword,_⟩ := hn
    simp [hz,KroneckerComponent.segment] at hword
  obtain ⟨g,rest,hword,hex⟩ := hn
  rw [segment_head E hpos] at hword
  obtain ⟨he,hrest⟩ := List.cons.inj hword
  rw [← hrest] at hex
  have hfirst : debt E 1 = ((g+1:ℕ):ℤ) := by simp [debt,walk,he,Edge.debtChange]
  refine ⟨hpos,⟨g+1,by omega,he⟩,?_,?_⟩
  · rw [segment_debt] at htotal
    simpa [debt,walk] using htotal
  · intro k hk hkn
    have hsplit := segment_append E 1 (k-1) (n-k)
    have hi : k-1+(n-k)=n-1 := by omega
    have hk' : 1+(k-1)=k := by omega
    rw [hi,hk'] at hsplit
    have hrun := hex
    rw [hsplit,execute_append] at hrun
    cases hs : execute (KroneckerComponent.segment E 1 (k-1)) ⟨1,[⟨g+1,1⟩]⟩ with
    | none => simp [hs] at hrun
    | some u =>
      have htail : execute (KroneckerComponent.segment E k (n-k)) u=some ⟨(c:ℤ)+1,[]⟩ := by
        simpa [hs] using hrun
      have hp : PositiveDebts u := execute_positive_debts (by simp [PositiveDebts]) hs
      have hmass := debt_total_positive hp (execution_segment_nonempty (by omega) htail)
      have hd := execute_debt hs
      rw [segment_debt,hk',hfirst] at hd
      have hinit : debtTotal ⟨1,[⟨g+1,1⟩]⟩ = ((g+1:ℕ):ℤ) := by simp [debtTotal]
      rw [hinit] at hd
      omega

/-- The complete finite dictionary, with no unproved component hypothesis
on a connected input word. Grade bounds are identical on both sides. -/
theorem full_component_dictionary (E : ℕ → Edge) (n m : ℕ) :
    (∃ c, Connected m (KroneckerComponent.segment E 0 n) c) ↔
      RootComponent E n ∧ CyclicCompatible E n ∧
        ∀ e ∈ KroneckerComponent.segment E 0 n,e.grade≤m := by
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨hn,hg⟩ := connected_iff.mp hc
    have hr := node_root_component hn
    exact ⟨hr,node_compatible hr hn,hg⟩
  · rintro ⟨hr,hc,hg⟩
    exact (compatibility_iff_connected hr).mp ⟨hc,hg⟩

end KroneckerComponentRoots
end
