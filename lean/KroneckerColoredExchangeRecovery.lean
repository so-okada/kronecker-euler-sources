import KroneckerRightColoredRecovery

/- Original module: KroneckerRepairGrade -/
section
/-! The explicit minimal grade repair when a debt baseline is raised. -/
set_option autoImplicit false
namespace KroneckerRepairGrade

def repairGrade (h : ℕ) (b β : ℤ) : ℕ := min h (b-β).toNat

theorem repair_grade_le (h : ℕ) (b β : ℤ) : repairGrade h b β≤h := Nat.min_le_left _ _

theorem repair_grade_guard (h : ℕ) (b β : ℤ) (hb : β≤b) :
    β≤b-(repairGrade h b β : ℤ) := by
  have hk := Nat.min_le_right h (b-β).toNat
  have hc : ((b-β).toNat : ℤ)=b-β := Int.toNat_of_nonneg (by omega)
  unfold repairGrade
  omega

theorem repair_grade_balance (h : ℕ) (b β : ℤ) :
    b-(repairGrade h b β : ℤ)=(b-(h : ℤ))+(h-repairGrade h b β : ℕ) := by
  have hk := repair_grade_le h b β
  omega

end KroneckerRepairGrade
end

/- Original module: KroneckerMarkedBaselineRepair -/
section
/-! Follow a raised marked baseline until its debt unit is consumed; repair that edge only. -/
set_option autoImplicit false
namespace KroneckerMarkedBaselineRepair
open KroneckerStack KroneckerDebtUnits KroneckerUnitBalanceRaise
open KroneckerUnitSingletonSimulation KroneckerMarkedDebtIndex KroneckerVerticalRepair
open KroneckerRepairGrade

theorem marked_baseline_repair {es : List Edge} {pre tail : List ℤ} {a β b c root : ℤ}
    (ht : tail≠[]) (hb : β≤b) (hp : ∀ x∈pre, β≤x)
    (he : unitExecute es ⟨b,pre++a::tail⟩=some ⟨c,[root]⟩) :
    ∃ es' j h k, markedIndex pre.length es=some j ∧ RepairAt j es es' h k ∧
      unitExecute es' ⟨b,pre++β::tail⟩=some ⟨c+(h-k : ℕ),[root]⟩ := by
  induction es generalizing pre b with
  | nil =>
    simp only [unitExecute,Option.some.injEq,UnitState.mk.injEq] at he
    have hl := congrArg List.length he.2
    have htlen : 0<tail.length := List.length_pos_iff.mpr ht
    simp only [List.length_append,List.length_cons,List.length_nil] at hl
    omega
  | cons e es ih =>
    cases e with
    | H g =>
      have hs : unitStep ⟨b,pre++a::tail⟩ (.H g)=
          some ⟨b+1,List.replicate g (b+1)++(pre++a::tail)⟩ := by
        cases pre <;> rfl
      have hu : unitExecute es ⟨b+1,(List.replicate g (b+1)++pre)++a::tail⟩=
          some ⟨c,[root]⟩ := by simpa [unitExecute,hs,List.append_assoc] using he
      have hp' : ∀ x∈List.replicate g (b+1)++pre, β≤x := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have hx' := (List.mem_replicate.mp hx).2; omega
        · exact hp x hx
      obtain ⟨ys,j,h,k,hj,hr,hy⟩ := ih (by omega) hp' hu
      refine ⟨.H g::ys,j+1,h,k,?_,.there (.H g) hr,?_⟩
      · simpa [markedIndex] using congrArg (Option.map Nat.succ) hj
      · have hs' : unitStep ⟨b,pre++β::tail⟩ (.H g)=
            some ⟨b+1,List.replicate g (b+1)++(pre++β::tail)⟩ := by
          cases pre <;> rfl
        simpa [unitExecute,hs',List.append_assoc] using hy
    | V h =>
      cases pre with
      | nil =>
        have hs : a≤b-(h : ℤ) := by
          by_contra hn
          simp [unitExecute,unitStep,hn] at he
        have hu : unitExecute es ⟨b-(h : ℤ),tail⟩=some ⟨c,[root]⟩ := by
          simpa [unitExecute,unitStep,hs] using he
        let k := repairGrade h b β
        have hk : k≤h := repair_grade_le h b β
        have hguard : β≤b-(k : ℤ) := repair_grade_guard h b β hb
        have hy := execute_raised_singleton hu (h-k : ℕ) (by positivity)
        refine ⟨.V k::es,0,h,k,rfl,.here es h k hk,?_⟩
        simp only [unitExecute,unitStep,List.nil_append,ite_eq_left hguard,Option.bind_some]
        convert hy using 1
        simp [raiseBalance,k,repair_grade_balance]
      | cons z zs =>
        have hs : z≤b-(h : ℤ) := by
          by_contra hn
          simp [unitExecute,unitStep,hn] at he
        have hu : unitExecute es ⟨b-(h : ℤ),zs++a::tail⟩=some ⟨c,[root]⟩ := by
          simpa [unitExecute,unitStep,hs] using he
        have hb' : β≤b-(h : ℤ) := le_trans (hp z (by simp)) hs
        obtain ⟨ys,j,h',k,hj,hr,hy⟩ := ih hb' (fun x hx => hp x (by simp [hx])) hu
        refine ⟨.V h::ys,j+1,h',k,?_,.there (.V h) hr,?_⟩
        · simpa [markedIndex] using congrArg (Option.map Nat.succ) hj
        · simpa [unitExecute,unitStep,hs] using hy

end KroneckerMarkedBaselineRepair
end

/- Original module: KroneckerPositiveRightExchange -/
section
/-! The nonlocal adjacent exchange: one displaced debt unit, one later vertical repair. -/
set_option autoImplicit false
namespace KroneckerPositiveRightExchange
open KroneckerStack KroneckerDebtUnits KroneckerUnitOrderBounds
open KroneckerMarkedDebtIndex KroneckerVerticalRepair KroneckerMarkedBaselineRepair

theorem positive_right {es : List Edge} {tail : List ℤ} {a b c root : ℤ} {g h : ℕ}
    (ht : tail≠[]) (ho : OrderedBounded ⟨b,a::tail⟩)
    (he : unitExecute (.H (g+1)::.V h::es) ⟨b,a::tail⟩=some ⟨c,[root]⟩) :
    h=0 ∧ ∃ es' j q k, markedIndex g es=some j ∧ RepairAt j es es' q k ∧
      unitExecute (.V 0::.H (g+1)::es') ⟨b,a::tail⟩=some ⟨c+(q-k : ℕ),[root]⟩ := by
  have hz : h=0 := by
    by_contra hn
    have hh : ¬ b+1≤b+1-(h : ℤ) := by omega
    simp [unitExecute,unitStep,List.replicate_succ,hh] at he
  subst h
  have hu : unitExecute es ⟨b+1,List.replicate g (b+1)++a::tail⟩=
      some ⟨c,[root]⟩ := by
    simpa [unitExecute,unitStep,List.replicate_succ] using he
  obtain ⟨es',j,q,k,hj,hr,hy⟩ := marked_baseline_repair ht le_rfl
    (fun x hx => (List.mem_replicate.mp hx).2.ge) hu
  have ha : a≤b := ho.2 a (by simp)
  refine ⟨rfl,es',j,q,k,by simpa using hj,hr,?_⟩
  cases tail with
  | nil => contradiction
  | cons z zs =>
    simpa [unitExecute,unitStep,ha,List.replicate_succ',List.append_assoc] using hy

end KroneckerPositiveRightExchange
end

/- Original module: KroneckerPositiveLeftExchange -/
section
/-! Moving a positive horizontal edge left weakens the translated debt stack. -/
set_option autoImplicit false
namespace KroneckerPositiveLeftExchange
open KroneckerStack KroneckerDebtUnits KroneckerUnitShift KroneckerUnitStepWeakening
open KroneckerUnitBalanceRaise KroneckerUnitSingletonSimulation KroneckerUnitExecutionBottom

theorem positive_left {es : List Edge} {tail : List ℤ} {a b c root : ℤ} {g h : ℕ}
    (he : unitExecute (.V h::.H (g+1)::es) ⟨b,a::tail⟩=some ⟨c,[root]⟩) :
    unitExecute (.H (g+1)::.V 0::es) ⟨b,a::tail⟩=some ⟨c+(h : ℤ),[root]⟩ := by
  have ha : a≤b-(h : ℤ) := by
    by_contra hn
    simp [unitExecute,unitStep,hn] at he
  have ht : tail≠[] := by
    intro hn
    simp [unitExecute,unitStep,ha,hn] at he
  have hu : unitExecute es ⟨b-(h : ℤ)+1,List.replicate (g+1) (b-(h : ℤ)+1)++tail⟩=
      some ⟨c,[root]⟩ := by
    cases tail with
    | nil => contradiction
    | cons z zs => simpa [unitExecute,unitStep,ha] using he
  have hbalance : b-(h : ℤ)+1+(h : ℤ)=b+1 := by omega
  have hw : Weaker ⟨b+1,List.replicate g (b+1)++a::tail⟩
      (shift (h : ℤ) ⟨b-(h : ℤ)+1,List.replicate (g+1) (b-(h : ℤ)+1)++tail⟩) := by
    constructor
    · exact hbalance.symm
    · simp only [shift,List.map_append,List.map_replicate,hbalance,List.replicate_succ',List.append_assoc]
      exact List.rel_append (List.forall₂_refl _)
        (.cons (by dsimp; omega) (baselines_le_shift tail (h : ℤ) (by positivity)))
  have hb := (unit_execute_bottom hu (by simp)).symm
  have htb : tail.getLast?=some root := by
    simpa [List.getLast?_append,ht] using hb
  have hb' : (List.replicate g (b+1)++a::tail).getLast?=some root := by
    simp [List.getLast?_append,List.getLast?_cons,htb]
  have hy := execute_weaker_singleton hw (unit_execute_shift hu (h : ℤ)) hb'
  simpa [unitExecute,unitStep,List.replicate_succ] using hy

end KroneckerPositiveLeftExchange
end

/- Original module: KroneckerZeroHorizontalExchange -/
section
/-! The two grade-zero adjacent exchanges, including the exact compensation. -/
set_option autoImplicit false
namespace KroneckerZeroHorizontalExchange
open KroneckerStack KroneckerDebtUnits KroneckerUnitOrderBounds
open KroneckerUnitNonemptyExecution KroneckerUnitBalanceRaise KroneckerUnitSingletonSimulation

theorem zero_right {es : List Edge} {tail : List ℤ} {a b c root : ℤ} {h : ℕ}
    (ho : OrderedBounded ⟨b,a::tail⟩)
    (he : unitExecute (.H 0::.V h::es) ⟨b,a::tail⟩=some ⟨c,[root]⟩) :
    unitExecute (.V (h-1)::.H 0::es) ⟨b,a::tail⟩=
      some ⟨c+(h-(h-1) : ℕ),[root]⟩ := by
  have ha : a≤b+1-(h : ℤ) := by
    by_contra hn
    simp [unitExecute,unitStep,hn] at he
  have hu : unitExecute es ⟨b+1-(h : ℤ),tail⟩=some ⟨c,[root]⟩ := by
    simpa [unitExecute,unitStep,ha] using he
  have ht : tail≠[] := execute_nonempty_source hu (by simp)
  have ha' : a≤b-(h-1 : ℕ) := by
    have hab : a≤b := ho.2 a (by simp)
    omega
  have hy := execute_raised_singleton hu (h-(h-1) : ℕ) (by positivity)
  have hb : b+1-(h : ℤ)+(h-(h-1) : ℕ)=b-(h-1 : ℕ)+1 := by omega
  change unitExecute es ⟨b+1-(h : ℤ)+(h-(h-1) : ℕ),tail⟩=_ at hy
  rw [hb] at hy
  cases tail with
  | nil => contradiction
  | cons z zs => simpa [unitExecute,unitStep,ha'] using hy

theorem zero_left {es : List Edge} {tail : List ℤ} {a b c root : ℤ} {h : ℕ}
    (he : unitExecute (.V h::.H 0::es) ⟨b,a::tail⟩=some ⟨c,[root]⟩) :
    unitExecute (.H 0::.V h::es) ⟨b,a::tail⟩=some ⟨c,[root]⟩ := by
  have ha : a≤b-(h : ℤ) := by
    by_contra hn
    simp [unitExecute,unitStep,hn] at he
  have ht : tail≠[] := by
    intro hn
    simp [unitExecute,unitStep,ha,hn] at he
  have ha' : a≤b+1-(h : ℤ) := by omega
  have hb : b-(h : ℤ)+1=b+1-(h : ℤ) := by omega
  cases tail with
  | nil => contradiction
  | cons z zs => simpa [unitExecute,unitStep,ha,ha',hb] using he

end KroneckerZeroHorizontalExchange
end

/- Original module: KroneckerRightColoredExecution -/
section
/-! Construct an actual colored right exchange from a successful protected suffix. -/
set_option autoImplicit false
namespace KroneckerRightColoredExecution
open KroneckerStack KroneckerDebtUnits KroneckerUnitOrderBounds
open KroneckerColoring KroneckerColoredShell KroneckerColoredEdges KroneckerColoredRepairLift
open KroneckerRightColoredChange KroneckerPositiveRightExchange KroneckerZeroHorizontalExchange

theorem right_colored_execute {m : ℕ} {x y : Palette m} {es : List (CEdge m)}
    {a b c root : ℤ} {tail : List ℤ} (ht : tail≠[]) (ho : OrderedBounded ⟨b,a::tail⟩)
    (he : unitExecute (.H (grade x)::.V (grade y)::coloredWord es) ⟨b,a::tail⟩=
      some ⟨c,[root]⟩) :
    ∃ q ds p d, RightChange x y es q ds p d ∧
      unitExecute (.V (grade q)::.H (grade x)::coloredWord ds) ⟨b,a::tail⟩=
        some ⟨c+(d : ℤ),[root]⟩ := by
  cases hx : grade x with
  | zero =>
    let q := regrade y (grade y-1) (le_trans (Nat.sub_le _ _) (grade_le y))
    refine ⟨q,es,y,grade y-(grade y-1),.zero y q es hx
      (regrade_grade _ _ _) (regrade_respects _ _ _),?_⟩
    have hh := zero_right ho (by simpa [hx] using he)
    simpa [q,hx] using hh
  | succ n =>
    obtain ⟨hy,ds',j,h,k,hi,hr,hout⟩ := positive_right ht ho (by simpa [hx] using he)
    obtain ⟨ds,p,q,hc,hds,hp,hq⟩ := repair_lift hr es rfl
    refine ⟨y,ds,p,grade p-grade q,.positive hx hy hi hc,?_⟩
    simpa [hx,hy,hds,hp,hq] using hout

end KroneckerRightColoredExecution
end

/- Original module: KroneckerLeftColoredExecution -/
section
/-! The colored left exchange retains the entire suffix and needs only the crossed palette for recovery. -/
set_option autoImplicit false
namespace KroneckerLeftColoredExecution
open KroneckerStack KroneckerDebtUnits KroneckerColoring KroneckerColoredEdges
open KroneckerPositiveLeftExchange KroneckerZeroHorizontalExchange

inductive LeftChange {m : ℕ} (x y : Palette m) : Palette m → ℕ → Prop
  | zero (hx : grade x=0) : LeftChange x y y 0
  | positive (hx : 0<grade x) : LeftChange x y (zeroColor m) (grade y)

theorem left_change_budget {m d : ℕ} {x y q : Palette m} (h : LeftChange x y q d) : d≤m := by
  cases h with
  | zero => exact Nat.zero_le _
  | positive => exact grade_le y

theorem left_colored_execute {m : ℕ} {x y : Palette m} {es : List (CEdge m)}
    {a b c root : ℤ} {tail : List ℤ}
    (he : unitExecute (.V (grade y)::.H (grade x)::coloredWord es) ⟨b,a::tail⟩=
      some ⟨c,[root]⟩) :
    ∃ q d, LeftChange x y q d ∧
      unitExecute (.H (grade x)::.V (grade q)::coloredWord es) ⟨b,a::tail⟩=
        some ⟨c+(d : ℤ),[root]⟩ := by
  cases hx : grade x with
  | zero =>
    refine ⟨y,0,.zero hx,?_⟩
    have hh := zero_left (by simpa [hx] using he)
    simpa [hx] using hh
  | succ n =>
    refine ⟨zeroColor m,grade y,.positive (by omega),?_⟩
    have hh := positive_left (by simpa [hx] using he)
    simpa [hx] using hh

end KroneckerLeftColoredExecution
end

/- Original module: KroneckerProtectedNodePrefix -/
section
/-! An interior position of an old connected node has a parent above the added root. -/
set_option autoImplicit false
namespace KroneckerProtectedNodePrefix
open KroneckerStack KroneckerDebtUnits KroneckerUnitNodeDictionary KroneckerUnitConcatenation
open KroneckerUnitOuterStack KroneckerUnitShift KroneckerUnitNonemptyExecution
open KroneckerUnitOrderBounds KroneckerUnitInvariantExecution

theorem protected_node_prefix {r c : ℕ} {pre rest : List Edge}
    (hn : NodeRun (.H (r+1)::(pre++rest)) c) (hne : rest≠[]) :
    ∃ b a tail, tail≠[] ∧ OrderedBounded ⟨b,a::tail⟩ ∧
      unitExecute (.H (r+1)::pre) ⟨1,[1]⟩=some ⟨b,a::tail⟩ ∧
      unitExecute rest ⟨b,a::tail⟩=some ⟨(c : ℤ)+2,[1]⟩ := by
  have hr : unitExecute (pre++rest) ⟨1,List.replicate (r+1) 1⟩=
      some ⟨(c : ℤ)+1,[]⟩ := by
    obtain ⟨q,es,he,hq⟩ := node_to_units hn
    have hh := List.cons.inj he
    have hg := Edge.H.inj hh.1
    rw [← hg,← hh.2] at hq
    exact hq
  obtain ⟨⟨b,xs⟩,hp,hs⟩ := unit_execute_split hr
  have hx : xs≠[] := by
    intro hx
    subst xs
    exact hne (execute_from_empty rest b _ hs).1
  have hp' := unit_execute_outer (unit_execute_shift hp 1) [1]
  have hs' := unit_execute_outer (unit_execute_shift hs 1) [1]
  cases xs with
  | nil => contradiction
  | cons a tail =>
    have hprefix : unitExecute (.H (r+1)::pre) ⟨1,[1]⟩=
        some ⟨b+1,(a+1)::(tail.map (fun x => x+1)++[1])⟩ := by
      simpa [unitExecute,unitStep,shift,outer] using hp'
    refine ⟨b+1,a+1,tail.map (fun x => x+1)++[1],by simp,?_,hprefix,?_⟩
    · exact unit_execute_ordered (by simpa using replicate_ordered 1 1) hprefix
    · simpa [shift,outer,add_assoc] using hs'

end KroneckerProtectedNodePrefix
end

/- Original module: KroneckerColoredNodeLoops -/
section
/-! Both colored exchange directions inside an actual connected node, protected by one outer unit. -/
set_option autoImplicit false
namespace KroneckerColoredNodeLoops
open KroneckerStack KroneckerDebtUnits KroneckerUnitConcatenation KroneckerProtectedNodePrefix
open KroneckerColoring KroneckerColoredEdges KroneckerRightColoredChange
open KroneckerRightColoredExecution KroneckerLeftColoredExecution

theorem node_head_positive {h c : ℕ} {es : List Edge} (hn : NodeRun (.H h::es) c) : 0<h := by
  obtain ⟨g,rest,he,_⟩ := hn
  have hh := Edge.H.inj (List.cons.inj he).1
  omega

theorem right_node_loop {m c : ℕ} {z x y : Palette m} {pre es : List (CEdge m)}
    (hn : NodeRun (coloredWord ((true,z)::(pre++(true,x)::(false,y)::es))) c) :
    ∃ q ds p d, RightChange x y es q ds p d ∧
      unitExecute (coloredWord ((true,z)::(pre++(false,q)::(true,x)::ds))) ⟨1,[1]⟩=
        some ⟨((c+d : ℕ) : ℤ)+2,[1]⟩ := by
  have hz : 0<grade z := node_head_positive hn
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : grade z≠0)
  have hn' : NodeRun (.H (r+1)::(coloredWord pre++(.H (grade x)::.V (grade y)::coloredWord es))) c := by
    simpa [coloredWord,uncolor,paint,hr] using hn
  obtain ⟨b,a,tail,ht,ho,hpre,hrest⟩ := protected_node_prefix hn' (by simp)
  obtain ⟨q,ds,p,d,hc,hout⟩ := right_colored_execute ht ho hrest
  refine ⟨q,ds,p,d,hc,?_⟩
  have hp : unitExecute (coloredWord ((true,z)::pre)) ⟨1,[1]⟩=some ⟨b,a::tail⟩ := by
    simpa [coloredWord,uncolor,paint,hr] using hpre
  have hjoin := unit_execute_append (coloredWord ((true,z)::pre))
    (.V (grade q)::.H (grade x)::coloredWord ds) ⟨1,[1]⟩
  rw [hp,Option.bind_some,hout] at hjoin
  simpa [coloredWord,uncolor,paint,add_assoc,add_comm,add_left_comm] using hjoin

theorem left_node_loop {m c : ℕ} {z x y : Palette m} {pre es : List (CEdge m)}
    (hn : NodeRun (coloredWord ((true,z)::(pre++(false,y)::(true,x)::es))) c) :
    ∃ q d, LeftChange x y q d ∧
      unitExecute (coloredWord ((true,z)::(pre++(true,x)::(false,q)::es))) ⟨1,[1]⟩=
        some ⟨((c+d : ℕ) : ℤ)+2,[1]⟩ := by
  have hz : 0<grade z := node_head_positive hn
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : grade z≠0)
  have hn' : NodeRun (.H (r+1)::(coloredWord pre++(.V (grade y)::.H (grade x)::coloredWord es))) c := by
    simpa [coloredWord,uncolor,paint,hr] using hn
  obtain ⟨b,a,tail,_,_,hpre,hrest⟩ := protected_node_prefix hn' (by simp)
  obtain ⟨q,d,hc,hout⟩ := left_colored_execute hrest
  refine ⟨q,d,hc,?_⟩
  have hp : unitExecute (coloredWord ((true,z)::pre)) ⟨1,[1]⟩=some ⟨b,a::tail⟩ := by
    simpa [coloredWord,uncolor,paint,hr] using hpre
  have hjoin := unit_execute_append (coloredWord ((true,z)::pre))
    (.H (grade x)::.V (grade q)::coloredWord es) ⟨1,[1]⟩
  rw [hp,Option.bind_some,hout] at hjoin
  simpa [coloredWord,uncolor,paint,add_assoc,add_comm,add_left_comm] using hjoin

end KroneckerColoredNodeLoops
end

/- Original module: KroneckerEdgeShell -/
section
/-! The preserving shell on full colored edges, with fixed new palettes. -/
set_option autoImplicit false
namespace KroneckerEdgeShell
open KroneckerStack KroneckerColoring KroneckerColoredShell KroneckerColoredEdges
open KroneckerUnitPreservingLoopShell KroneckerDebtUnits

def edgePrefix (m u : ℕ) (hu : u+1≤m) : List (CEdge m) :=
  (true,fixedColor m (u+1) hu)::List.replicate u (false,zeroColor m)

def edgeSuffix (m v : ℕ) (hv : v-1≤m) (hm : 2≤m) : List (CEdge m) :=
  (true,fixedColor m (v-1) hv)::(List.replicate (v-1) (false,zeroColor m)++[(false,fixedColor m 2 hm)])

def edgeShell {m : ℕ} (u v : ℕ) (hu : u+1≤m) (hv : v-1≤m) (hm : 2≤m)
    (es : List (CEdge m)) : List (CEdge m) :=
  edgePrefix m u hu++(es++edgeSuffix m v hv hm)

theorem edgeShell_word {m : ℕ} (u v : ℕ) (hu : u+1≤m) (hv : v-1≤m) (hm : 2≤m)
    (es : List (CEdge m)) :
    coloredWord (edgeShell u v hu hv hm es)=loopShell u (v-1) (coloredWord es) := by
  simp [edgeShell,edgePrefix,edgeSuffix,coloredWord,uncolor,paint,loopShell,List.append_assoc]

theorem edgeShell_shape {m : ℕ} (u v : ℕ) (hu : u+1≤m) (hv : v-1≤m) (hm : 2≤m)
    (hpos : 1≤v) (es : List (CEdge m)) :
    coloredShape (edgeShell u v hu hv hm es)=shellPath u v (coloredShape es) := by
  have hrep : List.replicate (v-1) false++[false]=List.replicate v false := by
    rw [← List.replicate_succ']
    congr 1
    omega
  simp [edgeShell,edgePrefix,edgeSuffix,coloredShape,shellPath,runShape,hrep]

theorem edgeShell_connected {m c : ℕ} (u v : ℕ) (hu : u+1≤m) (hv : v-1≤m) (hm : 2≤m)
    (es : List (CEdge m))
    (he : unitExecute (coloredWord es) ⟨1,[1]⟩=some ⟨(c : ℤ)+2,[1]⟩) :
    Connected m (coloredWord (edgeShell u v hu hv hm es)) c := by
  apply node_connected
  · rw [edgeShell_word]
    exact loop_shell_node u (v-1) c (coloredWord es) he
  · exact coloredWord_grades _

end KroneckerEdgeShell
end

/- Original module: KroneckerEdgeShellRecovery -/
section
/-! Removing the fixed shell recovers the complete colored interior. -/
set_option autoImplicit false
namespace KroneckerEdgeShellRecovery
open KroneckerColoredEdges KroneckerEdgeShell

def unshell {m : ℕ} (u n : ℕ) (es : List (CEdge m)) : List (CEdge m) :=
  (es.drop (u+1)).take n

theorem unshell_edgeShell {m : ℕ} (u v : ℕ) (hu : u+1≤m) (hv : v-1≤m) (hm : 2≤m)
    (es : List (CEdge m)) : unshell u es.length (edgeShell u v hu hv hm es)=es := by
  have hp : (edgePrefix m u hu).length=u+1 := by simp [edgePrefix]
  simp only [unshell,edgeShell,← hp,List.drop_left,List.take_left]

theorem edgeShell_injective {m : ℕ} (u v : ℕ) (hu : u+1≤m) (hv : v-1≤m) (hm : 2≤m) :
    Function.Injective (edgeShell u v hu hv hm) := by
  intro xs ys h
  simpa [edgeShell] using h

end KroneckerEdgeShellRecovery
end

/- Original module: KroneckerColoredExchangeRelation -/
section
/-! Exchange relations at a prescribed edge position, retaining the full colored prefix. -/
set_option autoImplicit false
namespace KroneckerColoredExchangeRelation
open KroneckerColoring KroneckerColoredEdges KroneckerRightColoredChange KroneckerLeftColoredExecution

inductive Exchange {m : ℕ} : Bool → ℕ → List (CEdge m) → List (CEdge m) → Palette m → ℕ → Prop
  | right (pre : List (CEdge m)) {x y q p : Palette m} {es ds : List (CEdge m)} {d : ℕ}
      (hc : RightChange x y es q ds p d) :
      Exchange true pre.length (pre++(true,x)::(false,y)::es)
        (pre++(false,q)::(true,x)::ds) p d
  | left (pre : List (CEdge m)) {x y q : Palette m} (es : List (CEdge m)) {d : ℕ}
      (hc : LeftChange x y q d) :
      Exchange false pre.length (pre++(false,y)::(true,x)::es)
        (pre++(true,x)::(false,q)::es) y d

theorem exchange_budget {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) : d≤m := by
  cases he with
  | right _ hc => exact right_change_budget hc
  | left _ _ hc => exact left_change_budget hc

theorem exchange_length {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) : xs.length=ys.length := by
  cases he with
  | right pre hc =>
    have hl := congrArg List.length (right_change_shape hc)
    simpa [coloredShape] using hl
  | left => simp

end KroneckerColoredExchangeRelation
end

/- Original module: KroneckerColoredExchangeRecovery -/
section
/-! Decode a full colored adjacent exchange from its output and one palette. -/
set_option autoImplicit false
namespace KroneckerColoredExchangeRecovery
open KroneckerColoring KroneckerColoredEdges KroneckerRightColoredRecovery
open KroneckerColoredExchangeRelation

def decodeAt {m : ℕ} (right : Bool) (i : ℕ) (ys : List (CEdge m)) (code : Palette m) : List (CEdge m) :=
  match ys.drop i with
  | e::f::ds =>
    if right then
      let old := decodeRight f.2 ds code
      ys.take i++(true,f.2)::(false,old.1)::old.2
    else ys.take i++(false,code)::(true,e.2)::ds
  | _ => []

theorem exchange_recovery {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) : decodeAt right i ys p=xs := by
  cases he with
  | right pre hc =>
    simp [decodeAt,right_recovery hc]
  | left pre es hc => simp [decodeAt]

theorem exchange_input_unique {m i d d' : ℕ} {right : Bool}
    {xs xs' ys : List (CEdge m)} {p : Palette m}
    (h : Exchange right i xs ys p d) (h' : Exchange right i xs' ys p d') : xs=xs' :=
  (exchange_recovery h).symm.trans (exchange_recovery h')

end KroneckerColoredExchangeRecovery
end
