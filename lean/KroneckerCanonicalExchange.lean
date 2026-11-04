import KroneckerWrappedLeftExistence

/-! Exact repair witnesses for the deterministic adjacent-exchange map. -/
set_option autoImplicit false
namespace KroneckerCanonicalExchange
open KroneckerStack KroneckerDebtUnits KroneckerMarkedDebtIndex
open KroneckerColoring KroneckerColoredEdges KroneckerColoredRepairLift
open KroneckerRightColoredChange KroneckerLeftColoredExecution
open KroneckerColoredExchangeRelation KroneckerEdgeShell KroneckerExchangePath

/-- Credit is additive along every successful unit execution. -/
theorem unit_execute_credit {es : List Edge} {s t : UnitState}
    (h : unitExecute es s = some t) : t.balance = s.balance + credit es := by
  induction es generalizing s with
  | nil =>
      simp only [unitExecute, Option.some.injEq] at h
      subst t
      simp [credit]
  | cons e es ih =>
    obtain ⟨w, hs, ht⟩ := Option.bind_eq_some_iff.mp h
    have hb : w.balance = s.balance + e.credit := by
      cases s with
      | mk b st =>
        cases st with
        | nil => simp [unitStep] at hs
        | cons a tail =>
          cases e with
          | H g => simp [unitStep] at hs; subst w; rfl
          | V g =>
              simp only [unitStep] at hs
              split at hs
              · cases hs; simp [Edge.credit]; omega
              · contradiction
    have ht' := ih ht
    simp only [credit, List.map_cons, List.sum_cons]
    change t.balance = s.balance + (e.credit + credit es)
    omega

def positiveDelta (n : ℕ) (es : List Edge) : ℕ :=
  let j := (markedIndex n es).getD 0
  let h := (es[j]?.getD (.V 0)).grade
  h - min h (credit (es.take j)).toNat

/-- The four formulas of the manuscript, at a zero-based pair position. -/
def repairDelta (right : Bool) (i : ℕ) (xs : List Edge) : ℕ :=
  let x := (xs[i]?.getD (.H 0)).grade
  let y := (xs[i+1]?.getD (.V 0)).grade
  if right then
    if x = 0 then y - (y-1) else positiveDelta (x-1) (xs.drop (i+2))
  else if y = 0 then 0 else x

theorem repairDelta_right (pre es : List Edge) (g h : ℕ) :
    repairDelta true pre.length (pre ++ .H g :: .V h :: es) =
      if g = 0 then h-(h-1) else positiveDelta (g-1) es := by
  simp [repairDelta, List.drop_append, List.drop_eq_nil_of_le (by omega : pre.length ≤ pre.length+2), Edge.grade]

theorem repairDelta_left (pre es : List Edge) (g h : ℕ) :
    repairDelta false pre.length (pre ++ .V h :: .H g :: es) =
      if g = 0 then 0 else h := by
  simp [repairDelta, Edge.grade]

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


theorem exact_delta {es ys : List Edge} {n j q k : ℕ} {b : ℤ} {xs : List ℤ}
    {w : UnitState} (hi : markedIndex n es = some j)
    (hr : KroneckerVerticalRepair.RepairAt j es ys q k)
    (hw : unitExecute (es.take j) ⟨b,xs⟩ = some w)
    (hd : ((q-k : ℕ) : ℤ) = (q : ℤ) - min (q : ℤ) (max (w.balance-b) 0)) :
    q-k = positiveDelta n es := by
  have hb : w.balance-b = credit (es.take j) := by
    have hh := unit_execute_credit hw
    dsimp at hh
    omega
  rw [hb] at hd
  have he := positive_reduction_formula q (credit (es.take j)) 0
  simp only [sub_zero] at he
  have hh : q-k = q-KroneckerRepairGrade.repairGrade q (credit (es.take j)) 0 := by
    omega
  simpa [positiveDelta, hi, KroneckerVerticalRepair.repair_original hr,
    KroneckerRepairGrade.repairGrade, Edge.grade] using hh

theorem right_colored_exact {m : ℕ} {x y : Palette m} {es : List (CEdge m)}
    {a b c root : ℤ} {tail : List ℤ} (ht : tail ≠ [])
    (ho : KroneckerUnitOrderBounds.OrderedBounded ⟨b,a::tail⟩)
    (he : unitExecute (.H (grade x) :: .V (grade y) :: coloredWord es) ⟨b,a::tail⟩ =
      some ⟨c,[root]⟩) :
    ∃ q ds p d, RightChange x y es q ds p d ∧
      unitExecute (.V (grade q) :: .H (grade x) :: coloredWord ds) ⟨b,a::tail⟩ =
        some ⟨c+(d : ℤ),[root]⟩ ∧
      d = if grade x = 0 then grade y-(grade y-1)
          else positiveDelta (grade x-1) (coloredWord es) := by
  cases hx : grade x with
  | zero =>
      let q := regrade y (grade y-1) (le_trans (Nat.sub_le _ _) (grade_le y))
      refine ⟨q,es,y,grade y-(grade y-1),.zero y q es hx
        (regrade_grade _ _ _) (regrade_respects _ _ _),?_,by simp⟩
      have hh := KroneckerZeroHorizontalExchange.zero_right ho (by simpa [hx] using he)
      simpa [q,hx] using hh
  | succ n =>
      obtain ⟨hy,ds',j,h,k,w,hi,hr,hw,hdelta,hout⟩ :=
        positive_right_exact ht ho (by simpa [hx] using he)
      have hd := exact_delta hi hr hw hdelta
      obtain ⟨ds,p,q,hc,hds,hp,hq⟩ := repair_lift hr es rfl
      refine ⟨y,ds,p,grade p-grade q,.positive hx hy hi hc,?_,?_⟩
      · simpa [hx,hy,hds,hp,hq] using hout
      · simpa [hx,hp,hq] using hd

theorem right_node_exact {m c : ℕ} {z x y : Palette m} {pre es : List (CEdge m)}
    (hn : NodeRun (coloredWord ((true,z)::(pre++(true,x)::(false,y)::es))) c) :
    ∃ q ds p d, RightChange x y es q ds p d ∧
      unitExecute (coloredWord ((true,z)::(pre++(false,q)::(true,x)::ds))) ⟨1,[1]⟩ =
        some ⟨((c+d : ℕ) : ℤ)+2,[1]⟩ ∧
      d = if grade x = 0 then grade y-(grade y-1)
          else positiveDelta (grade x-1) (coloredWord es) := by
  have hz : 0 < grade z := KroneckerColoredNodeLoops.node_head_positive hn
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : grade z ≠ 0)
  have hn' : NodeRun (.H (r+1)::(coloredWord pre++(.H (grade x)::.V (grade y)::coloredWord es))) c := by
    simpa [coloredWord,uncolor,paint,hr] using hn
  obtain ⟨b,a,tail,ht,ho,hpre,hrest⟩ :=
    KroneckerProtectedNodePrefix.protected_node_prefix hn' (by simp)
  obtain ⟨q,ds,p,d,hc,hout,hd⟩ := right_colored_exact ht ho hrest
  refine ⟨q,ds,p,d,hc,?_,hd⟩
  have hp : unitExecute (coloredWord ((true,z)::pre)) ⟨1,[1]⟩ = some ⟨b,a::tail⟩ := by
    simpa [coloredWord,uncolor,paint,hr] using hpre
  have hjoin := KroneckerUnitConcatenation.unit_execute_append (coloredWord ((true,z)::pre))
    (.V (grade q)::.H (grade x)::coloredWord ds) ⟨1,[1]⟩
  rw [hp,Option.bind_some,hout] at hjoin
  simpa [coloredWord,uncolor,paint,add_assoc,add_comm,add_left_comm] using hjoin

theorem wrapped_right_exact {m c : ℕ} (P Q : List Bool) (u v : ℕ)
    (hu : u+1 ≤ m) (hv : v-1 ≤ m) (hm : 2 ≤ m) (cs : List (CEdge m))
    (hshape : coloredShape cs = sourcePath true P Q) (hc : Connected m (coloredWord cs) c) :
    ∃ ds code d, Exchange true (P.length+1) cs ds code d ∧
      coloredShape ds = targetPath true P Q ∧
      Connected m (coloredWord (edgeShell u v hu hv hm ds)) (c+d) ∧
      d = repairDelta true (P.length+1) (coloredWord cs) := by
  obtain ⟨z,tail,rfl,ht⟩ := KroneckerColoredShapeSplit.colored_shape_cons hshape
  obtain ⟨pre,rest,hr,hpre,hrest⟩ := KroneckerColoredShapeSplit.colored_shape_append ht
  subst tail
  obtain ⟨x,rest',hr',hx⟩ := KroneckerColoredShapeSplit.colored_shape_cons hrest
  subst rest
  obtain ⟨y,es,hes,hy⟩ := KroneckerColoredShapeSplit.colored_shape_cons hx
  subst rest'
  obtain ⟨q,ds,p,d,hchange,hloop,hd⟩ := right_node_exact (connected_node hc)
  have hp : pre.length = P.length := by simpa [coloredShape] using congrArg List.length hpre
  refine ⟨(true,z)::(pre++(false,q)::(true,x)::ds),p,d,?_,?_,?_,?_⟩
  · simpa [hp] using Exchange.right ((true,z)::pre) hchange
  · have hds : coloredShape ds = Q := (right_change_shape hchange).symm.trans hy
    simp only [coloredShape,List.map_cons,List.map_append]
    change true::(coloredShape pre++false::true::coloredShape ds) = _
    rw [hpre,hds]
    rfl
  · exact edgeShell_connected u v hu hv hm _ hloop
  · have hh := repairDelta_right (coloredWord ((true,z)::pre)) (coloredWord es)
        (grade x) (grade y)
    simpa [coloredWord,uncolor,paint,hp] using hd.trans hh.symm

theorem left_delta {m i d : ℕ} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange false i xs ys p d) :
    d = repairDelta false i (coloredWord xs) := by
  cases he with
  | @left pre x y q es d hc =>
      have hh := repairDelta_left (coloredWord pre) (coloredWord es) (grade x) (grade p)
      have hl : (coloredWord pre).length = pre.length := by simp [coloredWord]
      simp only [hl] at hh
      cases hc with
      | zero hx => simpa [coloredWord,uncolor,paint,hx] using hh.symm
      | positive hx =>
          simpa [coloredWord,uncolor,paint,Nat.ne_of_gt hx] using hh.symm

/-- The target word before its single vertical repair. -/
def swapEdges (i : ℕ) (xs : List Edge) : List Edge :=
  xs.take i ++ ((xs.drop i).take 2).reverse ++ xs.drop (i+2)

theorem swapEdges_pair (pre es : List Edge) (x y : Edge) :
    swapEdges pre.length (pre ++ x::y::es) = pre ++ y::x::es := by
  simp [swapEdges,List.drop_append,
    List.drop_eq_nil_of_le (by omega : pre.length ≤ pre.length+2),List.append_assoc]

def repairPosition (right : Bool) (i : ℕ) (xs : List Edge) : ℕ :=
  if right then
    let g := (xs[i]?.getD (.H 0)).grade
    if g = 0 then i else i+2+(markedIndex (g-1) (xs.drop (i+2))).getD 0
  else i+1

def lower (d : ℕ) : Edge → Edge
  | .H g => .H g
  | .V g => .V (g-d)

def repairWord (right : Bool) (i : ℕ) (xs : List Edge) : List Edge :=
  (swapEdges i xs).modify (repairPosition right i xs) (lower (repairDelta right i xs))

theorem repairPosition_right (pre es : List Edge) (g h : ℕ) :
    repairPosition true pre.length (pre ++ .H g :: .V h :: es) =
      if g = 0 then pre.length else pre.length+2+(markedIndex (g-1) es).getD 0 := by
  simp [repairPosition,List.drop_append,
    List.drop_eq_nil_of_le (by omega : pre.length ≤ pre.length+2),Edge.grade]

theorem modify_append (pre es : List Edge) (j d : ℕ) :
    (pre ++ es).modify (pre.length+j) (lower d) = pre ++ es.modify j (lower d) := by
  induction pre with
  | nil => simp
  | cons e pre ih =>
      simpa only [List.cons_append,List.length_cons,Nat.succ_add,List.modify_succ_cons]
        using congrArg (List.cons e) ih

theorem repair_modify {xs ys : List Edge} {j h k : ℕ}
    (hr : KroneckerVerticalRepair.RepairAt j xs ys h k) :
    ys = xs.modify j (lower (h-k)) := by
  induction hr with
  | here es h k hk => simp [lower,Nat.sub_sub_self hk]
  | there e hr ih => simpa using congrArg (List.cons e) ih

/-- The exchange relation fixes all edge values once its reduction is fixed. -/
theorem exchange_word {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) :
    coloredWord ys = (swapEdges i (coloredWord xs)).modify
      (repairPosition right i (coloredWord xs)) (lower d) := by
  cases he with
  | right pre hc =>
      have hl : pre.length = (pre.map uncolor).length := by simp
      cases hc with
      | zero q es hx hq hcol =>
          simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true]
          rw [hl,swapEdges_pair (pre.map uncolor),repairPosition_right (pre.map uncolor)]
          simp only [hx, ↓reduceIte]
          rw [show (pre.map uncolor).length = (pre.map uncolor).length+0 by omega,modify_append]
          simp [lower,hq,Nat.sub_sub_self (Nat.sub_le (grade p) 1)]
      | @positive y q es ds n j hx hy hi hr =>
          have hm := repair_modify (KroneckerColoredRepair.colored_repair_word hr)
          simp only [coloredWord] at hi hm
          simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true]
          rw [hl,swapEdges_pair (pre.map uncolor),repairPosition_right (pre.map uncolor)]
          simp only [hx,Nat.add_sub_cancel,Nat.add_eq_zero_iff,one_ne_zero,and_false,
            ite_false,hi,Option.getD_some]
          rw [show (pre.map uncolor).length+2+j = (pre.map uncolor).length+(j+1+1) by omega,
            modify_append]
          simp only [List.modify_succ_cons]
          rw [hm]
  | @left pre x y q es d hc =>
      have hl : pre.length = (pre.map uncolor).length := by simp
      simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true]
      rw [hl,swapEdges_pair (pre.map uncolor)]
      simp only [repairPosition,Bool.false_eq_true,ite_false]
      rw [modify_append]
      cases hc with
      | zero hx => simp [lower]
      | positive hx => simp [lower]

theorem exchange_word_exact {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d)
    (hd : d = repairDelta right i (coloredWord xs)) :
    coloredWord ys = repairWord right i (coloredWord xs) := by
  rw [exchange_word he,hd]
  rfl

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


theorem positiveDelta_append {n j : ℕ} {es : List Edge}
    (hi : markedIndex n es = some j) (post : List Edge) :
    positiveDelta n (es ++ post) = positiveDelta n es := by
  obtain ⟨h,hh⟩ := markedIndex_vertical hi
  have hj : j < es.length := by
    by_contra hn
    have he : es[j]? = none := List.getElem?_eq_none (by omega)
    rw [he] at hh
    contradiction
  simp [positiveDelta,hi,markedIndex_append_of_some hi post,
    List.getElem?_append,hj,List.take_append,Nat.sub_eq_zero_of_le (Nat.le_of_lt hj)]

theorem coloredRepair_append {m j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m}
    (hr : KroneckerColoredRepair.ColoredRepairAt j xs ys p q) (post : List (CEdge m)) :
    KroneckerColoredRepair.ColoredRepairAt j (xs++post) (ys++post) p q := by
  induction hr with
  | here es p q hk hc => exact .here (es++post) p q hk hc
  | there e hr ih => exact .there e ih

theorem exchange_context {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) (pre post : List (CEdge m)) :
    Exchange right (pre.length+i) (pre++xs++post) (pre++ys++post) p d := by
  cases he with
  | right middle hc =>
      cases hc with
      | zero q es hx hq hcol =>
          rename_i x q es
          simpa [List.append_assoc] using
            Exchange.right (pre++middle) (RightChange.zero _ _ (es++post) hx hq hcol)
      | @positive y q es ds n j hx hy hi hr =>
          rename_i x y es ds
          have hi' : markedIndex n (coloredWord (es++post)) = some j := by
            simpa [coloredWord] using markedIndex_append_of_some hi (coloredWord post)
          simpa [List.append_assoc] using
            Exchange.right (pre++middle) (RightChange.positive hx hy hi' (coloredRepair_append hr post))
  | left middle es hc =>
      simpa [List.append_assoc] using Exchange.left (pre++middle) (es++post) hc

theorem repairDelta_context {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) (pre post : List (CEdge m)) :
    repairDelta right (pre.length+i) (coloredWord (pre++xs++post)) =
      repairDelta right i (coloredWord xs) := by
  cases he with
  | right middle hc =>
      have hl : pre.length+middle.length = (pre.map uncolor ++ middle.map uncolor).length := by simp
      have hm : middle.length = (middle.map uncolor).length := by simp
      cases hc with
      | zero q es hx hq hcol =>
          simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.cons_append]
          rw [←List.append_assoc]
          rw [hl,hm,repairDelta_right (pre.map uncolor ++ middle.map uncolor),repairDelta_right (middle.map uncolor)]
          simp [hx]
      | @positive y q es ds n j hx hy hi hr =>
          simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.cons_append]
          rw [←List.append_assoc]
          rw [hl,hm,repairDelta_right (pre.map uncolor ++ middle.map uncolor),repairDelta_right (middle.map uncolor)]
          simp only [hx,Nat.add_sub_cancel,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
          exact positiveDelta_append hi (coloredWord post)
  | left middle es hc =>
      have hl : pre.length+middle.length = (pre.map uncolor ++ middle.map uncolor).length := by simp
      have hm : middle.length = (middle.map uncolor).length := by simp
      simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
        Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.cons_append]
      rw [←List.append_assoc]
      rw [hl,hm,repairDelta_left (pre.map uncolor ++ middle.map uncolor),repairDelta_left (middle.map uncolor)]

end KroneckerCanonicalExchange

#print axioms KroneckerCanonicalExchange.wrapped_right_exact
#print axioms KroneckerCanonicalExchange.left_delta
