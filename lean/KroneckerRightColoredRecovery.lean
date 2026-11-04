import KroneckerVerticalRepair
import KroneckerColoredShell
import KroneckerPaletteRecolor

/- Original module: KroneckerVerticalRepairBounds -/
section
/-! A single vertical repair retains the legal alphabet and has a bounded loss. -/
set_option autoImplicit false
namespace KroneckerVerticalRepairBounds
open KroneckerStack KroneckerMarkedDebtIndex KroneckerVerticalRepair





end KroneckerVerticalRepairBounds
end

/- Original module: KroneckerColoredEdges -/
section
/-! Ordered colored edges, retaining the orientation and the full binomial palette. -/
set_option autoImplicit false
namespace KroneckerColoredEdges
open KroneckerStack KroneckerColoring

abbrev CEdge (m : ℕ) := Bool × Palette m

def uncolor {m : ℕ} (e : CEdge m) : Edge := paint e.1 e.2
def coloredWord {m : ℕ} (es : List (CEdge m)) : List Edge := es.map uncolor
def coloredShape {m : ℕ} (es : List (CEdge m)) : List Bool := es.map Prod.fst

theorem uncolor_vertical {m h : ℕ} (e : CEdge m) :
    uncolor e=.V h ↔ e.1=false ∧ grade e.2=h := by
  rcases e with ⟨b,p⟩
  cases b <;> simp [uncolor,paint]

theorem uncolor_horizontal {m h : ℕ} (e : CEdge m) :
    uncolor e=.H h ↔ e.1=true ∧ grade e.2=h := by
  rcases e with ⟨b,p⟩
  cases b <;> simp [uncolor,paint]

theorem coloredWord_grades {m : ℕ} (es : List (CEdge m)) :
    ∀ e∈coloredWord es, e.grade≤m := by
  intro e he
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp he
  simpa only [uncolor,paint_grade] using grade_le p.2


end KroneckerColoredEdges
end

/- Original module: KroneckerColoredRepair -/
section
/-! One vertical palette change, with exact recovery of every original color. -/
set_option autoImplicit false
namespace KroneckerColoredRepair
open KroneckerStack KroneckerColoring KroneckerColoredEdges KroneckerVerticalRepair

inductive ColoredRepairAt {m : ℕ} : ℕ → List (CEdge m) → List (CEdge m) → Palette m → Palette m → Prop
  | here (es : List (CEdge m)) (p q : Palette m) (hq : grade q≤grade p)
      (hc : RespectsRecol p q) :
      ColoredRepairAt 0 ((false,p)::es) ((false,q)::es) p q
  | there {j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m} (e : CEdge m)
      (hr : ColoredRepairAt j xs ys p q) :
      ColoredRepairAt (j+1) (e::xs) (e::ys) p q

theorem colored_repair_recovery {m j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m}
    (hr : ColoredRepairAt j xs ys p q) : ys.set j (false,p)=xs := by
  induction hr with
  | here => rfl
  | there e _ ih => exact congrArg (List.cons e) ih

theorem colored_repair_word {m j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m}
    (hr : ColoredRepairAt j xs ys p q) :
    RepairAt j (coloredWord xs) (coloredWord ys) (grade p) (grade q) := by
  induction hr with
  | here es p q hq _ => exact .here (coloredWord es) (grade p) (grade q) hq
  | there e _ ih => exact .there (uncolor e) ih

theorem colored_repair_shape {m j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m}
    (hr : ColoredRepairAt j xs ys p q) : coloredShape xs=coloredShape ys := by
  induction hr with
  | here => rfl
  | there e _ ih => exact congrArg (List.cons e.1) ih

end KroneckerColoredRepair
end

/- Original module: KroneckerColoredRepairLift -/
section
/-! Lift the actual uncolored repair to palettes, retaining all other colors. -/
set_option autoImplicit false
namespace KroneckerColoredRepairLift
open KroneckerStack KroneckerColoring KroneckerColoredShell KroneckerColoredEdges
open KroneckerVerticalRepair KroneckerColoredRepair

theorem repair_lift {m j h k : ℕ} {xs ys : List Edge}
    (hr : RepairAt j xs ys h k) (cs : List (CEdge m)) (hc : coloredWord cs=xs) :
    ∃ ds p q, ColoredRepairAt j cs ds p q ∧ coloredWord ds=ys ∧ grade p=h ∧ grade q=k := by
  induction hr generalizing cs with
  | here es h k hk =>
    cases cs with
    | nil => simp [coloredWord] at hc
    | cons e cs =>
      have hh := List.cons.inj hc
      have hp := (uncolor_vertical e).mp hh.1
      rcases e with ⟨b,p⟩
      dsimp only at hp
      obtain ⟨rfl,hp⟩ := hp
      have hkm : k≤m := le_trans hk (hp ▸ grade_le p)
      let q := regrade p k hkm
      refine ⟨(false,q)::cs,p,q,.here cs p q (by simpa [q,hp] using hk)
        (regrade_respects p k hkm),?_,hp,regrade_grade p k hkm⟩
      change .V (grade q)::coloredWord cs=.V k::es
      rw [show grade q = k from regrade_grade p k hkm]
      exact congrArg (List.cons (.V k)) hh.2
  | @there j h k xs ys e hr ih =>
    cases cs with
    | nil => simp [coloredWord] at hc
    | cons p cs =>
      have hh := List.cons.inj hc
      obtain ⟨ds,q,r,hrep,hds,hq,hrg⟩ := ih cs hh.2
      refine ⟨p::ds,q,r,.there p hrep,?_,hq,hrg⟩
      change uncolor p::coloredWord ds=e::ys
      rw [hh.1,hds]

end KroneckerColoredRepairLift
end

/- Original module: KroneckerRightColoredChange -/
section
/-! The two possible palette changes for a right exchange, with a one-palette recovery code. -/
set_option autoImplicit false
namespace KroneckerRightColoredChange
open KroneckerColoring KroneckerColoredEdges KroneckerColoredRepair
open KroneckerMarkedDebtIndex KroneckerVerticalRepair KroneckerVerticalRepairBounds

inductive RightChange {m : ℕ} (x : Palette m) :
    Palette m → List (CEdge m) → Palette m → List (CEdge m) → Palette m → ℕ → Prop
  | zero (y q : Palette m) (es : List (CEdge m)) (hx : grade x=0)
      (hq : grade q=grade y-1) (hc : RespectsRecol y q) :
      RightChange x y es q es y (grade y-(grade y-1))
  | positive {y p q : Palette m} {es ds : List (CEdge m)} {n j : ℕ}
      (hx : grade x=n+1) (hy : grade y=0)
      (hi : markedIndex n (coloredWord es)=some j) (hr : ColoredRepairAt j es ds p q) :
      RightChange x y es y ds p (grade p-grade q)

theorem right_change_shape {m d : ℕ} {x y q p : Palette m} {es ds : List (CEdge m)}
    (hr : RightChange x y es q ds p d) : coloredShape es=coloredShape ds := by
  cases hr with
  | zero => rfl
  | positive _ _ _ hc => exact colored_repair_shape hc

theorem right_change_budget {m d : ℕ} {x y q p : Palette m} {es ds : List (CEdge m)}
    (hr : RightChange x y es q ds p d) : d≤m := by
  cases hr <;> exact le_trans (Nat.sub_le _ _) (grade_le _)

end KroneckerRightColoredChange
end

/- Original module: KroneckerRightColoredRecovery -/
section
/-! Recover the repair position from output horizontal grades, without coding its index. -/
set_option autoImplicit false
namespace KroneckerRightColoredRecovery
open KroneckerColoring KroneckerColoredEdges KroneckerColoredRepair KroneckerRightColoredChange
open KroneckerMarkedDebtIndex KroneckerVerticalRepair

def decodeRight {m : ℕ} (x : Palette m) (ds : List (CEdge m)) (code : Palette m) :
    Palette m × List (CEdge m) :=
  if grade x=0 then (code,ds)
  else (zeroColor m,ds.set ((markedIndex (grade x-1) (coloredWord ds)).getD 0) (false,code))

theorem right_recovery {m d : ℕ} {x y q p : Palette m} {es ds : List (CEdge m)}
    (hr : RightChange x y es q ds p d) : decodeRight x ds p=(y,es) := by
  cases hr with
  | zero q es hx hq _ => simp [decodeRight,hx]
  | @positive p q es ds n j hx hy hi hc =>
    have hx0 : grade x≠0 := by omega
    have hn : grade x-1=n := by omega
    have hindex : markedIndex n (coloredWord ds)=some j := by
      rw [← markedIndex_invariant (repair_sameDebt (colored_repair_word hc)) n]
      exact hi
    simp only [decodeRight,ite_eq_right hx0,hn,hindex,Option.getD_some,colored_repair_recovery hc]
    rw [grade_zero_unique hy]

theorem right_input_unique {m d d' : ℕ} {x y y' q p : Palette m}
    {es es' ds : List (CEdge m)}
    (h : RightChange x y es q ds p d) (h' : RightChange x y' es' q ds p d') :
    y=y' ∧ es=es' := by
  exact Prod.mk.inj ((right_recovery h).symm.trans (right_recovery h'))

end KroneckerRightColoredRecovery
end
