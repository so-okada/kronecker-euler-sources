import KroneckerCanonicalExchange

/-! The deterministic reduction stated using the full transported word and
its boundary balances, as in the manuscript. -/
set_option autoImplicit false
namespace KroneckerLiteralRepair
open KroneckerStack KroneckerDebtUnits KroneckerMarkedDebtIndex
open KroneckerColoring KroneckerColoredEdges KroneckerColoredExchangeRelation
open KroneckerCanonicalExchange

def literalDelta (right : Bool) (i : ℕ) (xs : List Edge) : ℕ :=
  let x := (xs[i]?.getD (.H 0)).grade
  let y := (xs[i+1]?.getD (.V 0)).grade
  if right then
    if x = 0 then y-(y-1)
    else
      let ys := swapEdges i xs
      let j := repairPosition right i xs
      let h := (ys[j]?.getD (.V 0)).grade
      h - min h (credit (ys.take j) - (credit (xs.take i)+1)).toNat
  else if y = 0 then 0 else x

theorem right_zero (pre es : List Edge) (h : ℕ) :
    literalDelta true pre.length (pre ++ .H 0 :: .V h :: es) = h-(h-1) := by
  simp [literalDelta,Edge.grade]

theorem left (pre es : List Edge) (g h : ℕ) :
    literalDelta false pre.length (pre ++ .V h :: .H g :: es) =
      if g = 0 then 0 else h := by
  simp [literalDelta,Edge.grade]

theorem right_positive (pre es : List Edge) (n j : ℕ)
    (hi : markedIndex n es = some j) :
    literalDelta true pre.length (pre ++ .H (n+1) :: .V 0 :: es) =
      positiveDelta n es := by
  unfold literalDelta
  simp only [List.getElem?_append_right (by omega : pre.length ≤ pre.length),
    Nat.sub_self,List.getElem?_cons_zero,Option.getD_some,Edge.grade]
  simp only [↓reduceIte]
  rw [swapEdges_pair,repairPosition_right]
  simp only [Nat.add_sub_cancel,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,hi,Option.getD_some]
  have hj : pre.length+2+j-pre.length = j+1+1 := by omega
  simp only [List.getElem?_append_right (by omega : pre.length ≤ pre.length+2+j),hj,
    List.getElem?_cons_succ,List.take_append]
  have htake : pre.take (pre.length+2+j) = pre := List.take_of_length_le (by omega)
  rw [htake]
  simp only [List.take_succ_cons,credit,List.map_append,List.sum_append,List.map_cons,
    List.sum_cons,Edge.credit,Int.ofNat_zero,neg_zero,zero_add]
  have hb : (pre.map Edge.credit).sum + (1+(es.take j |>.map Edge.credit).sum) -
      ((pre.map Edge.credit).sum+1) = (es.take j |>.map Edge.credit).sum := by omega
  simp only [List.take_length,Nat.sub_self,List.take_zero,List.map_nil,List.sum_nil,add_zero]
  rw [hb]
  simp [positiveDelta,hi,credit,Edge.grade]

/-- All four formulas agree on every exchange witness. -/
theorem reduction_eq {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) :
    literalDelta right i (coloredWord xs) = repairDelta right i (coloredWord xs) := by
  cases he with
  | right pre hc =>
      have hl : pre.length = (pre.map uncolor).length := by simp
      cases hc with
      | zero q es hx hq hcol =>
          simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true]
          rw [hl,repairDelta_right (pre.map uncolor)]
          simp only [hx,↓reduceIte]
          exact right_zero _ _ _
      | @positive y q es ds n j hx hy hi hr =>
          simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true]
          rw [hl,repairDelta_right (pre.map uncolor)]
          simp only [hx,hy,Nat.add_sub_cancel,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
          exact right_positive _ _ n j hi
  | left pre es hc =>
      have hl : pre.length = (pre.map uncolor).length := by simp
      simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
        Bool.false_eq_true,ite_false,ite_true]
      rw [hl,repairDelta_left (pre.map uncolor),left]

/-- Natural subtraction is exactly the integer min/max formula in the paper. -/
theorem positive_formula (h : ℕ) (b θ : ℤ) :
    ((h-min h (b-θ).toNat : ℕ) : ℤ) =
      (h : ℤ) - min (h : ℤ) (max (b-θ) 0) :=
  positive_reduction_formula h b θ

end KroneckerLiteralRepair
