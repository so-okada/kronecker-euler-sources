import KroneckerAdjacentExchangeLemma

/-! Lemma 9.5: the grade decrease and its index, independent of vertical
grades and colors. Connectedness comes from the constructed exchange witness. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerExchangeIntermediateLemma
open KroneckerStack KroneckerMarkedDebtIndex KroneckerVerticalRepair
open KroneckerColoring KroneckerColoredEdges KroneckerColoredRepair
open KroneckerRightColoredChange KroneckerLeftColoredExecution
open KroneckerColoredExchangeRelation KroneckerWrappedExchangeWitness

def verticalCount : List Edge → ℕ
  | [] => 0
  | .H _ :: es => verticalCount es
  | .V _ :: es => verticalCount es + 1
def verticalGrades : List Edge → List ℕ
  | [] => []
  | .H _ :: es => verticalGrades es
  | .V h :: es => h :: verticalGrades es

def changeIndex (right : Bool) : ℕ → List Edge → ℕ
  | 0, .H g :: .V _ :: es =>
      if right && (g != 0) then
        1 + verticalCount (es.take ((markedIndex (g-1) es).getD 0)) else 0
  | 0, _ => 0
  | _+1, [] => 0
  | i+1, .H _ :: es => changeIndex right i es
  | i+1, .V _ :: es => 1 + changeIndex right i es

theorem verticalCount_sameDebt {xs ys : List Edge}
    (h : List.Forall₂ SameDebt xs ys) : verticalCount xs = verticalCount ys := by
  induction h with
  | nil => rfl
  | cons he ht ih => cases he <;> simpa [verticalCount] using ih

theorem verticalCount_take_sameDebt {xs ys : List Edge}
    (h : List.Forall₂ SameDebt xs ys) (n : ℕ) :
    verticalCount (xs.take n) = verticalCount (ys.take n) := by
  induction h generalizing n with
  | nil => rfl
  | cons he ht ih =>
    cases n with
    | zero => rfl
    | succ n => cases he <;> simp [verticalCount, ih]

theorem changeIndex_sameDebt {xs ys : List Edge}
    (h : List.Forall₂ SameDebt xs ys) (right : Bool) (i : ℕ) :
    changeIndex right i xs = changeIndex right i ys := by
  induction i generalizing xs ys with
  | zero =>
    cases h with
    | nil => rfl
    | cons he ht =>
      cases he with
      | vertical a b => rfl
      | horizontal g =>
        cases ht with
        | nil => rfl
        | cons he ht =>
          cases he with
          | horizontal h => rfl
          | vertical a b =>
            simp only [changeIndex]
            split_ifs
            · rw [markedIndex_invariant ht]
              rw [verticalCount_take_sameDebt ht]
            · rfl
  | succ i ih =>
    cases h with
    | nil => rfl
    | cons he ht => cases he <;> simp only [changeIndex, ih ht]

theorem changeIndex_prefix (right : Bool) (pre es : List Edge) :
    changeIndex right pre.length (pre ++ es) =
      verticalCount pre + changeIndex right 0 es := by
  induction pre with
  | nil => simp [verticalCount]
  | cons e pre ih => cases e <;> simp [changeIndex, verticalCount, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem changeIndex_colored_prefix {m : ℕ} (right : Bool) (pre : List (CEdge m)) (es : List Edge) :
    changeIndex right pre.length (pre.map uncolor ++ es) =
      verticalCount (coloredWord pre) + changeIndex right 0 es := by
  simpa only [coloredWord, List.length_map] using changeIndex_prefix right (coloredWord pre) es

theorem verticalGrades_append (pre es : List Edge) :
    verticalGrades (pre ++ es) = verticalGrades pre ++ verticalGrades es := by
  induction pre with
  | nil => rfl
  | cons e pre ih => cases e <;> simp [verticalGrades, ih]
theorem verticalGrades_length (es : List Edge) :
    (verticalGrades es).length = verticalCount es := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp [verticalGrades, verticalCount, ih]

inductive LowerAt : ℕ → ℕ → List ℕ → List ℕ → Prop
  | here (xs : List ℕ) (h k : ℕ) (hk : k ≤ h) :
      LowerAt (h-k) 0 (h::xs) (k::xs)
  | there {d j : ℕ} {xs ys : List ℕ} (a : ℕ) (h : LowerAt d j xs ys) :
      LowerAt d (j+1) (a::xs) (a::ys)

theorem lowerAt_prefix {d j : ℕ} {xs ys : List ℕ} (h : LowerAt d j xs ys) (pre : List ℕ) :
    LowerAt d (pre.length+j) (pre++xs) (pre++ys) := by
  induction pre with
  | nil => simpa using h
  | cons a pre ih => simpa only [List.length_cons, List.cons_append, Nat.add_right_comm] using LowerAt.there a ih

theorem lowerAt_suffix {d j : ℕ} {xs ys : List ℕ} (h : LowerAt d j xs ys) (post : List ℕ) :
    LowerAt d j (xs++post) (ys++post) := by
  induction h with
  | here xs a b hb => exact .here (xs++post) a b hb
  | there a h ih => exact .there a ih

theorem lowerAt_properties {d j : ℕ} {xs ys : List ℕ} (h : LowerAt d j xs ys) :
    j < xs.length ∧ xs.length = ys.length ∧ d ≤ xs[j]! ∧
    ys[j]! + d = xs[j]! ∧ ∀ i, i ≠ j → ys[i]? = xs[i]? := by
  induction h with
  | here xs a b hb =>
    refine ⟨by simp, by simp, by simpa using Nat.sub_le a b,
      by simpa using Nat.add_sub_of_le hb, ?_⟩
    intro i hi
    cases i with
    | zero => contradiction
    | succ i => rfl
  | @there d j xs ys a h ih =>
    obtain ⟨hj, hl, hd, he, hall⟩ := ih
    refine ⟨by simpa using hj, by simp [hl], by simpa using hd, by simpa using he, ?_⟩
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hall i (by omega)

theorem repair_vertical_decrease {j h k : ℕ} {xs ys : List Edge}
    (hr : RepairAt j xs ys h k) :
    LowerAt (h-k) (verticalCount (xs.take j)) (verticalGrades xs) (verticalGrades ys) := by
  induction hr with
  | here es h k hk => exact .here _ h k hk
  | there e hr ih =>
    cases e with
    | H g => simpa [verticalCount, verticalGrades] using ih
    | V g => simpa [verticalCount, verticalGrades] using LowerAt.there g ih

theorem right_change_decrease {m d : ℕ} {x y q p : Palette m} {es ds : List (CEdge m)}
    (hr : RightChange x y es q ds p d) :
    LowerAt d (changeIndex true 0 (.H (grade x) :: .V (grade y) :: coloredWord es))
      (grade y :: verticalGrades (coloredWord es))
      (grade q :: verticalGrades (coloredWord ds)) := by
  cases hr with
  | zero q es hx hq hc =>
    simpa [changeIndex, hx, hq] using
      LowerAt.here (verticalGrades (coloredWord es)) (grade y) (grade y-1) (Nat.sub_le _ _)
  | @positive p q es ds n j hx hy hi hr =>
    have hh := LowerAt.there (grade y) (repair_vertical_decrease (colored_repair_word hr))
    simpa [changeIndex, hx, hi, Nat.add_comm] using hh

theorem left_change_decrease {m d : ℕ} {x y q : Palette m}
    (hr : LeftChange x y q d) (es : List Edge) :
    LowerAt d 0 (grade y :: verticalGrades es) (grade q :: verticalGrades es) := by
  cases hr with
  | zero hx => simpa using LowerAt.here (verticalGrades es) (grade y) (grade y) le_rfl
  | positive hx => simpa using LowerAt.here (verticalGrades es) (grade y) 0 (Nat.zero_le _)

theorem exchange_decrease {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) :
    LowerAt d (changeIndex right i (coloredWord xs))
      (verticalGrades (coloredWord xs)) (verticalGrades (coloredWord ys)) := by
  cases he with
  | right pre hc =>
    have h := lowerAt_prefix (right_change_decrease hc) (verticalGrades (coloredWord pre))
    simp only [coloredWord, List.map_append, List.map_cons, uncolor, paint,
      Bool.false_eq_true, ↓reduceIte]
    rw [changeIndex_colored_prefix true pre]
    simpa only [coloredWord, verticalGrades_append, verticalGrades, verticalGrades_length] using h
  | left pre es hc =>
    have h := lowerAt_prefix (left_change_decrease hc (coloredWord es)) (verticalGrades (coloredWord pre))
    simp only [coloredWord, List.map_append, List.map_cons, uncolor, paint,
      Bool.false_eq_true, ↓reduceIte]
    rw [changeIndex_colored_prefix false pre]
    simpa only [coloredWord, changeIndex, verticalGrades_append, verticalGrades,
      verticalGrades_length] using h

theorem constructed_exchange_decrease (s : ExchangeSpec 3)
    (a : KroneckerProgramExecution.SurplusColorings 3 s.source) :
    (chosen s a).delta ≤ 3 ∧
    LowerAt (chosen s a).delta
      (changeIndex s.right (s.P.length+1)
        (coloredWord (KroneckerColoredEdgeDictionary.ofColoring s.source a.2.val)))
      (verticalGrades (coloredWord (KroneckerColoredEdgeDictionary.ofColoring s.source a.2.val)))
      (verticalGrades (coloredWord (chosen s a).middle)) :=
  ⟨exchange_budget (chosen s a).exchange, exchange_decrease (chosen s a).exchange⟩

open KroneckerEdgeShell

theorem shell_decrease {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) (u v : ℕ)
    (hu : u+1 ≤ m) (hv : v-1 ≤ m) (hm : 2 ≤ m) :
    LowerAt d (verticalCount (coloredWord (edgePrefix m u hu)) +
      changeIndex right i (coloredWord xs))
      (verticalGrades (coloredWord (edgeShell u v hu hv hm xs)))
      (verticalGrades (coloredWord (edgeShell u v hu hv hm ys))) := by
  have h := lowerAt_suffix
    (lowerAt_prefix (exchange_decrease he) (verticalGrades (coloredWord (edgePrefix m u hu))))
    (verticalGrades (coloredWord (edgeSuffix m v hv hm)))
  simpa only [edgeShell, coloredWord, List.map_append, verticalGrades_append,
    verticalGrades_length, List.append_assoc] using h

def horizontalGrades : List Edge → List ℕ
  | [] => []
  | .H g :: es => g :: horizontalGrades es
  | .V _ :: es => horizontalGrades es
def directions : List Edge → List Bool
  | [] => []
  | .H _ :: es => true :: directions es
  | .V _ :: es => false :: directions es

theorem sameDebt_of_horizontal {xs ys : List Edge}
    (hs : directions xs = directions ys) (hh : horizontalGrades xs = horizontalGrades ys) :
    List.Forall₂ SameDebt xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact .nil
    | cons e ys => cases e <;> simp [directions] at hs
  | cons e xs ih =>
    cases ys with
    | nil => cases e <;> simp [directions] at hs
    | cons f ys =>
      cases e <;> cases f <;> simp only [directions, List.cons.injEq, Bool.true_eq_false,
        Bool.false_eq_true, false_and, true_and] at hs
      · simp only [horizontalGrades, List.cons.injEq] at hh
        obtain ⟨rfl, hh⟩ := hh
        exact .cons (.horizontal _) (ih hs hh)
      · exact .cons (.vertical _ _) (ih hs hh)

theorem changeIndex_of_horizontal {xs ys : List Edge}
    (hs : directions xs = directions ys) (hh : horizontalGrades xs = horizontalGrades ys)
    (right : Bool) (i : ℕ) : changeIndex right i xs = changeIndex right i ys :=
  changeIndex_sameDebt (sameDebt_of_horizontal hs hh) right i

end KroneckerExchangeIntermediateLemma
