import KroneckerWrappedExchangeAssembly

/-! Lemma 9.10, Claim 3: colors are compared in separate horizontal
and vertical traversal order. An unchanged grade retains its color. -/
set_option autoImplicit false
namespace KroneckerExchangeRecolor
open KroneckerColoring KroneckerColoredEdges KroneckerColoredRepair
open KroneckerColoredExchangeRelation KroneckerExchangeColorOrder

theorem list_refl {m : ℕ} (xs : List (Palette m)) :
    List.Forall₂ RespectsRecol xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (respects_self x) ih

private theorem list_append {m : ℕ} {xs ys zs ws : List (Palette m)}
    (h : List.Forall₂ RespectsRecol xs ys) (k : List.Forall₂ RespectsRecol zs ws) :
    List.Forall₂ RespectsRecol (xs ++ zs) (ys ++ ws) := by
  induction h with
  | nil => exact k
  | cons h _ ih => exact .cons h ih

theorem repair_vertical {m j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m}
    (h : ColoredRepairAt j xs ys p q) :
    List.Forall₂ RespectsRecol (verticalColors xs) (verticalColors ys) := by
  induction h with
  | here es p q _ hc => exact .cons hc (list_refl _)
  | there e _ ih =>
    rcases e with ⟨b, r⟩
    cases b with
    | false => exact .cons (respects_self r) ih
    | true => exact ih

theorem exchange_vertical {m i d : ℕ} {right : Bool}
    {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) :
    List.Forall₂ RespectsRecol (verticalColors xs) (verticalColors ys) := by
  cases he with
  | right pre hc =>
    cases hc with
    | zero q es hx hq hc =>
      simpa [verticalColors, List.filterMap_append, List.filterMap_cons] using
        list_append (list_refl (verticalColors pre)) (.cons hc (list_refl _))
    | positive hx hy hi hr =>
      simpa [verticalColors, List.filterMap_append, List.filterMap_cons] using
        list_append (list_refl (verticalColors pre)) (.cons (respects_self _) (repair_vertical hr))
  | left pre es hc =>
    cases hc with
    | zero => simpa [verticalColors] using list_refl (verticalColors pre ++ p :: verticalColors es)
    | positive =>
      simpa [verticalColors, List.filterMap_append, List.filterMap_cons] using
        list_append (list_refl (verticalColors pre)) (.cons (respects_zero _) (list_refl (verticalColors es)))

open KroneckerEdgeShell KroneckerColoredEdgeDictionary KroneckerProgramExecution
open KroneckerWrappedExchangeWitness KroneckerWrappedExchangeMap

theorem exchangeMap_vertical {m : ℕ} (s : ExchangeSpec m)
    (a : SurplusColorings m s.source) :
    List.Forall₂ RespectsRecol
      (verticalColors (edgeShell s.u s.v s.hu s.hv s.hm (ofColoring s.source a.2.val)))
      (verticalColors (ofColoring s.target (exchangeMap s a).2.val)) := by
  rw [exchangeMap_edges]
  have hc := exchange_vertical (chosen s a).exchange
  simpa only [edgeShell, verticalColors, List.filterMap_append] using
    list_append (list_refl (verticalColors (edgePrefix m s.u s.hu)))
      (list_append hc (list_refl (verticalColors (edgeSuffix m s.v s.hv s.hm))))

open KroneckerBinaryExchangeShapes KroneckerBinaryExchangeSpec KroneckerBinaryExchangeMap
open KroneckerSurplusPathTransport KroneckerBinaryExchangeColors KroneckerWordCounts

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem binary_vertical (right : Bool) (rs ts : List ℕ) (u v : ℕ)
    (hu : 1 ≤ u ∧ u ≤ 2) (hv : 1 ≤ v ∧ v ≤ 2)
    (a : SurplusColorings 3 (runWord (rs ++ pairRuns right ++ ts))) :
    List.Forall₂ RespectsRecol
      (verticalColors (edgeShell u v (by omega) (by omega) (by decide)
        (ofColoring (runWord (rs ++ pairRuns right ++ ts)) a.2.val)))
      (verticalColors (ofColoring (runWord (u :: (rs ++ pairRuns (!right) ++ ts) ++ [v]))
        (binaryExchange right rs ts u v hu hv a).2.val)) := by
  have hh := exchangeMap_vertical (binarySpec right rs ts u v hu hv)
    (transport (binary_spec_source right rs ts u v hu hv).symm a)
  simpa only [binaryExchange, transport_edges, binarySpec] using hh

end KroneckerExchangeRecolor
