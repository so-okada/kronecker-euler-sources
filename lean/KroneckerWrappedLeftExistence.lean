import KroneckerExchangePath

/- Original module: KroneckerExchangeColorOrder -/
section
/-! Ordered horizontal palettes are unchanged; at most one ordered vertical palette is replaced. -/
set_option autoImplicit false
namespace KroneckerExchangeColorOrder
open KroneckerColoring KroneckerColoredEdges KroneckerColoredRepair KroneckerRightColoredChange
open KroneckerColoredExchangeRelation

def horizontalColors {m : ℕ} (es : List (CEdge m)) : List (Palette m) :=
  es.filterMap (fun e => if e.1 then some e.2 else none)
def verticalColors {m : ℕ} (es : List (CEdge m)) : List (Palette m) :=
  es.filterMap (fun e => if e.1 then none else some e.2)

inductive OneChange {α : Type*} : List α → List α → Prop
  | here (p q : α) (xs : List α) : OneChange (p::xs) (q::xs)
  | there (p : α) {xs ys : List α} (h : OneChange xs ys) : OneChange (p::xs) (p::ys)

theorem oneChange_append_left {α : Type*} {xs ys : List α} (h : OneChange xs ys) (pre : List α) :
    OneChange (pre++xs) (pre++ys) := by
  induction pre with
  | nil => exact h
  | cons p pre ih => exact .there p ih

theorem oneChange_append_right {α : Type*} {xs ys : List α} (h : OneChange xs ys) (post : List α) :
    OneChange (xs++post) (ys++post) := by
  induction h with
  | here p q xs => exact .here p q (xs++post)
  | there p _ ih => exact .there p ih

theorem repair_horizontal_colors {m j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m}
    (h : ColoredRepairAt j xs ys p q) : horizontalColors xs=horizontalColors ys := by
  induction h with
  | here => rfl
  | there e _ ih =>
    rcases e with ⟨b,r⟩
    cases b with
    | false => exact ih
    | true => exact congrArg (List.cons r) ih

theorem repair_vertical_colors {m j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m}
    (h : ColoredRepairAt j xs ys p q) : OneChange (verticalColors xs) (verticalColors ys) := by
  induction h with
  | here es p q _ _ => exact .here p q (verticalColors es)
  | there e _ ih =>
    rcases e with ⟨b,r⟩
    cases b with
    | false => exact .there r ih
    | true => exact ih

theorem exchange_horizontal_colors {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) : horizontalColors xs=horizontalColors ys := by
  cases he with
  | right pre hc =>
    cases hc with
    | zero => simp [horizontalColors]
    | positive _ _ _ hr =>
      have hh := repair_horizontal_colors hr
      simpa [horizontalColors] using hh
  | left => simp [horizontalColors]

theorem exchange_vertical_colors {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) : OneChange (verticalColors xs) (verticalColors ys) := by
  cases he with
  | right pre hc =>
    cases hc with
    | zero =>
      simp only [verticalColors,List.filterMap_append,List.filterMap_cons]
      exact oneChange_append_left (.here _ _ _) _
    | positive hx hy hi hr =>
      simpa [verticalColors] using oneChange_append_left (.there _ (repair_vertical_colors hr)) (verticalColors pre)
  | left pre es hc =>
    simpa [verticalColors] using oneChange_append_left (.here _ _ (verticalColors es)) (verticalColors pre)

end KroneckerExchangeColorOrder
end

/- Original module: KroneckerWrappedRightExistence -/
section
/-! Existence of the actual wrapped right exchange on every connected colored source. -/
set_option autoImplicit false
namespace KroneckerWrappedRightExistence
open KroneckerStack KroneckerColoring KroneckerColoredEdges KroneckerColoredShapeSplit
open KroneckerColoredNodeLoops KroneckerColoredExchangeRelation KroneckerRightColoredChange
open KroneckerEdgeShell KroneckerExchangePath

theorem wrapped_right_exists {m c : ℕ} (P Q : List Bool) (u v : ℕ)
    (hu : u+1≤m) (hv : v-1≤m) (hm : 2≤m) (cs : List (CEdge m))
    (hshape : coloredShape cs=sourcePath true P Q) (hc : Connected m (coloredWord cs) c) :
    ∃ ds code d, Exchange true (P.length+1) cs ds code d ∧
      coloredShape ds=targetPath true P Q ∧
      Connected m (coloredWord (edgeShell u v hu hv hm ds)) (c+d) := by
  obtain ⟨z,tail,rfl,ht⟩ := colored_shape_cons hshape
  obtain ⟨pre,rest,hr,hpre,hrest⟩ := colored_shape_append ht
  subst tail
  obtain ⟨x,rest',hr',hx⟩ := colored_shape_cons hrest
  subst rest
  obtain ⟨y,es,hes,hy⟩ := colored_shape_cons hx
  subst rest'
  obtain ⟨q,ds,p,d,hchange,hloop⟩ := right_node_loop (connected_node hc)
  have hp : pre.length=P.length := by simpa [coloredShape] using congrArg List.length hpre
  refine ⟨(true,z)::(pre++(false,q)::(true,x)::ds),p,d,?_,?_,?_⟩
  · simpa [hp] using Exchange.right ((true,z)::pre) hchange
  · have hds : coloredShape ds=Q := (right_change_shape hchange).symm.trans hy
    simp only [coloredShape,List.map_cons,List.map_append]
    change true::(coloredShape pre++false::true::coloredShape ds)=_
    rw [hpre,hds]
    rfl
  · exact edgeShell_connected u v hu hv hm _ hloop

end KroneckerWrappedRightExistence
end

/- Original module: KroneckerWrappedLeftExistence -/
section
/-! Existence of the actual wrapped left exchange on every connected colored source. -/
set_option autoImplicit false
namespace KroneckerWrappedLeftExistence
open KroneckerStack KroneckerColoring KroneckerColoredEdges KroneckerColoredShapeSplit
open KroneckerColoredNodeLoops KroneckerColoredExchangeRelation KroneckerEdgeShell KroneckerExchangePath

theorem wrapped_left_exists {m c : ℕ} (P Q : List Bool) (u v : ℕ)
    (hu : u+1≤m) (hv : v-1≤m) (hm : 2≤m) (cs : List (CEdge m))
    (hshape : coloredShape cs=sourcePath false P Q) (hc : Connected m (coloredWord cs) c) :
    ∃ ds code d, Exchange false (P.length+1) cs ds code d ∧
      coloredShape ds=targetPath false P Q ∧
      Connected m (coloredWord (edgeShell u v hu hv hm ds)) (c+d) := by
  obtain ⟨z,tail,rfl,ht⟩ := colored_shape_cons hshape
  obtain ⟨pre,rest,hr,hpre,hrest⟩ := colored_shape_append ht
  subst tail
  obtain ⟨y,rest',hr',hy⟩ := colored_shape_cons hrest
  subst rest
  obtain ⟨x,es,hes,hx⟩ := colored_shape_cons hy
  subst rest'
  obtain ⟨q,d,hchange,hloop⟩ := left_node_loop (connected_node hc)
  have hp : pre.length=P.length := by simpa [coloredShape] using congrArg List.length hpre
  refine ⟨(true,z)::(pre++(true,x)::(false,q)::es),y,d,?_,?_,?_⟩
  · simpa [hp] using Exchange.left ((true,z)::pre) es hchange
  · simp only [coloredShape,List.map_cons,List.map_append]
    change true::(coloredShape pre++true::false::coloredShape es)=_
    rw [hpre,hx]
    rfl
  · exact edgeShell_connected u v hu hv hm _ hloop

end KroneckerWrappedLeftExistence
end
