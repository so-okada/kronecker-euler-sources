import KroneckerColoredExchangeRecovery

/- Original module: KroneckerColoredEdgeDictionary -/
section
/-! Exact conversion between ordered colored edges and the original finite path colorings. -/
set_option autoImplicit false
namespace KroneckerColoredEdgeDictionary
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell KroneckerColoredEdges

def ofColoring {m : ℕ} (U : List Bool) (g : Coloring m U.length) : List (CEdge m) :=
  List.zip U (List.ofFn g)

theorem ofColoring_shape {m : ℕ} (U : List Bool) (g : Coloring m U.length) :
    coloredShape (ofColoring U g)=U := by
  exact List.map_fst_zip (by simp)

theorem ofColoring_colors {m : ℕ} (U : List Bool) (g : Coloring m U.length) :
    (ofColoring U g).map Prod.snd=List.ofFn g := by
  exact List.map_snd_zip (by simp)

theorem ofColoring_word {m : ℕ} (U : List Bool) (g : Coloring m U.length) :
    coloredWord (ofColoring U g)=pathWord U g := by
  rw [word_zip]
  unfold coloredWord ofColoring
  rw [List.map_zip_eq_zipWith]
  rfl

def toColoring {m : ℕ} {U : List Bool} (es : List (CEdge m)) (hs : coloredShape es=U) :
    Coloring m U.length :=
  fromList (es.map Prod.snd) (by have hh := congrArg List.length hs; simpa [coloredShape] using hh)

theorem of_toColoring {m : ℕ} {U : List Bool} (es : List (CEdge m)) (hs : coloredShape es=U) :
    ofColoring U (toColoring es hs)=es := by
  unfold ofColoring toColoring
  rw [fromList_colors,← hs]
  change (es.map Prod.fst).zip (es.map Prod.snd)=es
  simpa only [List.unzip_fst,List.unzip_snd] using List.zip_unzip es

theorem toColoring_word {m : ℕ} {U : List Bool} (es : List (CEdge m)) (hs : coloredShape es=U) :
    pathWord U (toColoring es hs)=coloredWord es := by
  rw [← ofColoring_word,of_toColoring]

theorem ofColoring_injective {m : ℕ} (U : List Bool) : Function.Injective (@ofColoring m U) := by
  intro g h he
  have hh := congrArg (List.map Prod.snd) he
  rw [ofColoring_colors,ofColoring_colors] at hh
  exact List.ofFn_injective hh

end KroneckerColoredEdgeDictionary
end

/- Original module: KroneckerColoredShapeSplit -/
section
/-! Split colored words at prescribed shape boundaries without changing any palette. -/
set_option autoImplicit false
namespace KroneckerColoredShapeSplit
open KroneckerColoring KroneckerColoredEdges

theorem colored_shape_cons {m : ℕ} {es : List (CEdge m)} {b : Bool} {U : List Bool}
    (h : coloredShape es=b::U) : ∃ p ds, es=(b,p)::ds ∧ coloredShape ds=U := by
  cases es with
  | nil => simp [coloredShape] at h
  | cons e es =>
    have hh := List.cons.inj h
    rcases e with ⟨c,p⟩
    have hb : c=b := hh.1
    subst c
    exact ⟨p,es,rfl,hh.2⟩

theorem colored_shape_append {m : ℕ} {es : List (CEdge m)} {U V : List Bool}
    (h : coloredShape es=U++V) :
    ∃ xs ys, es=xs++ys ∧ coloredShape xs=U ∧ coloredShape ys=V := by
  refine ⟨es.take U.length,es.drop U.length,(List.take_append_drop _ _).symm,?_,?_⟩
  · change (es.take U.length).map Prod.fst=U
    rw [List.map_take]
    change (coloredShape es).take U.length=U
    rw [h,List.take_left]
  · change (es.drop U.length).map Prod.fst=V
    rw [List.map_drop]
    change (coloredShape es).drop U.length=V
    rw [h,List.drop_left]

end KroneckerColoredShapeSplit
end

/- Original module: KroneckerExchangePath -/
section
/-! Fixed source/target shapes for an adjacent exchange after the old first horizontal. -/
set_option autoImplicit false
namespace KroneckerExchangePath

def sourcePath (right : Bool) (P Q : List Bool) : List Bool :=
  if right then true::(P++true::false::Q) else true::(P++false::true::Q)
def targetPath (right : Bool) (P Q : List Bool) : List Bool := sourcePath (!right) P Q


theorem exchange_path_horizontal (right : Bool) (P Q : List Bool) :
    (sourcePath right P Q).count true=(targetPath right P Q).count true := by
  cases right <;> simp [sourcePath,targetPath,List.count_append,Nat.add_comm,Nat.add_left_comm]

end KroneckerExchangePath
end
