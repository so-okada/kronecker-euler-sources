import KroneckerWeightedSupportDeckCriterion
import KroneckerFiniteAccumulatedStableIndex
import KroneckerTreeInducedEmbedding
import KroneckerFullImageNumericalTransport

section

/- Original module: KroneckerDirectSumDimensionForest -/
section
/-! At explicit depth |A|*B+1 in the genuine direct-sum tower, the complete
induced support of EVERY dimension vector of total at most B is a reduced
forest. The estimate includes all induced arrows, and requires finiteness
only of the original arrow alphabet. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumDimensionForest
open KroneckerAbelianCover LabeledWalk KroneckerTypedQuiverMaps
open KroneckerTypedReducedForest KroneckerFiniteSupportInducedQuiver
open KroneckerIteratedFiniteSupportArrows
attribute [local instance] Classical.decEq Classical.propDecidable

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

theorem induced_girth (Q : TypedQuiver) (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q (n+1)).V →₀ ℕ) :
    ReducedGirthBound (supportQuiver (KroneckerDirectSumIteratedGirth.iterate Q (n+1)) d).source
      (supportQuiver (KroneckerDirectSumIteratedGirth.iterate Q (n+1)) d).target (2^n+2) := by
  let i : QuiverMap (supportQuiver (KroneckerDirectSumIteratedGirth.iterate Q (n+1)) d)
      (KroneckerDirectSumIteratedGirth.iterate Q (n+1)) :=
    ⟨Subtype.val,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  exact i.pull_girth Subtype.val_injective _ (KroneckerDirectSumIteratedGirth.iterate_girth Q n)

theorem support_forest (Q : TypedQuiver) [Fintype Q.A] (B : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q (Fintype.card Q.A * B + 1)).V →₀ ℕ)
    (hB : d.sum (fun _ k => k) ≤ B) :
    ReducedForest (supportQuiver (KroneckerDirectSumIteratedGirth.iterate Q (Fintype.card Q.A * B + 1)) d) := by
  let n := Fintype.card Q.A * B
  let P := KroneckerDirectSumIteratedGirth.iterate Q (n+1)
  haveI := directSupportArrow_finite Q (n+1) d
  let : Fintype (SupportArrow P.source P.target d) := Fintype.ofFinite _
  let : Fintype (supportQuiver P d).A := inferInstanceAs (Fintype (SupportArrow P.source P.target d))
  apply forest_of_finite_girth (supportQuiver P d) (2^n+2) (induced_girth Q n d)
  have ha := directSupportArrow_card_le Q (n+1) d
  have hs := (KroneckerBoundedCoverDimensions.support_card_le_total d).trans hB
  have hc : Fintype.card (supportQuiver P d).A ≤ n := by
    change Fintype.card (SupportArrow P.source P.target d) ≤ n
    rw [← Nat.card_eq_fintype_card]
    exact ha.trans (Nat.mul_le_mul_left _ hs)
  have hp := Nat.lt_two_pow_self (n:=n)
  omega

end KroneckerDirectSumDimensionForest
end
end

/- Original module: KroneckerDirectSumStableSupportTree -/
section
/-! Every nonzero stable representation of total at most B at direct-sum depth
|A|*B+1 has a connected reduced-forest FULL support. Actual reduced root paths
exist inside that support, have distinct vertices, and length strictly below
its total dimension. This supplies finite typed trees for the next universal
colored-tree comparison, without assuming that comparison in advance. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumStableSupportTree
open KroneckerAbelianCover LabeledWalk KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
open KroneckerTypedReducedForest KroneckerStableSupportTypedConnectivity
open KroneckerWeightedSupportDeckCriterion
attribute [local instance] Classical.decEq Classical.propDecidable

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)
local instance supportQuiverFintype (Q : TypedQuiver) (d : Q.V →₀ ℕ) : Fintype (supportQuiver Q d).V :=
  supportFintype d

theorem stable_support_connected (Q : TypedQuiver) (d : Q.V →₀ ℕ) (hd : d ≠ 0)
    (θ : Q.V → ℤ) (R : Representation Q.source Q.target (fun v => d v))
    (hR : FiniteSupportStable d θ R) : SupportConnected Q d := by
  obtain ⟨r,hr⟩ := Finsupp.support_nonempty_iff.mpr hd
  refine ⟨⟨r,hr⟩,fun v => ?_⟩
  exact finite_stable_walk_connected (supportQuiver Q d) (supportDimension d) (restrictToSupport Q d R)
    (supportCharacter d θ) ((finiteSupportStable_iff_restrict Q d θ R).mp hR)
    (fun w => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp w.property)) ⟨r,hr⟩ v

theorem stable_support_tree (Q : TypedQuiver) [Fintype Q.A] (B : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q (Fintype.card Q.A * B + 1)).V →₀ ℕ)
    (hd : d ≠ 0) (hB : d.sum (fun _ k => k) ≤ B)
    (θ : (KroneckerDirectSumIteratedGirth.iterate Q (Fintype.card Q.A * B + 1)).V → ℤ)
    (R : Representation (KroneckerDirectSumIteratedGirth.iterate Q (Fintype.card Q.A * B + 1)).source
      (KroneckerDirectSumIteratedGirth.iterate Q (Fintype.card Q.A * B + 1)).target (fun v => d v))
    (hR : FiniteSupportStable d θ R) :
    ReducedForest (supportQuiver (KroneckerDirectSumIteratedGirth.iterate Q (Fintype.card Q.A * B + 1)) d) ∧
      SupportConnected (KroneckerDirectSumIteratedGirth.iterate Q (Fintype.card Q.A * B + 1)) d :=
  ⟨KroneckerDirectSumDimensionForest.support_forest Q B d hB,stable_support_connected _ d hd θ R hR⟩


end KroneckerDirectSumStableSupportTree
end
end
end

section

/- Original module: KroneckerBallDartDictionary -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

/-- Positive girth excludes actual loop arrows, not just loops in the collapsed
graph representation. -/
theorem signed_step_endpoints_ne {g : ℕ} (hg : ReducedGirthBound s t g) (h2 : 2 < g)
    (x : A × Bool) : stepStart s t x ≠ stepEnd s t x := by
  intro hx
  let p := castEndpoints rfl hx.symm (oneStep s t x)
  have hp : Reduced p := by simp [p,Reduced,labels_castEndpoints,oneStep_labels]
  have he := reduced_closed_empty_below_girth hg p hp (by
    simp only [p,labels_castEndpoints,oneStep_labels,List.length_singleton]; omega)
  simpa only [p,labels_castEndpoints,oneStep_labels,List.cons_ne_nil] using he

/-- The ordered endpoints determine the FULL signed arrow at girth>2. Hence
parallel and opposite directed-arrow multiplicities are not lost on passing to
the underlying simple graph. -/
theorem signed_step_endpoints_injective {g : ℕ} (hg : ReducedGirthBound s t g) (h2 : 2 < g)
    (x y : A × Bool) (hs : stepStart s t x = stepStart s t y)
    (ht : stepEnd s t x = stepEnd s t y) : x = y := by
  let p := oneStep s t x
  let q := castEndpoints hs.symm ht.symm (oneStep s t y)
  have hp : Reduced p := by simp [p,Reduced,oneStep_labels]
  have hq : Reduced q := by simp [q,Reduced,labels_castEndpoints,oneStep_labels]
  have he := reduced_paths_unique_below_girth hg p q hp hq (by
    simpa only [p,q,labels_castEndpoints,oneStep_labels,List.length_singleton] using h2)
  have hl := congrArg labels he
  simpa only [p,q,labels_castEndpoints,oneStep_labels,List.singleton_inj] using hl

/-- ALL signed actual arrows with both endpoints in the radius ball. -/
def InternalSignedArrow (u : V) (r : ℕ) :=
  {x : A × Bool //
    (∃p : LabeledWalk s t u (stepStart s t x), Reduced p ∧ (labels p).length ≤ r) ∧
    (∃q : LabeledWalk s t u (stepEnd s t x), Reduced q ∧ (labels q).length ≤ r)}

noncomputable def signedArrowDart {g : ℕ} (hg : ReducedGirthBound s t g) (h2 : 2 < g)
    (u : V) (r : ℕ) (x : InternalSignedArrow (s:=s) (t:=t) u r) :
    (vertexBallGraph (s:=s) (t:=t) u r).Dart where
  toProd := (⟨stepStart s t x.val,x.property.1⟩,⟨stepEnd s t x.val,x.property.2⟩)
  adj := ⟨fun h => signed_step_endpoints_ne hg h2 x.val (congrArg Subtype.val h),x.val,rfl,rfl⟩

theorem signedArrowDart_bijective {g : ℕ} (hg : ReducedGirthBound s t g) (h2 : 2 < g)
    (u : V) (r : ℕ) : Function.Bijective (signedArrowDart hg h2 u r) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact signed_step_endpoints_injective hg h2 x.val y.val
      (congrArg (fun d => d.fst.val) h) (congrArg (fun d => d.snd.val) h)
  · intro d
    obtain ⟨x,hs,ht⟩ := d.adj.2
    have hxs : ∃p : LabeledWalk s t u (stepStart s t x), Reduced p ∧ (labels p).length ≤ r := by
      rw [←hs]; exact d.fst.property
    have hxt : ∃p : LabeledWalk s t u (stepEnd s t x), Reduced p ∧ (labels p).length ≤ r := by
      rw [←ht]; exact d.snd.property
    refine ⟨⟨x,hxs,hxt⟩,?_⟩
    apply SimpleGraph.Dart.ext
    exact Prod.ext (Subtype.ext hs.symm) (Subtype.ext ht.symm)

/-- Exact actual-arrow/dart dictionary; this is a bijection of named types. -/
noncomputable def signedArrowDartEquiv {g : ℕ} (hg : ReducedGirthBound s t g) (h2 : 2 < g)
    (u : V) (r : ℕ) : InternalSignedArrow (s:=s) (t:=t) u r ≃
      (vertexBallGraph (s:=s) (t:=t) u r).Dart :=
  Equiv.ofBijective (signedArrowDart hg h2 u r) (signedArrowDart_bijective hg h2 u r)

/-- The signed actual label recovered from a graph dart. -/
noncomputable def dartLabel {g : ℕ} (hg : ReducedGirthBound s t g) (h2 : 2 < g)
    {u : V} {r : ℕ} (d : (vertexBallGraph (s:=s) (t:=t) u r).Dart) : A × Bool :=
  ((signedArrowDartEquiv hg h2 u r).symm d).val




end LabeledWalk
end KroneckerAbelianCover
end

/- Original module: KroneckerTypedForestArrowDictionary -/
section
/-! Passing from a bipartite typed forest to its underlying simple graph loses
no actual arrow: directed arrows are in bijection with graph darts starting
on the source side. The forest hypothesis excludes every parallel or opposite
signed-arrow ambiguity before the graph is used. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTypedForestArrowDictionary
open KroneckerAbelianCover LabeledWalk KroneckerTypedReducedForest
open KroneckerProperBipartiteQuiver
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver}

theorem forest_girth (hQ : ReducedForest Q) (g : ℕ) : ReducedGirthBound Q.source Q.target g := by
  intro u p hp hpos
  rw [hQ u p hp] at hpos
  exact False.elim (Nat.lt_irrefl 0 hpos)

abbrev SourceDart (C : Coloring Q) :=
  {e : (underlyingGraph Q.source Q.target).Dart // C.side e.fst = 0}

def arrowDart (C : Coloring Q) (a : Q.A) : SourceDart C :=
  ⟨⟨(Q.source a,Q.target a),endpoints_ne C a,⟨(a,true),rfl,rfl⟩⟩,C.source_side a⟩



end KroneckerTypedForestArrowDictionary
end
end

/- Original module: KroneckerTypedForestGraphColoring -/
section
/-! The underlying simple graph of a properly colored typed forest inherits
an unambiguous proper edge coloring. Chosen signed arrow witnesses are proved
unique and reverse by flipping only orientation, so actual colors are not
lost in the graph conversion. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTypedForestGraphColoring
open KroneckerAbelianCover LabeledWalk KroneckerProperBipartiteQuiver
open KroneckerTypedReducedForest KroneckerTypedForestArrowDictionary
open KroneckerGraphColorWords
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver}

def edgeLabel {u v : Q.V} (h : (underlyingGraph Q.source Q.target).Adj u v) : Q.A × Bool :=
  Classical.choose h.2

theorem edgeLabel_endpoints {u v : Q.V} (h : (underlyingGraph Q.source Q.target).Adj u v) :
    stepStart Q.source Q.target (edgeLabel h) = u ∧ stepEnd Q.source Q.target (edgeLabel h) = v :=
  ⟨(Classical.choose_spec h.2).1.symm,(Classical.choose_spec h.2).2.symm⟩

theorem edgeLabel_unique (hQ : ReducedForest Q) {u v : Q.V}
    (h : (underlyingGraph Q.source Q.target).Adj u v) (x : Q.A × Bool)
    (hs : stepStart Q.source Q.target x = u) (ht : stepEnd Q.source Q.target x = v) : edgeLabel h = x :=
  signed_step_endpoints_injective (forest_girth hQ 3) (by omega) _ x
    ((edgeLabel_endpoints h).1.trans hs.symm) ((edgeLabel_endpoints h).2.trans ht.symm)

theorem edgeLabel_symm (hQ : ReducedForest Q) {u v : Q.V}
    (h : (underlyingGraph Q.source Q.target).Adj u v) :
    edgeLabel h.symm = ((edgeLabel h).1,!(edgeLabel h).2) := by
  apply edgeLabel_unique hQ
  · have hh := (edgeLabel_endpoints h).2
    generalize edgeLabel h = x at hh ⊢
    rcases x with ⟨a,b⟩
    cases b <;> exact hh
  · have hh := (edgeLabel_endpoints h).1
    generalize edgeLabel h = x at hh ⊢
    rcases x with ⟨a,b⟩
    cases b <;> exact hh

def graphColoring (C : Coloring Q) (hQ : ReducedForest Q) : EdgeColoring (underlyingGraph Q.source Q.target) where
  color h := C.color (edgeLabel h).1
  symm h := by rw [edgeLabel_symm hQ h]
  proper h k hc := by
    have he := signed_color_start_injective C (edgeLabel h) (edgeLabel k) hc
      ((edgeLabel_endpoints h).1.trans (edgeLabel_endpoints k).1.symm)
    exact (edgeLabel_endpoints h).2.symm.trans
      ((congrArg (stepEnd Q.source Q.target) he).trans (edgeLabel_endpoints k).2)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem graphColoring_arrow (C : Coloring Q) (hQ : ReducedForest Q) (a : Q.A) :
    (graphColoring C hQ).color (arrowDart C a).val.adj = C.color a := by
  change C.color (edgeLabel (arrowDart C a).val.adj).1 = C.color a
  rw [edgeLabel_unique hQ _ (a,true) rfl rfl]

end KroneckerTypedForestGraphColoring
end
end

/- Original module: KroneckerColoredGraphParity -/
section
/-! The side of a properly oriented quiver vertex agrees with graph-walk
length parity. A source or sink root has a concrete color word of the correct
parity, so single-vertex sink supports are included in the later tree lift. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerColoredGraphParity
open KroneckerAbelianCover KroneckerProperBipartiteQuiver
open KroneckerTypedForestGraphColoring KroneckerReducedColorWords
open KroneckerWordParity KroneckerColorWordAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver}

theorem edge_side (C : Coloring Q) {u v : Q.V} (h : (underlyingGraph Q.source Q.target).Adj u v) :
    C.side v = (C.side u + 1) % 2 := by
  have hh := signed_step_side C (edgeLabel h)
  rw [(edgeLabel_endpoints h).1,(edgeLabel_endpoints h).2] at hh
  exact hh

theorem walk_side (C : Coloring Q) {u v : Q.V} (p : (underlyingGraph Q.source Q.target).Walk u v) :
    C.side u = (p.length + C.side v) % 2 := by
  induction p with
  | nil => simpa only [SimpleGraph.Walk.length_nil,zero_add] using (Nat.mod_eq_of_lt (C.side_lt _)).symm
  | @cons u v w h p ih =>
    have hh := edge_side C h.symm
    rw [hh,ih]
    simp only [SimpleGraph.Walk.length_cons]
    omega

def sideWord (i : Fin 2) : Word := if i.val = 0 then root else toggle (0 : Color) root

theorem sideWord_parity (i : Fin 2) : parity (sideWord i) = i.val := by
  unfold sideWord
  split_ifs with h
  · simpa only [parity,root,List.length_nil,Nat.zero_mod] using h.symm
  · have hi : i.val = 1 := by have hh := i.isLt; omega
    rw [toggle_parity]
    simpa only [parity,root,List.length_nil,Nat.zero_mod] using hi.symm

end KroneckerColoredGraphParity
end
end

/- Original module: KroneckerOrientedTypedTreeLift -/
section
/-! Every properly colored typed tree embeds as an actual directed quiver in
the universal parity-oriented colored-word quiver. Root translation corrects
the parity even when the chosen root is a sink, and every actual arrow keeps
its original color. Vertices and arrows are both proved injective. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOrientedTypedTreeLift
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerTypedReducedForest
open KroneckerTypedForestGraphColoring KroneckerTypedForestArrowDictionary
open KroneckerColoredGraphParity KroneckerColoredTreeLift KroneckerGraphColorWords
open KroneckerReducedColorWords KroneckerWordTranslations KroneckerWordParity
open KroneckerCoverDeckTranslations KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerTypedQuiverMaps
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (hQ : ReducedForest Q)
  (hT : (underlyingGraph Q.source Q.target).IsTree)

def liftVertex (r v : Q.V) : Word :=
  translate (sideWord ⟨C.side r,C.side_lt r⟩) (rootLift (graphColoring C hQ) hT r v)

theorem liftVertex_parity (r v : Q.V) : parity (liftVertex C hQ hT r v) = C.side v := by
  rw [liftVertex,translate_parity,sideWord_parity]
  have hp := walk_side C (KroneckerTreeRootPaths.rootPath hT r v)
  change ((colors (graphColoring C hQ) (KroneckerTreeRootPaths.rootPath hT r v)).length % 2 + C.side r) % 2 = C.side v
  rw [colors_length]
  omega


theorem liftVertex_injective (r : Q.V) : Function.Injective (liftVertex C hQ hT r) :=
  (translation _).injective.comp (rootLift_injective _ hT r)

theorem liftVertex_arrow (r : Q.V) (a : Q.A) :
    liftVertex C hQ hT r (Q.target a) = toggle (C.color a) (liftVertex C hQ hT r (Q.source a)) := by
  have h := rootLift_step (graphColoring C hQ) hT r (arrowDart C a).val.adj
  rw [graphColoring_arrow] at h
  change rootLift (graphColoring C hQ) hT r (Q.source a) =
    toggle (C.color a) (rootLift (graphColoring C hQ) hT r (Q.target a)) at h
  have ht := congrArg (toggle (C.color a)) h
  rw [KroneckerReducedColorWords.toggle_involution] at ht
  change translate _ (rootLift _ _ _ _) = toggle _ (translate _ (rootLift _ _ _ _))
  rw [← translate_toggle,ht]

def liftMap (r : Q.V) : QuiverMap Q coloredCoverQuiver where
  vertex := liftVertex C hQ hT r
  arrow a := (C.color a,⟨liftVertex C hQ hT r (Q.source a),by rw [liftVertex_parity,C.source_side]⟩)
  source _ := rfl
  target a := (liftVertex_arrow C hQ hT r a).symm

theorem liftMap_arrow_injective (r : Q.V) : Function.Injective (liftMap C hQ hT r).arrow := by
  intro a b h
  apply C.source_injective a b
  · exact congrArg (fun x : coloredCoverQuiver.A => x.1) h
  · apply liftVertex_injective C hQ hT r
    exact congrArg (fun x : coloredCoverQuiver.A => x.2.val) h

end KroneckerOrientedTypedTreeLift
end
end

/- Original module: KroneckerOrientedTreeLiftFullness -/
section
/-! The oriented colored-tree lift identifies the FULL induced quiver on its
vertex image. Connectedness and acyclicity of the universal colored tree
reflect adjacency; parity recovers arrow direction and color uniqueness
recovers the actual arrow, including zero-matrix positions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOrientedTreeLiftFullness
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerTypedReducedForest
open KroneckerTypedForestGraphColoring KroneckerTypedForestArrowDictionary
open KroneckerOrientedTypedTreeLift KroneckerColoredTreeLift KroneckerReducedColorWords
open KroneckerWordTranslations KroneckerColorWordCover KroneckerWordParity
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerFullImageQuiverEmbedding
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (hQ : ReducedForest Q)
  (hT : (underlyingGraph Q.source Q.target).IsTree)

def liftGraphHom (r : Q.V) : (underlyingGraph Q.source Q.target) →g cover where
  toFun := liftVertex C hQ hT r
  map_rel' := by
    intro u v h
    refine ⟨(graphColoring C hQ).color h,?_⟩
    have hh := rootLift_step (graphColoring C hQ) hT r h
    have ht := congrArg (toggle ((graphColoring C hQ).color h)) hh
    rw [toggle_involution] at ht
    change toggle _ (translate _ (rootLift _ _ _ _)) = translate _ (rootLift _ _ _ _)
    rw [← translate_toggle,ht]

theorem lift_adj_iff (r u v : Q.V) :
    cover.Adj (liftVertex C hQ hT r u) (liftVertex C hQ hT r v) ↔
      (underlyingGraph Q.source Q.target).Adj u v :=
  KroneckerTreeInducedEmbedding.connected_hom_into_tree_induced hT.connected.preconnected cover_tree
    (liftGraphHom C hQ hT r) (liftVertex_injective C hQ hT r)

theorem lift_full (r : Q.V) : FullOnImage (liftMap C hQ hT r) := by
  intro a u v hs ht
  change a.2.val = liftVertex C hQ hT r u at hs
  change toggle a.1 a.2.val = liftVertex C hQ hT r v at ht
  have hu : C.side u = 0 := by
    rw [← liftVertex_parity C hQ hT r u,← hs]
    exact a.2.property
  have hg : cover.Adj (liftVertex C hQ hT r u) (liftVertex C hQ hT r v) := by
    refine ⟨a.1,?_⟩
    exact (congrArg (toggle a.1) hs).symm.trans ht
  have h := (lift_adj_iff C hQ hT r u v).mp hg
  obtain ⟨⟨b,ε⟩,hb,hv⟩ := h.2
  cases ε
  · have hh := hu
    rw [hb] at hh
    change C.side (Q.target b) = 0 at hh
    rw [C.target_side] at hh
    omega
  · have hbs : Q.source b = u := hb.symm
    have hbt : Q.target b = v := hv.symm
    have hc : C.color b = a.1 := by
      apply toggle_color_injective (liftVertex C hQ hT r u)
      dsimp only
      have hl := liftVertex_arrow C hQ hT r b
      rw [hbs,hbt] at hl
      rw [← hl,← ht,← hs]
    refine ⟨b,?_⟩
    apply Prod.ext
    · exact hc
    · apply Subtype.ext
      change liftVertex C hQ hT r (Q.source b) = a.2.val
      rw [hbs]
      exact hs.symm

end KroneckerOrientedTreeLiftFullness
end
end

/- Original module: KroneckerTypedTreeGraphBridge -/
section
/-! Actual typed walks in a properly bipartite quiver map to graph walks with
exactly the same vertex trace. A nonempty connected typed reduced forest is
therefore a Mathlib tree. This supplies the graph hypothesis for the oriented
universal-tree lift directly from checked typed support statements. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTypedTreeGraphBridge
open KroneckerAbelianCover LabeledWalk KroneckerProperBipartiteQuiver
open KroneckerTypedForestArrowDictionary KroneckerTypedReducedForest
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver}

def toGraph (C : Coloring Q) {u v : Q.V} (p : LabeledWalk Q.source Q.target u v) :
    (underlyingGraph Q.source Q.target).Walk u v := by
  induction p with
  | nil u => exact .nil
  | forward a p ih => exact .cons (arrowDart C a).val.adj ih
  | backward a p ih => exact .cons (arrowDart C a).val.adj.symm ih

theorem toGraph_support (C : Coloring Q) {u v : Q.V} (p : LabeledWalk Q.source Q.target u v) :
    (toGraph C p).support = vertices p := by
  induction p with
  | nil u => rfl
  | forward a p ih => exact congrArg (List.cons (Q.source a)) ih
  | backward a p ih => exact congrArg (List.cons (Q.target a)) ih

theorem reduced_toGraph_path (C : Coloring Q) (hQ : ReducedForest Q)
    {u v : Q.V} (p : LabeledWalk Q.source Q.target u v) (hp : Reduced p) : (toGraph C p).IsPath := by
  rw [SimpleGraph.Walk.isPath_def,toGraph_support]
  exact reduced_vertices_nodup Q hQ p hp

theorem underlying_tree (C : Coloring Q) (hQ : ReducedForest Q) (r : Q.V)
    (hc : ∀ v, Nonempty (LabeledWalk Q.source Q.target r v)) :
    (underlyingGraph Q.source Q.target).IsTree := by
  refine ⟨?_,underlyingGraph_acyclic hQ⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨r,fun v => ?_⟩
  obtain ⟨p⟩ := hc v
  exact ⟨toGraph C p⟩

end KroneckerTypedTreeGraphBridge
end
end

/- Original module: KroneckerDirectSumUniversalSupportEmbedding -/
section
/-! At the explicit three-arrow depth3B+1, every nonzero stable direct-sum
representation of total at most B has its COMPLETE support embedded fully
and faithfully into the universal directed colored-word quiver. Original
source/sink types and every original arrow color are preserved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumUniversalSupportEmbedding
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumBaseColoring
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteQuiverHom KroneckerFiniteSupportStability
open KroneckerDirectSumStableSupportTree KroneckerBipartiteColorRestriction
open KroneckerOrientedTypedTreeLift KroneckerOrientedTreeLiftFullness KroneckerTypedTreeGraphBridge
open KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerWordParity
attribute [local instance] Classical.decEq Classical.propDecidable

def depth (B : ℕ) := Fintype.card baseQuiver.A * B + 1

theorem depth_eq (B : ℕ) : depth B = 3*B+1 := by rw [depth,arrow_card]

theorem exists_full_colored_support_embedding (B : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)).V →₀ ℕ)
    (hd : d ≠ 0) (hB : d.sum (fun _ k => k) ≤ B)
    (θ : (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)).V → ℤ)
    (R : Representation (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)).source
      (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)).target (fun v => d v))
    (hR : FiniteSupportStable d θ R) :
    ∃ f : QuiverMap (supportQuiver (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)) d) coloredCoverQuiver,
      Function.Injective f.vertex ∧ Function.Injective f.arrow ∧ FullOnImage f ∧
      (∀ v, parity (f.vertex v) = (KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B) v.val).val) ∧
      (∀ a, (f.arrow a).1 = KroneckerDirectSumIteratedEmbedding.baseArrow baseQuiver (depth B) a.val) := by
  obtain ⟨hf,r,hr⟩ := stable_support_tree baseQuiver B d hd hB θ R hR
  let C := restrictColoring (KroneckerDirectSumBaseColoring.coloring (depth B)) d
  let hT := underlying_tree C hf r hr
  refine ⟨liftMap C hf hT r,liftVertex_injective C hf hT r,
    liftMap_arrow_injective C hf hT r,lift_full C hf hT r,?_,?_⟩
  · intro v
    exact liftVertex_parity C hf hT r v
  · intro a
    rfl

end KroneckerDirectSumUniversalSupportEmbedding
end
end
end

