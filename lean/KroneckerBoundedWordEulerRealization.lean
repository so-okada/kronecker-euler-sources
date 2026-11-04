import KroneckerDirectSumUniversalSupportEmbedding
import KroneckerFullSupportRepresentationTransport
import KroneckerUniversalSupportEuler

/- Original module: KroneckerBipartiteMoveTypedStep -/
section
/-! Every involutive color move is witnessed by an actual signed typed arrow
walk. Its color list is the prescribed singleton and its length is one, with
the incoming/outgoing orientation selected by the side of the base vertex. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerBipartiteMoveTypedStep
open KroneckerAbelianCover LabeledWalk KroneckerProperBipartiteQuiver KroneckerReducedColorWords
open KroneckerBipartiteCompleteColorFibers KroneckerBipartiteColorMoves
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (H : Complete C)

def step (c : Color) (v : Q.V) : LabeledWalk Q.source Q.target (move C H c v) v := by
  by_cases hs : C.side v = 0
  · let a := sourceArrow C H v hs c
    have hm : move C H c v = Q.target a := by unfold move; rw [dite_eq_left hs]
    exact castEndpoints hm.symm (sourceArrow_spec C H v hs c).1 (.backward a (.nil _))
  · have ht : C.side v = 1 := by have hh := C.side_lt v; omega
    let a := targetArrow C H v ht c
    have hm : move C H c v = Q.source a := by unfold move; rw [dite_eq_right hs]
    exact castEndpoints hm.symm (targetArrow_spec C H v ht c).1 (.forward a (.nil _))

def colorLabels {u v : Q.V} (p : LabeledWalk Q.source Q.target u v) : List Color :=
  (labels p).map (fun x => C.color x.1)

theorem step_colors (c : Color) (v : Q.V) : colorLabels C (step C H c v) = [c] := by
  unfold step colorLabels
  split_ifs
  · simp only [labels_castEndpoints,labels,List.map_cons,List.map_nil,(sourceArrow_spec C H _ _ c).2]
  · simp only [labels_castEndpoints,labels,List.map_cons,List.map_nil,(targetArrow_spec C H _ _ c).2]

theorem step_length (c : Color) (v : Q.V) : (labels (step C H c v)).length = 1 := by
  have h := congrArg List.length (step_colors C H c v)
  simpa only [colorLabels,List.length_map,List.length_singleton] using h

theorem colorLabels_append {u v w : Q.V} (p : LabeledWalk Q.source Q.target u v)
    (q : LabeledWalk Q.source Q.target v w) : colorLabels C (append p q) = colorLabels C p ++ colorLabels C q := by
  simp only [colorLabels,labels_append,List.map_append]

end KroneckerBipartiteMoveTypedStep
end
end

/- Original module: KroneckerReducedColorEvaluationPaths -/
section
/-! A color list evaluating a vertex has an actual typed walk from that vertex
back to the chosen root. The walk's color list and length are exactly the
input list. Reduced color words give reduced typed walks, independently of
any global injectivity or acyclicity of the target quiver. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReducedColorEvaluationPaths
open KroneckerAbelianCover LabeledWalk KroneckerProperBipartiteQuiver KroneckerReducedColorWords
open KroneckerBipartiteCompleteColorFibers KroneckerBipartiteColorMoves
open KroneckerColorMoveWordEvaluation KroneckerBipartiteMoveTypedStep
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (H : Complete C)

def evalPath (u : Q.V) : (l : List Color) → LabeledWalk Q.source Q.target (evalList C H l u) u
  | [] => .nil u
  | c::l => append (step C H c (evalList C H l u)) (evalPath u l)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem evalPath_colors (u : Q.V) (l : List Color) : colorLabels C (evalPath C H u l) = l := by
  induction l with
  | nil => rfl
  | cons c l ih => rw [evalPath,colorLabels_append,step_colors,ih,List.singleton_append]

theorem evalPath_length (u : Q.V) (l : List Color) : (labels (evalPath C H u l)).length = l.length := by
  have h := congrArg List.length (evalPath_colors C H u l)
  simpa only [colorLabels,List.length_map] using h

theorem reduced_of_colors {u v : Q.V} (p : LabeledWalk Q.source Q.target u v)
    (h : KroneckerReducedColorWords.Reduced (colorLabels C p)) : LabeledWalk.Reduced p := by
  change List.IsChain (fun x y : Q.A × Bool => x.1 ≠ y.1 ∨ x.2 = y.2) (labels p)
  change List.IsChain (fun a b => a ≠ b) ((labels p).map (fun x => C.color x.1)) at h
  rw [List.isChain_map] at h
  exact h.imp (fun x y hxy => Or.inl (fun he => hxy (congrArg C.color he)))

theorem evalPath_reduced (u : Q.V) (w : Word) : LabeledWalk.Reduced (evalPath C H u w.val) := by
  apply reduced_of_colors
  rw [evalPath_colors]
  exact w.property

theorem colorLabels_cast {u v u' v' : Q.V} (hu : u = u') (hv : v = v')
    (p : LabeledWalk Q.source Q.target u v) : colorLabels C (castEndpoints hu hv p) = colorLabels C p := by
  simp only [colorLabels,labels_castEndpoints]

end KroneckerReducedColorEvaluationPaths
end
end

/- Original module: KroneckerBoundedWordEvaluationInjectivity -/
section
/-! Two reduced color words evaluating to the same vertex agree whenever their
combined lengths are below the actual target girth. This proves injectivity
on bounded word balls from genuine typed walks and their exact color lists;
global injectivity at finite cover depth is not asserted. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerBoundedWordEvaluationInjectivity
open KroneckerAbelianCover LabeledWalk KroneckerProperBipartiteQuiver KroneckerReducedColorWords
open KroneckerBipartiteCompleteColorFibers KroneckerColorMoveWordEvaluation
open KroneckerBipartiteMoveTypedStep KroneckerReducedColorEvaluationPaths
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (H : Complete C)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem words_eq_below_girth (g : ℕ) (hg : ReducedGirthBound Q.source Q.target g)
    (u : Q.V) (w z : Word) (h : eval C H u w = eval C H u z)
    (hlen : w.val.length + z.val.length < g) : w = z := by
  let p := evalPath C H u w.val
  let q := castEndpoints h.symm rfl (evalPath C H u z.val)
  have hp : LabeledWalk.Reduced p := evalPath_reduced C H u w
  have hq : LabeledWalk.Reduced q := by
    simpa only [q,LabeledWalk.Reduced,labels_castEndpoints] using evalPath_reduced C H u z
  have he := reduced_paths_unique_below_girth hg p q hp hq (by
    simpa only [p,q,labels_castEndpoints,evalPath_length] using hlen)
  apply Subtype.ext
  have hc := congrArg (colorLabels C) he
  simpa only [p,q,colorLabels_cast,evalPath_colors] using hc

theorem eval_injective_on_ball (g B : ℕ) (hg : ReducedGirthBound Q.source Q.target g)
    (hB : 2*B < g) (u : Q.V) : Set.InjOn (eval C H u) {w : Word | w.val.length ≤ B} := by
  intro w hw z hz h
  exact words_eq_below_girth C H g hg u w z h (by
    change w.val.length ≤ B at hw
    change z.val.length ≤ B at hz
    omega)

end KroneckerBoundedWordEvaluationInjectivity
end
end

/- Original module: KroneckerBoundedEvaluationEmbedding -/
section
/-! Evaluation on a finite full word support is injective on vertices and
actual colored arrows under the sharp combined-word girth bound. The domain
contains all arrows with both endpoints in the support. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerBoundedEvaluationEmbedding
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerReducedColorWords
open KroneckerBipartiteCompleteColorFibers KroneckerColorMoveWordEvaluation
open KroneckerUniversalWordEvaluationQuiver KroneckerBoundedWordEvaluationInjectivity
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportFullInclusion
open KroneckerTypedQuiverMaps KroneckerFiniteSupportDeckRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (H : Complete C) (u : Q.V) (hu : C.side u = 0)

def supportMap (d : Word →₀ ℕ) : QuiverMap (supportQuiver coloredCoverQuiver d) Q :=
  (inclusion coloredCoverQuiver d).comp (evaluationMap C H u hu)

theorem vertex_injective (d : Word →₀ ℕ) (B g : ℕ)
    (hb : ∀ w ∈ d.support, w.val.length ≤ B)
    (hg : LabeledWalk.ReducedGirthBound Q.source Q.target g) (hB : 2*B < g) :
    Function.Injective (supportMap C H u hu d).vertex := by
  intro w z he
  exact Subtype.ext (eval_injective_on_ball C H g B hg hB u (hb _ w.property) (hb _ z.property) he)

theorem arrow_injective (d : Word →₀ ℕ)
    (hv : Function.Injective (supportMap C H u hu d).vertex) :
    Function.Injective (supportMap C H u hu d).arrow := by
  intro a b h
  have hc : a.val.1 = b.val.1 := by
    have hh := congrArg C.color h
    exact (evaluation_color C H u hu a.val).symm.trans (hh.trans (evaluation_color C H u hu b.val))
  have hs := hv (((supportMap C H u hu d).source a).symm.trans
    ((congrArg Q.source h).trans ((supportMap C H u hu d).source b)))
  apply Subtype.ext
  apply Prod.ext hc
  exact Subtype.ext (congrArg (fun v : SupportVertex d => v.val) hs)

end KroneckerBoundedEvaluationEmbedding
end
end

/- Original module: KroneckerBoundedEvaluationFullness -/
section
/-! A slightly larger girth bound makes bounded evaluation FULL on its
vertex image. Every target arrow with endpoints in the evaluated support is
the image of the unique original colored arrow, including its orientation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerBoundedEvaluationFullness
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerReducedColorWords
open KroneckerBipartiteCompleteColorFibers KroneckerColorMoveWordEvaluation
open KroneckerUniversalWordEvaluationQuiver KroneckerBoundedWordEvaluationInjectivity
open KroneckerFiniteSupportInducedQuiver KroneckerBoundedEvaluationEmbedding
open KroneckerTypedQuiverMaps KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFullImageQuiverEmbedding KroneckerWordParity
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (H : Complete C) (u : Q.V) (hu : C.side u = 0)

theorem supportMap_full (d : Word →₀ ℕ) (B g : ℕ)
    (hb : ∀ w ∈ d.support, w.val.length ≤ B)
    (hg : LabeledWalk.ReducedGirthBound Q.source Q.target g) (hB : 2*B+1 < g) :
    FullOnImage (supportMap C H u hu d) := by
  intro a w z hs ht
  have hw : parity w.val = 0 := by
    have he := evaluation_side C H u hu w.val
    change Q.source a = eval C H u w.val at hs
    rw [← hs,C.source_side] at he
    exact he.symm
  let b : coloredCoverQuiver.A := (C.color a,⟨w.val,hw⟩)
  have he : (evaluationMap C H u hu).arrow b = a := by
    apply C.source_injective
    · exact evaluation_color C H u hu b
    · exact ((evaluationMap C H u hu).source b).trans hs.symm
  have hz : toggle (C.color a) w.val = z.val := by
    apply words_eq_below_girth C H g hg u
    · exact ((evaluationMap C H u hu).target b).symm.trans ((congrArg Q.target he).trans ht)
    · have h₁ := hb w.val w.property
      have h₂ := hb z.val z.property
      have h₃ := toggle_length (C.color a) w.val
      omega
  refine ⟨⟨b,w.property,?_⟩,he⟩
  change toggle (C.color a) w.val ∈ d.support
  exact hz.symm ▸ z.property

end KroneckerBoundedEvaluationFullness
end
end

/- Original module: KroneckerDirectSumBoundedWordEmbedding -/
section
/-! The same explicit depth3B+1 used for direct-sum support forests also
embeds every word support in the radius-B ball fully into the direct-sum
iterate. Both directions therefore use one common depth, with an explicit
exponential girth estimate and exact actual-arrow injectivity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumBoundedWordEmbedding
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerReducedColorWords
open KroneckerDirectSumUniversalSupportEmbedding KroneckerDirectSumWordEvaluation
open KroneckerDirectSumCompleteColorFibers KroneckerBoundedEvaluationEmbedding
open KroneckerBoundedEvaluationFullness KroneckerFiniteSupportInducedQuiver
open KroneckerTypedQuiverMaps KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFullImageQuiverEmbedding
attribute [local instance] Classical.decEq Classical.propDecidable

theorem depth_girth (B : ℕ) :
    LabeledWalk.ReducedGirthBound (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)).source
      (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)).target (2^(3*B)+2) := by
  rw [depth_eq]
  exact KroneckerDirectSumIteratedGirth.iterate_girth baseQuiver (3*B)

theorem depth_girth_bound (B : ℕ) : 2*B+1 < 2^(3*B)+2 := by
  have : 3*B < 2^(3*B) := Nat.lt_two_pow_self
  omega

def boundedMap (B : ℕ) (d : Word →₀ ℕ) :
    QuiverMap (supportQuiver coloredCoverQuiver d) (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)) :=
  supportMap (KroneckerDirectSumBaseColoring.coloring (depth B)) (coloring_complete (depth B))
    (sourceRoot (depth B)) (sourceRoot_side (depth B)) d

theorem boundedMap_embedding (B : ℕ) (d : Word →₀ ℕ) (hb : ∀ w ∈ d.support, w.val.length ≤ B) :
    Function.Injective (boundedMap B d).vertex ∧ Function.Injective (boundedMap B d).arrow ∧ FullOnImage (boundedMap B d) := by
  have hv := vertex_injective (KroneckerDirectSumBaseColoring.coloring (depth B)) (coloring_complete (depth B))
    (sourceRoot (depth B)) (sourceRoot_side (depth B)) d B _ hb (depth_girth B) (by have := depth_girth_bound B; omega)
  exact ⟨hv,arrow_injective _ _ _ _ _ hv,supportMap_full _ _ _ _ d B _ hb (depth_girth B) (depth_girth_bound B)⟩

end KroneckerDirectSumBoundedWordEmbedding
end
end

/- Original module: KroneckerBoundedWordRepresentationRealization -/
section
/-! Every actual universal-word representation supported in the radius-B
ball has a full faithful realization at direct-sum depth3B+1. All matrices,
original source/sink multiplicities, total dimension and King stability are
transported together, without any tree-shaped matrix sparsity assumption. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerBoundedWordRepresentationRealization
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
open KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerFullSupportRepresentationTransport KroneckerDirectSumBoundedWordEmbedding
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_direct_realization (B : ℕ) (S : SupportedRepresentation coloredCoverQuiver)
    (hb : ∀ w ∈ S.1.support, w.val.length ≤ B) (θ : Fin 2 → ℤ) :
    ∃ T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)),
      (T.1 = 0 ↔ S.1 = 0) ∧ T.1.sum (fun _ k => k) = S.1.sum (fun _ k => k) ∧
      T.1.mapDomain (KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B)) =
        S.1.mapDomain KroneckerUniversalWordBaseProjection.baseVertex ∧
      (FiniteSupportStable T.1 (θ ∘ KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B)) T.2 ↔
        FiniteSupportStable S.1 (θ ∘ KroneckerUniversalWordBaseProjection.baseVertex) S.2) ∧
      (∀ v, T.1 ((boundedMap B S.1).vertex v) = S.1 v.val) ∧
      (∀ a, T.2.arrow ((boundedMap B S.1).arrow a) ≍ S.2.arrow a.val) := by
  obtain ⟨hv,ha,hf⟩ := boundedMap_embedding B S.1 hb
  let f := boundedMap B S.1
  have hbase : ∀ v, KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B) (f.vertex v) =
      KroneckerUniversalWordBaseProjection.baseVertex v.val := fun v =>
    KroneckerDirectSumWordEvaluation.wordMap_base (depth B) v.val
  exact ⟨transport S f hv ha hf,transport_zero_iff S f hv ha hf,transport_sum S f hv ha hf,
    transport_original_dimension S f hv ha hf _ _ hbase,
    transport_stable_iff S f hv ha hf _ _ (fun v => congrArg θ (hbase v)),
    transport_dimension S f hv ha hf,transport_arrow S f hv ha hf⟩

end KroneckerBoundedWordRepresentationRealization
end
end

/- Original module: KroneckerFullSupportEulerTransport -/
section
/-! Transport of an actual representation through a full support embedding
preserves its self-Euler form exactly. The proof passes through the full
restricted representation and cancels restriction/extension, retaining every
actual arrow contribution and all positive vertex multiplicities. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullSupportEulerTransport
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerFullImagePushforward KroneckerFullImageNumericalTransport
open KroneckerFiniteSupportFullInclusion KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportEulerTransport
open KroneckerFullSupportRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable

theorem transport_selfEuler {Q W : TypedQuiver} (S : SupportedRepresentation Q)
    (f : QuiverMap (supportQuiver Q S.1) W) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    [Finite (SupportArrow Q.source Q.target S.1)]
    [Finite (SupportArrow W.source W.target (transport S f hv ha hf).1)] :
    supportEuler W (transport S f hv ha hf).1 = supportEuler Q S.1 := by
  let P := supportQuiver Q S.1
  let : Finite P.A := inferInstanceAs (Finite (SupportArrow Q.source Q.target S.1))
  let : Finite (SupportArrow W.source W.target (push f hv ha hf (restricted Q S)).1) :=
    inferInstanceAs (Finite (SupportArrow W.source W.target (transport S f hv ha hf).1))
  have h₁ := push_selfEuler f hv ha hf (restricted Q S)
  let i := inclusion Q S.1
  let X := push i Subtype.val_injective Subtype.val_injective (inclusion_full Q S.1) (restricted Q S)
  have hx : X = S := push_restricted Q S
  let : Finite (SupportArrow Q.source Q.target X.1) := by rw [hx]; infer_instance
  have h₂ := push_selfEuler i Subtype.val_injective Subtype.val_injective (inclusion_full Q S.1) (restricted Q S)
  exact h₁.symm.trans (h₂.trans (supportEuler_congr X.1 S.1 (congrArg Sigma.fst hx)))

end KroneckerFullSupportEulerTransport
end
end

/- Original module: KroneckerBoundedWordEulerRealization -/
section
/-! Bounded word realization preserves the self-Euler form as well as the
actual stable representation. This adds the numerical invariant needed for
positive-Euler index restrictions to the direct-sum realization theorem. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerBoundedWordEulerRealization
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability KroneckerFiniteSupportEulerTransport
open KroneckerFullSupportRepresentationTransport KroneckerDirectSumBoundedWordEmbedding
attribute [local instance] Classical.decEq Classical.propDecidable

instance directSupportFinite (n : ℕ) (d : (KroneckerDirectSumIteratedGirth.iterate baseQuiver n).V →₀ ℕ) :
    Finite (SupportArrow (KroneckerDirectSumIteratedGirth.iterate baseQuiver n).source
      (KroneckerDirectSumIteratedGirth.iterate baseQuiver n).target d) :=
  KroneckerProperColoringFiniteSupportArrows.support_arrows_finite (KroneckerDirectSumBaseColoring.coloring n) d

theorem exists_direct_euler_realization (B : ℕ) (S : SupportedRepresentation coloredCoverQuiver)
    (hb : ∀ w ∈ S.1.support, w.val.length ≤ B) (θ : Fin 2 → ℤ) :
    ∃ T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)),
      (T.1 = 0 ↔ S.1 = 0) ∧ T.1.sum (fun _ k => k) = S.1.sum (fun _ k => k) ∧
      T.1.mapDomain (KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B)) =
        S.1.mapDomain KroneckerUniversalWordBaseProjection.baseVertex ∧
      (FiniteSupportStable T.1 (θ ∘ KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B)) T.2 ↔
        FiniteSupportStable S.1 (θ ∘ KroneckerUniversalWordBaseProjection.baseVertex) S.2) ∧
      supportEuler (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)) T.1 = supportEuler coloredCoverQuiver S.1 := by
  obtain ⟨hv,ha,hf⟩ := boundedMap_embedding B S.1 hb
  let f := boundedMap B S.1
  have hbase : ∀ v, KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B) (f.vertex v) =
      KroneckerUniversalWordBaseProjection.baseVertex v.val := fun v =>
    KroneckerDirectSumWordEvaluation.wordMap_base (depth B) v.val
  exact ⟨transport S f hv ha hf,transport_zero_iff S f hv ha hf,transport_sum S f hv ha hf,
    transport_original_dimension S f hv ha hf _ _ hbase,
    transport_stable_iff S f hv ha hf _ _ (fun v => congrArg θ (hbase v)),
    KroneckerFullSupportEulerTransport.transport_selfEuler S f hv ha hf⟩

end KroneckerBoundedWordEulerRealization
end
end
