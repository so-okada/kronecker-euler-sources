import KroneckerQuiverImageWalkLifting
import KroneckerDirectSumBaseColoring
import KroneckerUniversalWordEvaluationQuiver
import KroneckerUniversalWordBaseProjection

section

/-! Every connected family in a product-model iterated cover has an accumulated
translate inside the precise iterated direct-sum cover. This proves component
adequacy after root normalization, without equating the ambient vertex sets. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumRootComponentBridge
open KroneckerAbelianCover LabeledWalk KroneckerTypedQuiverMaps
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumEmbeddingLocalLifts
open KroneckerQuiverImageWalkLifting KroneckerDirectSumCoverEmbeddingLift
open KroneckerAccumulatedCoverDeckActions KroneckerAccumulatedDeckRootTransitivity
open KroneckerAccumulatedDeckWalkTransport
attribute [local instance] Classical.decEq Classical.propDecidable

def directRoot (Q : TypedQuiver) : (n : ℕ) → Q.V → (KroneckerDirectSumIteratedGirth.iterate Q n).V
  | 0,v => v
  | n+1,v => (directRoot Q n v,0)

theorem embedding_directRoot (Q : TypedQuiver) (n : ℕ) (v : Q.V) :
    (embedding Q n).vertex (directRoot Q n v) = zeroRoot Q n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · exact ih
    · change ((Finsupp.mapDomain (embedding Q n).arrow (0 : (KroneckerDirectSumIteratedGirth.iterate Q n).A →₀ ℤ)) : _ → ℤ) = 0
      rw [Finsupp.mapDomain_zero]
      rfl

theorem root_component_in_image (Q : TypedQuiver) (n : ℕ) (v : Q.V)
    {w : (Q.iterate n).V}
    (p : LabeledWalk (Q.iterate n).source (Q.iterate n).target (zeroRoot Q n v) w) :
    w ∈ Set.range (embedding Q n).vertex :=
  image_closed_under_walk _ (embedding_locallySurjective Q n) p
    ⟨directRoot Q n v,embedding_directRoot Q n v⟩

theorem normalize_connected_family (Q : TypedQuiver) (n : ℕ) {I : Type}
    (u : (Q.iterate n).V) (x : I → (Q.iterate n).V)
    (hc : ∀ i, Nonempty (LabeledWalk (Q.iterate n).source (Q.iterate n).target u (x i))) :
    ∃ f : Deck Q n, f.val.vertexEquiv u = zeroRoot Q n (TypedQuiver.baseVertex Q n u) ∧
      ∀ i, f.val.vertexEquiv (x i) ∈ Set.range (embedding Q n).vertex := by
  obtain ⟨f,hf⟩ := exists_normalizing_deck Q n u
  refine ⟨f,hf,?_⟩
  intro i
  obtain ⟨p⟩ := hc i
  exact root_component_in_image Q n _ (castEndpoints hf rfl (KroneckerAccumulatedDeckWalkTransport.walk Q n f p))

end KroneckerDirectSumRootComponentBridge
end
end

section

/- Original module: KroneckerDirectSumCompleteColorFibers -/
section
/-! Every direct-sum cover stage has unique actual source and target lifts of
each original arrow. Incoming lifting subtracts that actual preceding-stage
arrow's finite unit character. Thus the three-arrow tower has complete proper
color fibers at all depths, without a product-character existence assumption. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumCompleteColorFibers
open KroneckerAbelianCover KroneckerDirectSumIteratedEmbedding
open KroneckerDirectSumBaseColoring KroneckerThreeArrowBaseQuiver
open KroneckerBipartiteCompleteColorFibers
attribute [local instance] Classical.decEq Classical.propDecidable

theorem source_fiber (Q : TypedQuiver) (n : ℕ) (a : Q.A)
    (v : (KroneckerDirectSumIteratedGirth.iterate Q n).V) (hv : Q.source a = baseVertex Q n v) :
    ∃ b : (KroneckerDirectSumIteratedGirth.iterate Q n).A,
      baseArrow Q n b = a ∧ (KroneckerDirectSumIteratedGirth.iterate Q n).source b = v := by
  induction n with
  | zero => exact ⟨a,rfl,hv⟩
  | succ n ih =>
    obtain ⟨b,hb,hs⟩ := ih v.1 hv
    refine ⟨(b,v.2),hb,?_⟩
    apply Prod.ext
    · exact hs
    · rfl

theorem target_fiber (Q : TypedQuiver) (n : ℕ) (a : Q.A)
    (v : (KroneckerDirectSumIteratedGirth.iterate Q n).V) (hv : Q.target a = baseVertex Q n v) :
    ∃ b : (KroneckerDirectSumIteratedGirth.iterate Q n).A,
      baseArrow Q n b = a ∧ (KroneckerDirectSumIteratedGirth.iterate Q n).target b = v := by
  induction n with
  | zero => exact ⟨a,rfl,hv⟩
  | succ n ih =>
    obtain ⟨b,hb,ht⟩ := ih v.1 hv
    refine ⟨(b,v.2-Finsupp.single b 1),hb,?_⟩
    apply Prod.ext
    · exact ht
    · exact sub_add_cancel _ _



theorem coloring_complete (n : ℕ) : Complete (KroneckerDirectSumBaseColoring.coloring n) := by
  constructor
  · intro v hv c
    obtain ⟨a,ha,hs⟩ := source_fiber baseQuiver n c v (Fin.ext hv.symm)
    exact ⟨a,hs,ha⟩
  · intro v hv c
    obtain ⟨a,ha,ht⟩ := target_fiber baseQuiver n c v (Fin.ext hv.symm)
    exact ⟨a,ht,ha⟩

end KroneckerDirectSumCompleteColorFibers
end
end

/- Original module: KroneckerDirectSumWordEvaluation -/
section
/-! The universal colored-word quiver has a concrete color-preserving
projection to EVERY genuine direct-sum iterate, based at its zero-character
source root. The original source/sink projection is exactly word parity. This
map is global; injectivity will be proved only on sufficiently small supports. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumWordEvaluation
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumBaseColoring
open KroneckerDirectSumCompleteColorFibers KroneckerDirectSumRootComponentBridge
open KroneckerDirectSumIteratedEmbedding KroneckerUniversalWordEvaluationQuiver
open KroneckerTypedQuiverMaps KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerReducedColorWords
attribute [local instance] Classical.decEq Classical.propDecidable

theorem directRoot_base (Q : TypedQuiver) (n : ℕ) (v : Q.V) : baseVertex Q n (directRoot Q n v) = v := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

def sourceRoot (n : ℕ) : (KroneckerDirectSumIteratedGirth.iterate baseQuiver n).V :=
  directRoot baseQuiver n (0 : Fin 2)

set_option backward.isDefEq.respectTransparency false in
theorem sourceRoot_side (n : ℕ) : (KroneckerDirectSumBaseColoring.coloring n).side (sourceRoot n) = 0 := by
  change (baseVertex baseQuiver n (directRoot baseQuiver n (0 : Fin 2))).val = 0
  rw [directRoot_base]
  rfl

def wordMap (n : ℕ) : QuiverMap coloredCoverQuiver (KroneckerDirectSumIteratedGirth.iterate baseQuiver n) :=
  evaluationMap (KroneckerDirectSumBaseColoring.coloring n) (coloring_complete n) (sourceRoot n) (sourceRoot_side n)

theorem wordMap_base (n : ℕ) (w : Word) :
    baseVertex baseQuiver n ((wordMap n).vertex w) = KroneckerUniversalWordBaseProjection.baseVertex w :=
  Fin.ext (evaluation_side (KroneckerDirectSumBaseColoring.coloring n) (coloring_complete n)
    (sourceRoot n) (sourceRoot_side n) w)

theorem wordMap_color (n : ℕ) (a : coloredCoverQuiver.A) : baseArrow baseQuiver n ((wordMap n).arrow a) = a.1 :=
  evaluation_color (KroneckerDirectSumBaseColoring.coloring n) (coloring_complete n) (sourceRoot n) (sourceRoot_side n) a


end KroneckerDirectSumWordEvaluation
end
end
end

