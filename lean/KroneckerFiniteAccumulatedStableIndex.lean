import KroneckerLabeledGraphForest
import KroneckerStablePositiveSupportConnected

section

/- Original module: KroneckerDeepBallAcyclic -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace TypedQuiver
open LabeledWalk

/-- The finite set of ALL actual outgoing arrows over a finite radius ball. -/
noncomputable def sourceBallFinset (Q : TypedQuiver) [Finite Q.A] (n r : ℕ)
    (u : (Q.iterate n).V) : Finset (Q.iterate n).A := by
  classical
  haveI := sourceBallArrow_finite Q n r u
  letI := Fintype.ofFinite (SourceBallArrow Q n r u)
  exact Finset.univ.image (fun a : SourceBallArrow Q n r u => a.val)

theorem sourceBallFinset_mem (Q : TypedQuiver) [Finite Q.A] (n r : ℕ)
    (u : (Q.iterate n).V) (a : (Q.iterate n).A) :
    a ∈ sourceBallFinset Q n r u ↔
      ∃p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u ((Q.iterate n).source a),
        Reduced p ∧ (labels p).length ≤ r := by
  classical
  simp only [sourceBallFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,rfl⟩; exact a.property
  · intro h; exact ⟨⟨a,h⟩,rfl⟩


/-- The actual induced radius-ball graph embeds into the actual arrow-restricted
quiver graph supported by ALL arrows whose source belongs to the ball. -/
noncomputable def ballToSourceSupport (Q : TypedQuiver) [Finite Q.A] (n r : ℕ)
    (u : (Q.iterate n).V) :
    vertexBallGraph (s:=(Q.iterate n).source) (t:=(Q.iterate n).target) u r →g
      underlyingGraph ((Q.iterate n).restrictArrows (sourceBallFinset Q n r u)).source
        ((Q.iterate n).restrictArrows (sourceBallFinset Q n r u)).target where
  toFun := Subtype.val
  map_rel' := by
    classical
    rintro v w ⟨hne,⟨⟨a,b⟩,hs,ht⟩⟩
    refine ⟨fun h => hne (Subtype.ext h),?_⟩
    have ha : a ∈ sourceBallFinset Q n r u := by
      apply (sourceBallFinset_mem Q n r u a).mpr
      cases b with
      | false =>
        change w.val = (Q.iterate n).source a at ht
        rw [←ht]
        exact w.property
      | true =>
        change v.val = (Q.iterate n).source a at hs
        rw [←hs]
        exact v.property
    exact ⟨(⟨a,ha⟩,b),hs,ht⟩

/-- An explicit arrow budget depending only on the ORIGINAL finite alphabet and
radius. It is uniform over every actual cover stage. -/
def ballArrowBudget (Q : TypedQuiver) [Fintype Q.A] (r : ℕ) : ℕ :=
  Fintype.card Q.A * ∑j : Fin (r+1), (2*Fintype.card Q.A)^j.val


end TypedQuiver
end KroneckerAbelianCover
end

/- Original module: KroneckerDeepBallTree -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}





end LabeledWalk
namespace TypedQuiver
open LabeledWalk


end TypedQuiver
end KroneckerAbelianCover
end

/- Original module: KroneckerFiniteRadiusTreeBridge -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace TypedQuiver
open LabeledWalk


/-- A common explicit stage budget for actual finite tree balls AND their
word-normal-form unfolding graph isomorphism. -/
def treeBridgeBudget (Q : TypedQuiver) [Fintype Q.A] (r : ℕ) : ℕ :=
  ballArrowBudget Q r + 2*r + 1

noncomputable def finiteRadiusTreeIso (Q : TypedQuiver) [Fintype Q.A] (r : ℕ)
    [DecidableEq (Q.iterate (treeBridgeBudget Q r + 1)).A]
    (u : (Q.iterate (treeBridgeBudget Q r + 1)).V) :
    pathBallGraph (s:=(Q.iterate (treeBridgeBudget Q r + 1)).source)
      (t:=(Q.iterate (treeBridgeBudget Q r + 1)).target) u r ≃g
    vertexBallGraph (s:=(Q.iterate (treeBridgeBudget Q r + 1)).source)
      (t:=(Q.iterate (treeBridgeBudget Q r + 1)).target) u r := by
  classical
  apply pathBallGraphIso (iterate_girth Q (treeBridgeBudget Q r)) _ u
  have h : treeBridgeBudget Q r < 2^(treeBridgeBudget Q r) := Nat.lt_two_pow_self
  dsimp [treeBridgeBudget] at h ⊢
  omega


end TypedQuiver
end KroneckerAbelianCover
end
end

section

/- Original module: KroneckerAccumulatedDeckBallTransport -/
section
/-! Accumulated deck maps identify exact finite-radius vertex balls. The radius
is preserved by actual walk transport and its inverse, so normalization does
not enlarge the support radius. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDeckBallTransport
open KroneckerAbelianCover LabeledWalk KroneckerAccumulatedCoverDeckActions
open KroneckerAccumulatedDeckWalkTransport
attribute [local instance] Classical.decEq Classical.propDecidable

theorem walk_length (Q : TypedQuiver) (n : ℕ) (f : Deck Q n) {u v : (Q.iterate n).V}
    (p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v) :
    (labels (walk Q n f p)).length = (labels p).length := by
  rw [walk,transport_labels,List.length_map]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem ball_membership (Q : TypedQuiver) (n B : ℕ) (f : Deck Q n) (u v : (Q.iterate n).V) :
    (∃ p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v,
      Reduced p ∧ (labels p).length ≤ B) ↔
    (∃ p : LabeledWalk (Q.iterate n).source (Q.iterate n).target
      (f.val.vertexEquiv u) (f.val.vertexEquiv v), Reduced p ∧ (labels p).length ≤ B) := by
  constructor
  · rintro ⟨p,hr,hp⟩
    exact ⟨walk Q n f p,(walk_reduced_iff Q n f p).mpr hr,by rwa [walk_length]⟩
  · rintro ⟨p,hr,hp⟩
    let q := castEndpoints (f.val.vertexEquiv.symm_apply_apply u) (f.val.vertexEquiv.symm_apply_apply v)
      (walk Q n (inverse f) p)
    refine ⟨q,?_,?_⟩
    · change List.IsChain _ (labels q)
      dsimp only [q]
      rw [labels_castEndpoints]
      exact (walk_reduced_iff Q n (inverse f) p).mpr hr
    · dsimp only [q]
      rw [labels_castEndpoints,walk_length]
      exact hp


end KroneckerAccumulatedDeckBallTransport
end
end

/- Original module: KroneckerIteratedRootedDimensionBound -/
section
/-! An explicit finite code for all dimensions supported in an iterated-cover
ball and bounded at every vertex. The bound depends only on the original
arrow alphabet, the radius and the coordinate bound, uniformly in cover depth. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerIteratedRootedDimensionBound
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver LabeledWalk
open KroneckerAccumulatedDeckRootTransitivity
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

def BallDimension (Q : TypedQuiver) (n B D : ℕ) (u : (Q.iterate n).V) :=
  {d : (Q.iterate n).V →₀ ℕ //
    (∀ v ∈ d.support, ∃ p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v,
      Reduced p ∧ (labels p).length ≤ B) ∧ ∀ v, d v ≤ D}

def code (Q : TypedQuiver) (n B D : ℕ) (u : (Q.iterate n).V) (d : BallDimension Q n B D u) :
    VertexBall (s:=(Q.iterate n).source) (t:=(Q.iterate n).target) u B → Fin (D+1) :=
  fun v => ⟨d.val v.val,Nat.lt_succ_of_le (d.property.2 v.val)⟩

theorem code_injective (Q : TypedQuiver) (n B D : ℕ) (u : (Q.iterate n).V) :
    Function.Injective (code Q n B D u) := by
  intro d e h
  apply Subtype.ext
  ext v
  by_cases hd : d.val v = 0
  · by_cases he : e.val v = 0
    · exact hd.trans he.symm
    · exact congrArg Fin.val (congrFun h ⟨v,e.property.1 v (Finsupp.mem_support_iff.mpr he)⟩)
  · exact congrArg Fin.val (congrFun h ⟨v,d.property.1 v (Finsupp.mem_support_iff.mpr hd)⟩)

theorem ballDimension_finite (Q : TypedQuiver) [Finite Q.A] (n B D : ℕ) (u : (Q.iterate n).V) :
    Finite (BallDimension Q n B D u) := by
  haveI := iterate_vertexBall_finite Q n B u
  exact Finite.of_injective (code Q n B D u) (code_injective Q n B D u)

def wordBudget (Q : TypedQuiver) [Fintype Q.A] (B : ℕ) : ℕ :=
  ∑ j : Fin (B+1), (2*Fintype.card Q.A)^j.val

theorem ballDimension_card_le (Q : TypedQuiver) [Fintype Q.A] (n B D : ℕ) (u : (Q.iterate n).V) :
    Nat.card (BallDimension Q n B D u) ≤ (D+1) ^ wordBudget Q B := by
  haveI := iterate_vertexBall_finite Q n B u
  haveI := ballDimension_finite Q n B D u
  have h := Nat.card_le_card_of_injective (code Q n B D u) (code_injective Q n B D u)
  rw [Nat.card_fun,Nat.card_fin] at h
  exact h.trans (Nat.pow_le_pow_right (by omega) (iterate_vertexBall_card_le Q n B u))

abbrev NormalizedIndex (Q : TypedQuiver) (n B D : ℕ) :=
  Σ v : Q.V, BallDimension Q n B D (zeroRoot Q n v)

theorem normalizedIndex_finite (Q : TypedQuiver) [Finite Q.V] [Finite Q.A] (n B D : ℕ) :
    Finite (NormalizedIndex Q n B D) := by
  let (v : Q.V) := ballDimension_finite Q n B D (zeroRoot Q n v)
  infer_instance

theorem normalizedIndex_card_le (Q : TypedQuiver) [Fintype Q.V] [Fintype Q.A] (n B D : ℕ) :
    Nat.card (NormalizedIndex Q n B D) ≤ Fintype.card Q.V * (D+1)^wordBudget Q B := by
  let (v : Q.V) := ballDimension_finite Q n B D (zeroRoot Q n v)
  let (v : Q.V) := Fintype.ofFinite (α:=BallDimension Q n B D (zeroRoot Q n v))
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  calc
    _ ≤ ∑ v : Q.V, (D+1)^wordBudget Q B := Finset.sum_le_sum (fun v _ => by
      simpa only [Nat.card_eq_fintype_card] using ballDimension_card_le Q n B D (zeroRoot Q n v))
    _ = _ := by simp

end KroneckerIteratedRootedDimensionBound
end
end

/- Original module: KroneckerIteratedSupportBall -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk

variable {V A : Type} [DecidableEq A] {s t : A → V}

/-- The positive vertex set of an arbitrary finitely supported dimension vector. -/
abbrev PositiveVertex (d : V →₀ ℕ) := {v : V // v ∈ d.support}

/-- The actual arrow graph induced on all positive-dimensional vertices. -/
def positiveSupportGraph (d : V →₀ ℕ) : SimpleGraph (PositiveVertex d) :=
  (underlyingGraph s t).induce (d.support : Set V)

/-- Inclusion of the positive-support graph into the full actual arrow graph. -/
def positiveSupportInclusion (d : V →₀ ℕ) :
    positiveSupportGraph (s:=s) (t:=t) d →g underlyingGraph s t where
  toFun := Subtype.val
  map_rel' h := h

noncomputable def positiveSupportPath (d : V →₀ ℕ)
    (hconn : (positiveSupportGraph (s:=s) (t:=t) d).Preconnected)
    (r w : PositiveVertex d) :
    (positiveSupportGraph (s:=s) (t:=t) d).Walk r w :=
  Classical.choose (hconn.exists_isPath r w)

theorem positiveSupportPath_isPath (d : V →₀ ℕ)
    (hconn : (positiveSupportGraph (s:=s) (t:=t) d).Preconnected)
    (r w : PositiveVertex d) :
    (positiveSupportPath d hconn r w).IsPath :=
  Classical.choose_spec (hconn.exists_isPath r w)

/-- The chosen simple support path uses fewer edges than there are positive vertices. -/
theorem positiveSupportPath_length_lt_card (d : V →₀ ℕ)
    (hconn : (positiveSupportGraph (s:=s) (t:=t) d).Preconnected)
    (r w : PositiveVertex d) :
    (positiveSupportPath d hconn r w).length < d.support.card := by
  have h := (positiveSupportPath_isPath d hconn r w).length_lt
  simpa only [Fintype.card_coe] using h

theorem consStep_labels (x : A × Bool) {u v w : V}
    (hs : stepStart s t x = u) (ht : stepEnd s t x = v)
    (p : LabeledWalk s t v w) :
    labels (consStep x hs ht p) = x :: labels p := by
  rcases x with ⟨a,b⟩
  cases b <;> dsimp [stepStart,stepEnd] at hs ht <;>
    subst u <;> subst v <;> rfl

/-- Lifting a graph walk by its genuine signed-arrow witnesses preserves length. -/
theorem ofGraph_label_length {u v : V} (p : (underlyingGraph s t).Walk u v) :
    (labels (ofGraph p)).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp only [ofGraph, consStep_labels, List.length_cons, SimpleGraph.Walk.length_cons]
      exact congrArg Nat.succ ih

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every vertex of a connected finite positive support lies in the actual radius ball
about any chosen positive root, once the radius bounds the support cardinality. -/
noncomputable def positiveSupportBallVertex (d : V →₀ ℕ)
    (hconn : (positiveSupportGraph (s:=s) (t:=t) d).Preconnected)
    (r : PositiveVertex d) (R : ℕ) (hcard : d.support.card ≤ R)
    (w : PositiveVertex d) : VertexBall (s:=s) (t:=t) r.val R := by
  let p := positiveSupportPath d hconn r w
  let q := p.map (positiveSupportInclusion (s:=s) (t:=t) d)
  refine ⟨w.val,(vertexBall_iff_walk r.val w.val R).mpr ⟨ofGraph q,?_⟩⟩
  rw [ofGraph_label_length,SimpleGraph.Walk.length_map]
  exact Nat.le_trans (Nat.le_of_lt (positiveSupportPath_length_lt_card d hconn r w)) hcard

@[simp] theorem positiveSupportBallVertex_val (d : V →₀ ℕ)
    (hconn : (positiveSupportGraph (s:=s) (t:=t) d).Preconnected)
    (r : PositiveVertex d) (R : ℕ) (hcard : d.support.card ≤ R)
    (w : PositiveVertex d) :
    (positiveSupportBallVertex d hconn r R hcard w).val = w.val := rfl

/-- The entire actual positive-support graph embeds in one finite radius ball. -/
noncomputable def positiveSupportToBall (d : V →₀ ℕ)
    (hconn : (positiveSupportGraph (s:=s) (t:=t) d).Preconnected)
    (r : PositiveVertex d) (R : ℕ) (hcard : d.support.card ≤ R) :
    positiveSupportGraph (s:=s) (t:=t) d →g vertexBallGraph (s:=s) (t:=t) r.val R where
  toFun := positiveSupportBallVertex d hconn r R hcard
  map_rel' := by
    intro u v h
    refine ⟨?_,h.2⟩
    intro huv
    have hval : u.val = v.val := congrArg
      (fun z : VertexBall (s:=s) (t:=t) r.val R ↦ z.val) huv
    exact h.1 hval


/-- Total dimension is a canonical radius for every connected positive support. -/
noncomputable def positiveSupportToTotalBall (d : V →₀ ℕ)
    (hconn : (positiveSupportGraph (s:=s) (t:=t) d).Preconnected)
    (r : PositiveVertex d) :
    positiveSupportGraph (s:=s) (t:=t) d →g
      vertexBallGraph (s:=s) (t:=t) r.val (d.sum (fun _ n ↦ n)) :=
  positiveSupportToBall d hconn r _
    (KroneckerBoundedCoverDimensions.support_card_le_total d)

end LabeledWalk
end KroneckerAbelianCover
end

/- Original module: KroneckerStableSupportRadiusBound -/
section
/-! Stable finite support is connected in the actual underlying arrow graph,
including for quivers with loops. Its total dimension bounds a genuine typed
walk radius around every positive root. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableSupportRadiusBound
open KroneckerAbelianCover LabeledWalk KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
attribute [local instance] Classical.decEq Classical.propDecidable

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

local instance supportQuiverFintype (Q : TypedQuiver) (d : Q.V →₀ ℕ) : Fintype (supportQuiver Q d).V :=
  supportFintype d

theorem stable_support_preconnected (Q : TypedQuiver) (d : Q.V →₀ ℕ)
    (R : Representation Q.source Q.target (fun v => d v)) (θ : Q.V → ℤ)
    (hR : FiniteSupportStable d θ R) :
    (positiveSupportGraph (s:=Q.source) (t:=Q.target) d).Preconnected := by
  apply stable_positive_support_preconnected (restrictToSupport Q d R) (supportCharacter d θ)
    ((finiteSupportStable_iff_restrict Q d θ R).mp hR)
  · intro v
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp v.property)
  · intro a _
    by_cases h : Q.source a.val = Q.target a.val
    · have he : (⟨Q.source a.val,a.property.1⟩ : PositiveVertex d) = ⟨Q.target a.val,a.property.2⟩ := Subtype.ext h
      change (positiveSupportGraph (s:=Q.source) (t:=Q.target) d).Reachable
        (⟨Q.source a.val,a.property.1⟩ : PositiveVertex d) ⟨Q.target a.val,a.property.2⟩
      rw [← he]
    · exact (show (positiveSupportGraph (s:=Q.source) (t:=Q.target) d).Adj
        ⟨Q.source a.val,a.property.1⟩ ⟨Q.target a.val,a.property.2⟩ from
          ⟨h,⟨(a.val,true),rfl,rfl⟩⟩).reachable

theorem stable_support_radius (Q : TypedQuiver) (d : Q.V →₀ ℕ)
    (R : Representation Q.source Q.target (fun v => d v)) (θ : Q.V → ℤ)
    (hR : FiniteSupportStable d θ R) (r : SupportVertex d) (B : ℕ)
    (hB : d.sum (fun _ n => n) ≤ B) (v : SupportVertex d) :
    ∃ p : LabeledWalk Q.source Q.target r.val v.val, Reduced p ∧ (labels p).length ≤ B := by
  exact (positiveSupportBallVertex d (stable_support_preconnected Q d R θ hR) r B
    ((KroneckerBoundedCoverDimensions.support_card_le_total d).trans hB) v).property

end KroneckerStableSupportRadiusBound
end
end

/- Original module: KroneckerStableAccumulatedBallNormalization -/
section
/-! A stable dimension of bounded total size has an accumulated translate in
one explicitly finite ball about a zero-character original root. Both its
support radius and every coordinate are bounded by the same total size. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableAccumulatedBallNormalization
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver LabeledWalk
open KroneckerFiniteQuiverHom KroneckerFiniteSupportStability
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerAccumulatedCoverDeckActions
open KroneckerAccumulatedDeckRootTransitivity KroneckerAccumulatedDeckBallTransport
open KroneckerStableSupportRadiusBound KroneckerIteratedRootedDimensionBound
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_bounded_normal_form (Q : TypedQuiver) (n B : ℕ)
    (d : (Q.iterate n).V →₀ ℕ) (hd : d ≠ 0) (hB : d.sum (fun _ k => k) ≤ B)
    (θ : (Q.iterate n).V → ℤ)
    (R : Representation (Q.iterate n).source (Q.iterate n).target (fun v => d v))
    (hR : FiniteSupportStable d θ R) :
    ∃ (f : Deck Q n) (i : NormalizedIndex Q n B B), i.2.val = pullDimension f.val d ∧
      i.2.val (zeroRoot Q n i.1) ≠ 0 := by
  obtain ⟨r,hr⟩ := Finsupp.support_nonempty_iff.mpr hd
  obtain ⟨g,hg⟩ := exists_normalizing_deck Q n r
  let f := inverse g
  let e := pullDimension f.val d
  refine ⟨f,⟨baseVertex Q n r,⟨e,?_,?_⟩⟩,rfl,?_⟩
  · intro v hv
    have hm : g.val.vertexEquiv.symm v ∈ d.support := by
      apply Finsupp.mem_support_iff.mpr
      change e v ≠ 0
      exact Finsupp.mem_support_iff.mp hv
    have hp := stable_support_radius (Q.iterate n) d R θ hR ⟨r,hr⟩ B hB
      ⟨g.val.vertexEquiv.symm v,hm⟩
    have hh := (ball_membership Q n B g r (g.val.vertexEquiv.symm v)).mp hp
    obtain ⟨p,hp,hl⟩ := hh
    refine ⟨castEndpoints hg (g.val.vertexEquiv.apply_symm_apply v) p,?_,?_⟩
    · simpa only [Reduced,labels_castEndpoints] using hp
    · simpa only [labels_castEndpoints] using hl
  · intro v
    exact (KroneckerBoundedCoverDimensions.coordinate_le_total d (f.val.vertexEquiv v)).trans hB

  · change e (zeroRoot Q n (baseVertex Q n r)) ≠ 0
    rw [← hg]
    change d (g.val.vertexEquiv.symm (g.val.vertexEquiv r)) ≠ 0
    rw [Equiv.symm_apply_apply]
    exact Finsupp.mem_support_iff.mp hr

end KroneckerStableAccumulatedBallNormalization
end
end

/- Original module: KroneckerFiniteAccumulatedStableIndex -/
section
/-! Finiteness and an explicit uniform bound for the dimension-vector deck
classes admitting stable finite-support representations in ANY iterated cover.
This concerns the localization index, not the number of representation or GIT
moduli points within each dimension class. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFiniteAccumulatedStableIndex
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver
open KroneckerFiniteQuiverHom KroneckerFiniteSupportStability
open KroneckerAccumulatedDimensionClasses KroneckerIteratedRootedDimensionBound
open KroneckerStableAccumulatedBallNormalization
attribute [local instance] Classical.decEq Classical.propDecidable

def StableIndex (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ) : Set (DimensionClass Q n) :=
  {q | ∃ (d : (Q.iterate n).V →₀ ℕ), d ≠ 0 ∧ d.sum (fun _ k => k) ≤ B ∧
    (∃ R : Representation (Q.iterate n).source (Q.iterate n).target (fun v => d v),
      FiniteSupportStable d (θ ∘ baseVertex Q n) R) ∧ Quotient.mk (dimensionSetoid Q n) d = q}

def indexClass (Q : TypedQuiver) (n B : ℕ) (i : NormalizedIndex Q n B B) : DimensionClass Q n :=
  Quotient.mk (dimensionSetoid Q n) i.2.val

theorem exists_index (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ)
    (q : StableIndex Q n B θ) : ∃ i : NormalizedIndex Q n B B, indexClass Q n B i = q.val := by
  obtain ⟨d,hd,hB,⟨R,hR⟩,hq⟩ := q.property
  obtain ⟨f,i,hi,_⟩ := exists_bounded_normal_form Q n B d hd hB _ R hR
  refine ⟨i,?_⟩
  have he : Quotient.mk (dimensionSetoid Q n) d = Quotient.mk (dimensionSetoid Q n) i.2.val :=
    Quotient.sound ⟨f,hi.symm⟩
  exact he.symm.trans hq

def indexCode (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ) (q : StableIndex Q n B θ) :
    NormalizedIndex Q n B B := Classical.choose (exists_index Q n B θ q)

theorem indexCode_injective (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ) :
    Function.Injective (indexCode Q n B θ) := by
  intro q r h
  apply Subtype.ext
  exact (Classical.choose_spec (exists_index Q n B θ q)).symm.trans
    ((congrArg (indexClass Q n B) h).trans (Classical.choose_spec (exists_index Q n B θ r)))

theorem stableIndex_finite (Q : TypedQuiver) [Finite Q.V] [Finite Q.A]
    (n B : ℕ) (θ : Q.V → ℤ) : Finite (StableIndex Q n B θ) := by
  haveI := normalizedIndex_finite Q n B B
  exact Finite.of_injective (indexCode Q n B θ) (indexCode_injective Q n B θ)

theorem stableIndex_card_le (Q : TypedQuiver) [Fintype Q.V] [Fintype Q.A]
    (n B : ℕ) (θ : Q.V → ℤ) :
    Nat.card (StableIndex Q n B θ) ≤ Fintype.card Q.V * (B+1)^wordBudget Q B := by
  haveI := normalizedIndex_finite Q n B B
  haveI := stableIndex_finite Q n B θ
  exact (Nat.card_le_card_of_injective _ (indexCode_injective Q n B θ)).trans
    (normalizedIndex_card_le Q n B B)

end KroneckerFiniteAccumulatedStableIndex
end
end
end

