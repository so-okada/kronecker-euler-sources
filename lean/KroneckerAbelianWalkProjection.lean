import KroneckerBoundedCoverDimensions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Int.Interval

/- Original module: KroneckerAbelianCoverWalks -/
section
/-! The actual universal abelian cover of a finite-arrow quiver, with its
coordinate displacement bound for arbitrary unoriented walks. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
variable {V A : Type} [DecidableEq A]
abbrev Character (A : Type) := A → ℤ
abbrev Vertex (V A : Type) := V × Character A
noncomputable def unit (a : A) : Character A := Pi.single a 1
variable (s t : A → V)
def arrowSource (e : A × Character A) : Vertex V A := (s e.1, e.2)
noncomputable def arrowTarget (e : A × Character A) : Vertex V A :=
  (t e.1, e.2 + unit e.1)

def Oriented (u v : Vertex V A) : Prop :=
  ∃ a : A, u.1 = s a ∧ v.1 = t a ∧ v.2 = u.2 + unit a

noncomputable def graph : SimpleGraph (Vertex V A) where
  Adj u v := u ≠ v ∧ (Oriented s t u v ∨ Oriented s t v u)
  symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

theorem oriented_ne {u v : Vertex V A} (h : Oriented s t u v) : u ≠ v := by
  rintro rfl
  obtain ⟨a,_,_,h⟩ := h
  have hh := congrFun h a
  simp [unit] at hh

theorem arrow_is_edge (e : A × Character A) :
    (graph s t).Adj (arrowSource s e) (arrowTarget t e) := by
  have h : Oriented s t (arrowSource s e) (arrowTarget t e) := ⟨e.1,rfl,rfl,rfl⟩
  exact ⟨oriented_ne s t h, Or.inl h⟩

/-- Every arrow or reversed arrow moves each character coordinate by at most one. -/
theorem adjacency_coordinate_bound {u v : Vertex V A} (h : (graph s t).Adj u v)
    (a : A) : u.2 a - 1 ≤ v.2 a ∧ v.2 a ≤ u.2 a + 1 := by
  rcases h.2 with ⟨b,_,_,hb⟩ | ⟨b,_,_,hb⟩
  · have hh := congrFun hb a
    simp only [Pi.add_apply,unit,Pi.single_apply] at hh
    split_ifs at hh <;> omega
  · have hh := congrFun hb a
    simp only [Pi.add_apply,unit,Pi.single_apply] at hh
    split_ifs at hh <;> omega

/-- This bound is for actual walks in the abelian cover, not a tree surrogate. -/
theorem walk_coordinate_bound {u v : Vertex V A} (p : (graph s t).Walk u v)
    (a : A) : u.2 a - (p.length : ℤ) ≤ v.2 a ∧
      v.2 a ≤ u.2 a + (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have he := adjacency_coordinate_bound s t h a
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

/-- Translation changes every character by the same vector and preserves colors. -/
def translate (ξ : Character A) : Vertex V A ≃ Vertex V A where
  toFun w := (w.1,w.2 + ξ)
  invFun w := (w.1,w.2 - ξ)
  left_inv w := by simp
  right_inv w := by simp

theorem oriented_translate (ξ : Character A) (u v : Vertex V A) :
    Oriented s t (translate ξ u) (translate ξ v) ↔ Oriented s t u v := by
  constructor <;> rintro ⟨a,hs,ht,ha⟩ <;> refine ⟨a,hs,ht,?_⟩
  · change v.2 + ξ = (u.2 + ξ) + unit a at ha
    apply add_right_cancel (b := ξ)
    simpa only [add_assoc,add_comm ξ (unit a)] using ha
  · change v.2 + ξ = (u.2 + ξ) + unit a
    rw [ha]
    abel

noncomputable def translationGraphIso (ξ : Character A) : graph s t ≃g graph s t where
  toEquiv := translate ξ
  map_rel_iff' := by
    intro u v
    simp only [graph,ne_eq,Equiv.apply_eq_iff_eq,
      oriented_translate]

end KroneckerAbelianCover
end

/- Original module: KroneckerAbelianArrowLifting -/
section
/-! Local lifting for the actual colored quiver, retaining parallel original
arrows and loops. This is not a claim about the collapsed base simple graph. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
variable {V A : Type} [DecidableEq A] (s t : A → V)

def vertexProjection : Vertex V A → V := Prod.fst
def arrowProjection : A × Character A → A := Prod.fst

theorem projection_source (e : A × Character A) :
    vertexProjection (arrowSource s e) = s (arrowProjection e) := rfl

theorem projection_target (e : A × Character A) :
    vertexProjection (arrowTarget t e) = t (arrowProjection e) := rfl

/-- Fix an original arrow and a cover vertex over its source. There is exactly
one lift of that arrow with this source. -/
theorem unique_source_lift (a : A) (w : Vertex V A) (h : w.1 = s a) :
    ∃! e : A × Character A, arrowProjection e = a ∧ arrowSource s e = w := by
  refine ⟨(a,w.2),⟨rfl,?_⟩,?_⟩
  · exact Prod.ext h.symm rfl
  · intro e he
    exact Prod.ext he.1 (congrArg (fun z : Vertex V A => z.2) he.2)

/-- Target lifting uses subtraction of the arrow's character, so it also works
for original loops and parallel arrows without collapsing their labels. -/
theorem unique_target_lift (a : A) (w : Vertex V A) (h : w.1 = t a) :
    ∃! e : A × Character A, arrowProjection e = a ∧ arrowTarget t e = w := by
  refine ⟨(a,w.2-unit a),⟨rfl,?_⟩,?_⟩
  · apply Prod.ext h.symm
    simp [arrowTarget]
  · intro e he
    apply Prod.ext he.1
    have hc := congrArg (fun z : Vertex V A => z.2) he.2
    change e.2 + unit e.1 = w.2 at hc
    have he1 : e.1 = a := he.1
    rw [he1] at hc
    exact eq_sub_iff_add_eq.mpr hc

end KroneckerAbelianCover
end

/- Original module: KroneckerAbelianLabeledWalkLift -/
section
/-! Signed labeled walks retain orientations and every original arrow. Their
lifts close precisely when every arrow has equal forward/backward multiplicity. -/
set_option autoImplicit false
namespace KroneckerAbelianCover

inductive LabeledWalk {V A : Type} (s t : A → V) : V → V → Type
  | nil (v : V) : LabeledWalk s t v v
  | forward (a : A) {v : V} (p : LabeledWalk s t (t a) v) : LabeledWalk s t (s a) v
  | backward (a : A) {v : V} (p : LabeledWalk s t (s a) v) : LabeledWalk s t (t a) v

variable {V A : Type} [DecidableEq A] {s t : A → V}
namespace LabeledWalk
noncomputable def displacement {u v : V} : LabeledWalk s t u v → Character A
  | .nil _ => 0
  | .forward a p => unit a + displacement p
  | .backward a p => -unit a + displacement p

def forwardCount {u v : V} : LabeledWalk s t u v → A → ℕ
  | .nil _, _ => 0
  | .forward b p, a => (if b = a then 1 else 0) + forwardCount p a
  | .backward _ p, a => forwardCount p a

def backwardCount {u v : V} : LabeledWalk s t u v → A → ℕ
  | .nil _, _ => 0
  | .forward _ p, a => backwardCount p a
  | .backward b p, a => (if b = a then 1 else 0) + backwardCount p a

/-- The displacement is the signed multiplicity of each original arrow label. -/
theorem displacement_apply {u v : V} (p : LabeledWalk s t u v) (a : A) :
    displacement p a = (forwardCount p a : ℤ) - (backwardCount p a : ℤ) := by
  induction p with
  | nil => simp [displacement,forwardCount,backwardCount]
  | forward b p ih =>
    simp only [displacement,forwardCount,backwardCount,Pi.add_apply,unit,Pi.single_apply,
      Nat.cast_add,ih,eq_comm]
    split_ifs <;> simp only [Nat.cast_one,Nat.cast_zero] <;> omega
  | backward b p ih =>
    simp only [displacement,forwardCount,backwardCount,Pi.add_apply,Pi.neg_apply,
      unit,Pi.single_apply,Nat.cast_add,ih,eq_comm]
    split_ifs <;> simp only [Nat.cast_one,Nat.cast_zero] <;> omega

/-- Actual lift of a signed labeled walk with prescribed starting character. -/
noncomputable def lift {u v : V} (p : LabeledWalk s t u v) (χ : Character A) :
    LabeledWalk (arrowSource s) (arrowTarget t) (u,χ) (v,χ + displacement p) := by
  induction p generalizing χ with
  | nil v =>
    simpa [displacement] using (LabeledWalk.nil (s := arrowSource s)
      (t := arrowTarget t) (v,χ))
  | @forward a v p ih =>
    have hp := ih (χ + unit a)
    have h := LabeledWalk.forward (s := arrowSource s) (t := arrowTarget t) (a,χ) hp
    simpa [arrowSource,arrowTarget,displacement,add_assoc] using h
  | @backward a v p ih =>
    have hp := ih (χ - unit a)
    have h := LabeledWalk.backward (s := arrowSource s) (t := arrowTarget t)
      (a,χ-unit a) hp
    simpa [arrowSource,arrowTarget,displacement,sub_eq_add_neg,add_assoc] using h

/-- For a closed base walk the constructed lift returns to its starting vertex
exactly when each original arrow has balanced signed multiplicities. -/
theorem lift_closed_iff {u : V} (p : LabeledWalk s t u u) (χ : Character A) :
    (u,χ + displacement p) = (u,χ) ↔
      ∀ a,forwardCount p a = backwardCount p a := by
  constructor
  · intro h a
    have ha := congrFun (congrArg (fun w : Vertex V A => w.2) h) a
    simp only [Pi.add_apply,displacement_apply] at ha
    omega
  · intro h
    apply Prod.ext
    · rfl
    · funext a
      simp [displacement_apply,h a]

end LabeledWalk
end KroneckerAbelianCover
end

/- Original module: KroneckerAbelianWalkProjection -/
section
/-! Displacement for every actual labeled cover walk. Unlike a guessed endpoint
formula, this is checked against each forward and backward lifted arrow. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

noncomputable def project {u v : Vertex V A} :
    LabeledWalk (arrowSource s) (arrowTarget t) u v → LabeledWalk s t u.1 v.1
  | .nil w => .nil w.1
  | .forward e p => .forward e.1 (project p)
  | .backward e p => .backward e.1 (project p)

/-- Endpoint displacement of any actual cover walk is the signed original-arrow
count of its projected walk. -/
theorem endpoint_character {u v : Vertex V A}
    (p : LabeledWalk (arrowSource s) (arrowTarget t) u v) :
    v.2 = u.2 + displacement (project p) := by
  induction p with
  | nil w => simp [project,displacement]
  | @forward e v p ih =>
    change v.2 = e.2 + (unit e.1 + displacement (project p))
    change v.2 = (e.2 + unit e.1) + displacement (project p) at ih
    simpa only [add_assoc] using ih
  | @backward e v p ih =>
    change v.2 = (e.2+unit e.1) + (-unit e.1 + displacement (project p))
    change v.2 = e.2 + displacement (project p) at ih
    rw [ih]
    abel

theorem endpoint_coordinate {u v : Vertex V A}
    (p : LabeledWalk (arrowSource s) (arrowTarget t) u v) (a : A) :
    v.2 a - u.2 a = (forwardCount (project p) a : ℤ) -
      (backwardCount (project p) a : ℤ) := by
  have h := congrFun (endpoint_character p) a
  simp only [Pi.add_apply,displacement_apply] at h
  omega

/-- Every closed actual cover walk projects to a balanced original-arrow word. -/
theorem closed_project_balanced {u : Vertex V A}
    (p : LabeledWalk (arrowSource s) (arrowTarget t) u u) (a : A) :
    forwardCount (project p) a = backwardCount (project p) a := by
  have h := endpoint_coordinate p a
  omega

end LabeledWalk
end KroneckerAbelianCover
end
