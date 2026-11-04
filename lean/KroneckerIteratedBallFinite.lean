import KroneckerReducedPathUniqueness
import Mathlib.Data.Set.Finite.List

section

/- Original module: KroneckerIteratedPathBall -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

/-- The radius-r vertices of the reduced path unfolding, retaining actual typed
paths from the root. -/
def ReducedPathBall (u : V) (r : ℕ) :=
  {p : (Σ v : V, LabeledWalk s t u v) // Reduced p.2 ∧ (labels p.2).length ≤ r}

/-- The actual vertex ball, defined by a reduced path of length at most r. -/
def VertexBall (u : V) (r : ℕ) :=
  {v : V // ∃ p : LabeledWalk s t u v, Reduced p ∧ (labels p).length ≤ r}

def ballEndpoint {u : V} {r : ℕ} (p : ReducedPathBall (s:=s) (t:=t) u r) :
    VertexBall (s:=s) (t:=t) u r := ⟨p.val.1,p.val.2,p.property⟩

theorem ballEndpoint_surjective (u : V) (r : ℕ) :
    Function.Surjective (ballEndpoint (s:=s) (t:=t) (u:=u) (r:=r)) := by
  rintro ⟨v,p,hp⟩
  exact ⟨⟨⟨v,p⟩,hp⟩,rfl⟩

theorem ballEndpoint_injective {g r : ℕ} (hg : ReducedGirthBound s t g)
    (hr : 2*r < g) (u : V) :
    Function.Injective (ballEndpoint (s:=s) (t:=t) (u:=u) (r:=r)) := by
  rintro ⟨⟨v,p⟩,hp,hpl⟩ ⟨⟨w,q⟩,hq,hql⟩ he
  have hv : v = w := congrArg Subtype.val he
  subst w
  change (labels p).length ≤ r at hpl
  change (labels q).length ≤ r at hql
  have heq : p = q := reduced_paths_unique_below_girth hg p q hp hq (by omega)
  subst q
  rfl

/-- Genuine finite-radius endpoint equivalence, not an assumed identification
of an abelian cover with a universal tree. -/
noncomputable def pathBallEquiv {g r : ℕ} (hg : ReducedGirthBound s t g)
    (hr : 2*r < g) (u : V) :
    ReducedPathBall (s:=s) (t:=t) u r ≃ VertexBall (s:=s) (t:=t) u r :=
  Equiv.ofBijective ballEndpoint ⟨ballEndpoint_injective hg hr u,ballEndpoint_surjective u r⟩


end LabeledWalk
namespace TypedQuiver
open LabeledWalk

/-- Explicit actual stage at which the radius-r reduced path unfolding embeds
bijectively onto its vertex ball. This is an equivalence of the named vertex
types; a graph-level universal-tree identification is not claimed. -/
noncomputable def iterate_pathBallEquiv (Q : TypedQuiver) (r : ℕ)
    (u : (Q.iterate (2*r+1)).V) :
    ReducedPathBall (s:=(Q.iterate (2*r+1)).source) (t:=(Q.iterate (2*r+1)).target) u r ≃
      VertexBall (s:=(Q.iterate (2*r+1)).source) (t:=(Q.iterate (2*r+1)).target) u r := by
  classical
  apply pathBallEquiv (iterate_girth Q (2*r)) _ u
  have hp : 2*r < 2^(2*r) := Nat.lt_two_pow_self
  omega

end TypedQuiver
end KroneckerAbelianCover
end

/- Original module: KroneckerUniqueProjectedWalk -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A B : Type} {s t : A → V}

/-- Unique path lifting for an arrow map injective on each source and target
fiber. This retains parallel arrows and both directions. -/
theorem labels_eq_of_projected_labels (f : A → B)
    (hs : ∀ a b, f a = f b → s a = s b → a = b)
    (ht : ∀ a b, f a = f b → t a = t b → a = b)
    {u v u' v' : V} (p : LabeledWalk s t u v) (q : LabeledWalk s t u' v')
    (hu : u = u')
    (h : (labels p).map (fun x => (f x.1,x.2)) =
      (labels q).map (fun x => (f x.1,x.2))) : labels p = labels q := by
  induction p generalizing u' v' with
  | nil w =>
    cases q <;> simp_all [labels]
  | forward a p ih =>
    cases q with
    | nil => simp [labels] at h
    | forward b q =>
      simp only [labels,List.map_cons,List.cons.injEq,Prod.mk.injEq,and_true] at h
      have hab := hs a b h.1 hu
      subst b
      exact congrArg (List.cons (a,true)) (ih q rfl h.2)
    | backward => simp [labels] at h
  | backward a p ih =>
    cases q with
    | nil => simp [labels] at h
    | backward b q =>
      simp only [labels,List.map_cons,List.cons.injEq,Prod.mk.injEq,and_true] at h
      have hab := ht a b h.1 hu
      subst b
      exact congrArg (List.cons (a,false)) (ih q rfl h.2)
    | forward => simp [labels] at h

variable [DecidableEq A]

/-- Actual abelian-cover walks from a fixed starting vertex are determined by
their full signed original-arrow word. Endpoints need not be stipulated equal. -/
theorem abelian_labels_eq_of_projection {u v u' v' : Vertex V A}
    (p : LabeledWalk (arrowSource s) (arrowTarget t) u v)
    (q : LabeledWalk (arrowSource s) (arrowTarget t) u' v') (hu : u = u')
    (h : labels (project p) = labels (project q)) : labels p = labels q := by
  apply labels_eq_of_projected_labels Prod.fst ?_ ?_ p q hu
  · simpa only [labels_project] using h
  · intro a b hab hs
    exact Prod.ext hab (congrArg (fun z : Vertex V A => z.2) hs)
  · intro a b hab ht
    apply Prod.ext hab
    have hh := congrArg (fun z : Vertex V A => z.2) ht
    change a.2 + unit a.1 = b.2 + unit b.1 at hh
    rw [hab] at hh
    exact add_right_cancel hh

end LabeledWalk
end KroneckerAbelianCover
end

/- Original module: KroneckerIteratedBaseWords -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace TypedQuiver
open LabeledWalk

/-- The actual vertex projection through all iterated abelian covers. -/
noncomputable def baseVertex (Q : TypedQuiver) : (n : ℕ) → (Q.iterate n).V → Q.V
  | 0,u => u
  | n+1,u => baseVertex Q n u.1

/-- Project an actual typed walk all the way to the original finite quiver. -/
noncomputable def baseWalk (Q : TypedQuiver) (n : ℕ) :
    ∀ {u v : (Q.iterate n).V}, LabeledWalk (Q.iterate n).source (Q.iterate n).target u v →
      LabeledWalk Q.source Q.target (baseVertex Q n u) (baseVertex Q n v) := by
  classical
  induction n with
  | zero => intro u v p; exact p
  | succ n ih => intro u v p; exact ih (project p)

theorem baseWalk_length (Q : TypedQuiver) (n : ℕ)
    {u v : (Q.iterate n).V} (p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v) :
    (labels (baseWalk Q n p)).length = (labels p).length := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    change (labels (baseWalk Q n (project p))).length = _
    exact (ih (project p)).trans (projection_length p)

/-- The complete signed word in the ORIGINAL arrow alphabet determines every
lift with prescribed starting vertex, at every actual iteration depth. -/
theorem baseWalk_labels_injective (Q : TypedQuiver) (n : ℕ)
    {u v u' v' : (Q.iterate n).V}
    (p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v)
    (q : LabeledWalk (Q.iterate n).source (Q.iterate n).target u' v') (hu : u = u')
    (h : labels (baseWalk Q n p) = labels (baseWalk Q n q)) : labels p = labels q := by
  classical
  induction n with
  | zero => exact h
  | succ n ih =>
    apply abelian_labels_eq_of_projection p q hu
    apply ih (project p) (project q) (congrArg Prod.fst hu)
    exact h

/-- Encoding the actual reduced unfolding ball by bounded original-arrow words. -/
noncomputable def ballBaseWord (Q : TypedQuiver) (n r : ℕ) (u : (Q.iterate n).V)
    (p : ReducedPathBall (s:=(Q.iterate n).source) (t:=(Q.iterate n).target) u r) :
    {w : List (Q.A × Bool) // w.length ≤ r} :=
  ⟨labels (baseWalk Q n p.val.2),by rw [baseWalk_length]; exact p.property.2⟩

theorem ballBaseWord_injective (Q : TypedQuiver) (n r : ℕ) (u : (Q.iterate n).V) :
    Function.Injective (ballBaseWord Q n r u) := by
  rintro ⟨⟨v,p⟩,hp⟩ ⟨⟨w,q⟩,hq⟩ h
  have he : labels (baseWalk Q n p) = labels (baseWalk Q n q) := congrArg Subtype.val h
  have hh := labels_heq p q rfl (baseWalk_labels_injective Q n p q rfl he)
  obtain ⟨hv,hpq⟩ := hh
  subst w
  cases hpq
  rfl

end TypedQuiver
end KroneckerAbelianCover
end
end

section

set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk

/-- Exact bounded-word alphabet decomposition, retaining word length. -/
def boundedWordEquiv (X : Type) (r : ℕ) :
    {w : List X // w.length ≤ r} ≃ (Σ n : Fin (r+1), List.Vector X n.val) where
  toFun w := ⟨⟨w.val.length,Nat.lt_succ_of_le w.property⟩,⟨w.val,rfl⟩⟩
  invFun w := ⟨w.2.val,by rw [w.2.property]; exact Nat.le_of_lt_succ w.1.isLt⟩
  left_inv w := rfl
  right_inv := by
    rintro ⟨⟨n,hn⟩,w,hw⟩
    dsimp at hw
    subst n
    rfl

theorem boundedWord_card (X : Type) [Fintype X] (r : ℕ) :
    Nat.card {w : List X // w.length ≤ r} = ∑ n : Fin (r+1), Fintype.card X ^ n.val := by
  rw [Nat.card_congr (boundedWordEquiv X r),Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [card_vector]

/-- The reduced-path ball is exactly the ordinary bounded typed-walk ball. -/
theorem vertexBall_iff_walk {V A : Type} [DecidableEq A] {s t : A → V}
    (u v : V) (r : ℕ) :
    (∃ p : LabeledWalk s t u v, Reduced p ∧ (labels p).length ≤ r) ↔
      ∃ p : LabeledWalk s t u v, (labels p).length ≤ r := by
  constructor
  · rintro ⟨p,_,hl⟩; exact ⟨p,hl⟩
  · rintro ⟨p,hl⟩
    obtain ⟨q,_,hq,hql,_⟩ := exists_reduced_normal_form p
    exact ⟨q,hq,hql.trans hl⟩

end LabeledWalk
namespace TypedQuiver
open LabeledWalk

/-- Local finiteness is inherited from the ORIGINAL arrow alphabet even though
all positive-depth cover arrow types themselves may be infinite. -/
theorem iterate_pathBall_finite (Q : TypedQuiver) [Finite Q.A] (n r : ℕ)
    (u : (Q.iterate n).V) :
    Finite (ReducedPathBall (s:=(Q.iterate n).source) (t:=(Q.iterate n).target) u r) := by
  haveI : Finite {w : List (Q.A × Bool) // w.length ≤ r} :=
    (List.finite_length_le (Q.A × Bool) r).to_subtype
  exact Finite.of_injective (ballBaseWord Q n r u) (ballBaseWord_injective Q n r u)

/-- Actual vertex balls are finite at EVERY iterated-cover stage, without a
separate local-finiteness assumption on the infinite cover. -/
theorem iterate_vertexBall_finite (Q : TypedQuiver) [Finite Q.A] (n r : ℕ)
    (u : (Q.iterate n).V) :
    Finite (VertexBall (s:=(Q.iterate n).source) (t:=(Q.iterate n).target) u r) := by
  classical
  haveI := iterate_pathBall_finite Q n r u
  exact Finite.of_surjective ballEndpoint (ballEndpoint_surjective u r)

/-- Uniform explicit ball bound in terms of the finite ORIGINAL arrow alphabet;
no finiteness of the character lattice or lifted arrow type is assumed. -/
theorem iterate_vertexBall_card_le (Q : TypedQuiver) [Fintype Q.A] (n r : ℕ)
    (u : (Q.iterate n).V) :
    Nat.card (VertexBall (s:=(Q.iterate n).source) (t:=(Q.iterate n).target) u r) ≤
      ∑ j : Fin (r+1), (2 * Fintype.card Q.A) ^ j.val := by
  classical
  haveI := iterate_pathBall_finite Q n r u
  haveI := iterate_vertexBall_finite Q n r u
  haveI : Finite {w : List (Q.A × Bool) // w.length ≤ r} :=
    (List.finite_length_le (Q.A × Bool) r).to_subtype
  have h1 := Nat.card_le_card_of_surjective ballEndpoint
    (ballEndpoint_surjective (s:=(Q.iterate n).source) (t:=(Q.iterate n).target) u r)
  have h2 := Nat.card_le_card_of_injective (ballBaseWord Q n r u) (ballBaseWord_injective Q n r u)
  have h := h1.trans h2
  rw [boundedWord_card] at h
  simpa only [Fintype.card_prod,Fintype.card_bool,Nat.mul_comm] using h

end TypedQuiver
end KroneckerAbelianCover
end

