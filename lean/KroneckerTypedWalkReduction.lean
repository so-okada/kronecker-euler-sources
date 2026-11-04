import KroneckerIteratedFiniteSupportForest
import Mathlib.GroupTheory.FreeGroup.Reduce

set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} {s t : A → V}

def append {u v w : V} (p : LabeledWalk s t u v) (q : LabeledWalk s t v w) :
    LabeledWalk s t u w := match p with
  | .nil _ => q
  | .forward a r => .forward a (append r q)
  | .backward a r => .backward a (append r q)

theorem labels_append {u v w : V} (p : LabeledWalk s t u v) (q : LabeledWalk s t v w) :
    labels (append p q) = labels p ++ labels q := by
  induction p <;> simp_all [append,labels]

def reverse {u v : V} (p : LabeledWalk s t u v) : LabeledWalk s t v u := match p with
  | .nil w => .nil w
  | .forward a r => append (reverse r) (.backward a (.nil _))
  | .backward a r => append (reverse r) (.forward a (.nil _))

theorem labels_reverse {u v : V} (p : LabeledWalk s t u v) :
    labels (reverse p) = FreeGroup.invRev (labels p) := by
  induction p <;> simp_all [reverse,labels,labels_append,FreeGroup.invRev]

theorem labels_heq {u v u' v' : V} (p : LabeledWalk s t u v)
    (q : LabeledWalk s t u' v') (hu : u = u') (h : labels p = labels q) : v = v' ∧ HEq p q := by
  induction p generalizing u' v' with
  | nil w =>
    cases q with
    | nil => cases hu; exact ⟨rfl,HEq.rfl⟩
    | forward => simp [labels] at h
    | backward => simp [labels] at h
  | forward a p ih =>
    cases q with
    | nil => simp [labels] at h
    | forward b q =>
      simp only [labels,List.cons.injEq,Prod.mk.injEq,and_true] at h
      rcases h with ⟨rfl,h⟩
      obtain ⟨hv,hh⟩ := ih q rfl h
      subst v'
      cases hh
      exact ⟨rfl,HEq.rfl⟩
    | backward => simp [labels] at h
  | backward a p ih =>
    cases q with
    | nil => simp [labels] at h
    | backward b q =>
      simp only [labels,List.cons.injEq,Prod.mk.injEq,and_true] at h
      rcases h with ⟨rfl,h⟩
      obtain ⟨hv,hh⟩ := ih q rfl h
      subst v'
      cases hh
      exact ⟨rfl,HEq.rfl⟩
    | forward => simp [labels] at h

theorem labels_injective {u v : V} : Function.Injective (labels (s:=s) (t:=t) (u:=u) (v:=v)) := by
  intro p q h
  exact eq_of_heq (labels_heq p q rfl h).2

theorem view_forward {u v : V} (p : LabeledWalk s t u v) (a : A) (L : List (A × Bool))
    (h : labels p = (a,true)::L) :
    u = s a ∧ ∃ q : LabeledWalk s t (t a) v, labels q = L := by
  cases p with
  | nil => simp [labels] at h
  | forward c p =>
    simp only [labels,List.cons.injEq,Prod.mk.injEq,and_true] at h
    rcases h with ⟨rfl,h⟩
    exact ⟨rfl,p,h⟩
  | backward => simp [labels] at h

theorem view_backward {u v : V} (p : LabeledWalk s t u v) (a : A) (L : List (A × Bool))
    (h : labels p = (a,false)::L) :
    u = t a ∧ ∃ q : LabeledWalk s t (s a) v, labels q = L := by
  cases p with
  | nil => simp [labels] at h
  | backward c p =>
    simp only [labels,List.cons.injEq,Prod.mk.injEq,and_true] at h
    rcases h with ⟨rfl,h⟩
    exact ⟨rfl,p,h⟩
  | forward => simp [labels] at h

/-- Removing a genuine inverse adjacent pair preserves the actual walk endpoints. -/
theorem realize_head_cancel {u v : V} (p : LabeledWalk s t u v)
    (a : A) (b : Bool) (L : List (A × Bool))
    (h : labels p = (a,b)::(a,!b)::L) :
    ∃ q : LabeledWalk s t u v, labels q = L := by
  cases b with
  | false =>
    obtain ⟨hu,q,hq⟩ := view_backward p a ((a,true)::L) h
    obtain ⟨_,r,hr⟩ := view_forward q a L hq
    subst u
    exact ⟨r,hr⟩
  | true =>
    obtain ⟨hu,q,hq⟩ := view_forward p a ((a,false)::L) h
    obtain ⟨_,r,hr⟩ := view_backward q a L hq
    subst u
    exact ⟨r,hr⟩

/-- Word cancellation is realized internally in the typed quiver, including an
arbitrary prefix. -/
theorem realize_cancel (K L : List (A × Bool)) (a : A) (b : Bool)
    {u v : V} (p : LabeledWalk s t u v)
    (h : labels p = K ++ (a,b)::(a,!b)::L) :
    ∃ q : LabeledWalk s t u v, labels q = K ++ L := by
  induction K generalizing u with
  | nil => exact realize_head_cancel p a b L h
  | cons x K ih =>
    cases p with
    | nil => simp [labels] at h
    | forward c p =>
      simp only [labels,List.cons_append,List.cons.injEq] at h
      obtain ⟨q,hq⟩ := ih p h.2
      exact ⟨.forward c q,by simp [labels,hq,←h.1]⟩
    | backward c p =>
      simp only [labels,List.cons_append,List.cons.injEq] at h
      obtain ⟨q,hq⟩ := ih p h.2
      exact ⟨.backward c q,by simp [labels,hq,←h.1]⟩

/-- Every finite free-word reduction is realized by an actual walk with the
same endpoints; no abstract word is silently substituted for a quiver path. -/
theorem realize_red {K L : List (A × Bool)} (h : FreeGroup.Red K L)
    {u v : V} (p : LabeledWalk s t u v) (hp : labels p = K) :
    ∃ q : LabeledWalk s t u v, labels q = L := by
  induction h with
  | refl => exact ⟨p,hp⟩
  | tail h step ih =>
    obtain ⟨q,hq⟩ := ih
    cases step with
    | @not K L a b => exact realize_cancel K L a b q hq

theorem reduced_iff_freeGroup {u v : V} (p : LabeledWalk s t u v) :
    Reduced p ↔ FreeGroup.IsReduced (labels p) := by
  classical
  simp only [Reduced,FreeGroup.IsReduced,or_iff_not_imp_left,not_not]

/-- Canonical free reduction has a genuine typed-walk realization, is reduced,
and never increases length or arrow support. -/
theorem exists_reduced_normal_form [DecidableEq A] {u v : V} (p : LabeledWalk s t u v) :
    ∃ q : LabeledWalk s t u v, labels q = FreeGroup.reduce (labels p) ∧
      Reduced q ∧ (labels q).length ≤ (labels p).length ∧
      arrowSupport q ⊆ arrowSupport p := by
  obtain ⟨q,hq⟩ := realize_red (FreeGroup.reduce.red (L:=labels p)) p rfl
  refine ⟨q,hq,?_,?_,?_⟩
  · rw [reduced_iff_freeGroup,hq]
    exact FreeGroup.IsReduced.of_reduce_eq FreeGroup.reduce.idem
  · rw [hq]
    exact FreeGroup.Red.length_le FreeGroup.reduce.red
  · apply support_mono_of_labels_sublist p q
    rw [hq]
    exact FreeGroup.Red.sublist FreeGroup.reduce.red

end LabeledWalk
end KroneckerAbelianCover
