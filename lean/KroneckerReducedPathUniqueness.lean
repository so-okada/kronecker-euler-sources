import KroneckerTypedWalkReduction

/- Original module: KroneckerFiniteSupportRestriction -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

/-- Forgetting the subtype of actual arrow labels leaves endpoints unchanged. -/
def forgetSupport (F : Finset A) {u v : V} :
    LabeledWalk (fun a : {a // a ∈ F} => s a.val)
      (fun a : {a // a ∈ F} => t a.val) u v → LabeledWalk s t u v
  | .nil w => .nil w
  | .forward a p => .forward a.val (forgetSupport F p)
  | .backward a p => .backward a.val (forgetSupport F p)

theorem forgetSupport_labels (F : Finset A) {u v : V}
    (p : LabeledWalk (fun a : {a // a ∈ F} => s a.val)
      (fun a : {a // a ∈ F} => t a.val) u v) :
    labels (forgetSupport F p) = (labels p).map (fun x => (x.1.val,x.2)) := by
  induction p <;> simp_all [forgetSupport,labels]

theorem forgetSupport_reduced_iff (F : Finset A) {u v : V}
    (p : LabeledWalk (fun a : {a // a ∈ F} => s a.val)
      (fun a : {a // a ∈ F} => t a.val) u v) :
    Reduced (forgetSupport F p) ↔ Reduced p := by
  simp only [Reduced,forgetSupport_labels,List.isChain_map]
  have hrel : (fun x y : {a // a ∈ F} × Bool => x.1.val ≠ y.1.val ∨ x.2 = y.2) =
      (fun x y => x.1 ≠ y.1 ∨ x.2 = y.2) := by
    funext x y
    apply propext
    exact or_congr (not_congr Subtype.ext_iff.symm) Iff.rfl
  rw [hrel]

theorem forgetSupport_support (F : Finset A) {u v : V}
    (p : LabeledWalk (fun a : {a // a ∈ F} => s a.val)
      (fun a : {a // a ∈ F} => t a.val) u v) : arrowSupport (forgetSupport F p) ⊆ F := by
  intro a ha
  simp only [arrowSupport,forgetSupport_labels,List.mem_toFinset,List.mem_map] at ha
  obtain ⟨b,hb,rfl⟩ := ha
  obtain ⟨c,hc,rfl⟩ := hb
  exact c.1.property

/-- The actual arrow-restricted quiver is a forest: all its reduced loops are
empty, with no bound imposed on the length of the loop. -/
theorem restricted_forest_of_girth {g : ℕ} (hg : ReducedGirthBound s t g)
    (F : Finset A) (hF : F.card + 1 < g) {u : V}
    (p : LabeledWalk (fun a : {a // a ∈ F} => s a.val)
      (fun a : {a // a ∈ F} => t a.val) u u) (hr : Reduced p) : labels p = [] := by
  have he := finite_support_no_reduced_closed hg F hF (forgetSupport F p)
    ((forgetSupport_reduced_iff F p).mpr hr) (forgetSupport_support F p)
  simpa only [forgetSupport_labels,List.map_eq_nil_iff] using he

end LabeledWalk
namespace TypedQuiver
open LabeledWalk

def restrictArrows (Q : TypedQuiver) (F : Finset Q.A) : TypedQuiver :=
  ⟨Q.V,{a // a ∈ F},fun a => Q.source a.val,fun a => Q.target a.val⟩

/-- Uniform actual finite-subquiver conclusion from the iterated cover girth. -/
theorem iterate_restricted_forest (Q : TypedQuiver) (m : ℕ)
    [DecidableEq (Q.iterate (m+1)).A]
    (F : Finset (Q.iterate (m+1)).A) (hF : F.card ≤ m)
    {u : ((Q.iterate (m+1)).restrictArrows F).V}
    (p : LabeledWalk ((Q.iterate (m+1)).restrictArrows F).source
      ((Q.iterate (m+1)).restrictArrows F).target u u)
    (hr : Reduced p) : labels p = [] := by
  apply restricted_forest_of_girth (iterate_girth Q m) F _ p hr
  have hp : m < 2^m := Nat.lt_two_pow_self
  omega

end TypedQuiver
end KroneckerAbelianCover
end

/- Original module: KroneckerReducedPathUniqueness -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

private theorem word_eq_of_normal_loop_empty {u v : V} (p q : LabeledWalk s t u v)
    (h : FreeGroup.reduce (labels (append p (reverse q))) = []) :
    FreeGroup.mk (labels p) = FreeGroup.mk (labels q) := by
  apply mul_inv_eq_one.mp
  rw [FreeGroup.inv_mk,FreeGroup.mul_mk]
  rw [←labels_reverse q,←labels_append p (reverse q)]
  rw [←FreeGroup.reduce.self,h]
  rfl

private theorem eq_of_word_eq {u v : V} (p q : LabeledWalk s t u v)
    (hp : Reduced p) (hq : Reduced q)
    (h : FreeGroup.mk (labels p) = FreeGroup.mk (labels q)) : p = q := by
  apply labels_injective
  have hh := FreeGroup.reduce.sound h
  rw [((reduced_iff_freeGroup p).mp hp).reduce_eq,
    ((reduced_iff_freeGroup q).mp hq).reduce_eq] at hh
  exact hh

/-- Two reduced typed paths with common endpoints agree whenever their combined
length is strictly below the actual reduced girth. -/
theorem reduced_paths_unique_below_girth {g : ℕ} (hg : ReducedGirthBound s t g)
    {u v : V} (p q : LabeledWalk s t u v) (hp : Reduced p) (hq : Reduced q)
    (hlen : (labels p).length + (labels q).length < g) : p = q := by
  obtain ⟨r,he,hr,hl,_⟩ := exists_reduced_normal_form (append p (reverse q))
  have hshort : (labels r).length < g := by
    simp only [labels_append,labels_reverse,List.length_append,FreeGroup.invRev,
      List.length_map,List.length_reverse] at hl
    omega
  have hempty := reduced_closed_empty_below_girth hg r hr hshort
  apply eq_of_word_eq p q hp hq
  apply word_eq_of_normal_loop_empty p q
  exact he.symm.trans hempty

/-- In a quiver with no nonempty reduced loop, endpoints determine every reduced
path, regardless of length. -/
theorem reduced_paths_unique_of_forest
    (hf : ∀ u (p : LabeledWalk s t u u), Reduced p → labels p = [])
    {u v : V} (p q : LabeledWalk s t u v) (hp : Reduced p) (hq : Reduced q) : p = q := by
  obtain ⟨r,he,hr,_,_⟩ := exists_reduced_normal_form (append p (reverse q))
  apply eq_of_word_eq p q hp hq
  apply word_eq_of_normal_loop_empty p q
  exact he.symm.trans (hf u r hr)

end LabeledWalk
namespace TypedQuiver
open LabeledWalk

/-- All reduced paths in any small actual finite arrow support agree on common
endpoints at the stated finite stage of iterated abelian covering. -/
theorem iterate_restricted_unique_paths (Q : TypedQuiver) (m : ℕ)
    [DecidableEq (Q.iterate (m+1)).A]
    (F : Finset (Q.iterate (m+1)).A) (hF : F.card ≤ m)
    {u v : ((Q.iterate (m+1)).restrictArrows F).V}
    (p q : LabeledWalk ((Q.iterate (m+1)).restrictArrows F).source
      ((Q.iterate (m+1)).restrictArrows F).target u v)
    (hp : Reduced p) (hq : Reduced q) : p = q := by
  classical
  exact reduced_paths_unique_of_forest (fun _ r hr => iterate_restricted_forest Q m F hF r hr)
    p q hp hq

end TypedQuiver
end KroneckerAbelianCover
end
