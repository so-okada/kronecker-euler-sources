import KroneckerLabeledWalkTrace

/- Original module: KroneckerLabeledClosedExtraction -/
section
/-! Actual closed-subwalk extraction and a minimal finite-support witness.
The bound proved here is support cardinality PLUS ONE; no sharper bound or
full iteration theorem is claimed. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

/-- A repeated vertex in a reduced walk gives a nonempty reduced closed subwalk
with a label list contained as a sublist of the original. -/
theorem repeated_vertex_closed_subwalk {u v : V} (p : LabeledWalk s t u v)
    (hr : Reduced p) (hn : ¬(vertices p).Nodup) :
    ∃ w : V, ∃ q : LabeledWalk s t w w,
      Reduced q ∧ 0 < (labels q).length ∧ (labels q).Sublist (labels p) := by
  induction p with
  | nil => simp [vertices] at hn
  | forward a p ih =>
    have hh : s a ∈ vertices p ∨ ¬(vertices p).Nodup := by
      simpa only [vertices,List.nodup_cons,not_and_or,not_not] using hn
    rcases hh with h | h
    · obtain ⟨q,r,he⟩ := split_at_vertex p (s a) h
      refine ⟨s a,.forward a q,?_,by simp [labels],?_⟩
      · have he' : labels (.forward a p) = labels (.forward a q) ++ labels r := by
          simp only [labels,he,List.cons_append]
        unfold Reduced at hr ⊢
        rw [he'] at hr
        exact hr.left_of_append
      · have hh := List.sublist_append_left (labels (.forward a q)) (labels r)
        simpa only [labels,he,List.cons_append] using hh
    · have ht : Reduced p := (show List.IsChain _ ((a,true)::labels p) from hr).tail
      obtain ⟨w,q,hq,hpos,hsub⟩ := ih ht h
      exact ⟨w,q,hq,hpos,hsub.cons (a,true)⟩
  | backward a p ih =>
    have hh : t a ∈ vertices p ∨ ¬(vertices p).Nodup := by
      simpa only [vertices,List.nodup_cons,not_and_or,not_not] using hn
    rcases hh with h | h
    · obtain ⟨q,r,he⟩ := split_at_vertex p (t a) h
      refine ⟨t a,.backward a q,?_,by simp [labels],?_⟩
      · have he' : labels (.backward a p) = labels (.backward a q) ++ labels r := by
          simp only [labels,he,List.cons_append]
        unfold Reduced at hr ⊢
        rw [he'] at hr
        exact hr.left_of_append
      · have hh := List.sublist_append_left (labels (.backward a q)) (labels r)
        simpa only [labels,he,List.cons_append] using hh
    · have ht : Reduced p := (show List.IsChain _ ((a,false)::labels p) from hr).tail
      obtain ⟨w,q,hq,hpos,hsub⟩ := ih ht h
      exact ⟨w,q,hq,hpos,hsub.cons (a,false)⟩

/-- A shortest positive reduced closed witness has a vertex-simple tail, hence
uses at most one more step than the original finite arrow support size. -/
theorem closed_support_bounded_witness {u : V} (p : LabeledWalk s t u u)
    (hr : Reduced p) (hpos : 0 < (labels p).length) :
    ∃ w : V, ∃ q : LabeledWalk s t w w,
      Reduced q ∧ 0 < (labels q).length ∧ arrowSupport q ⊆ arrowSupport p ∧
      (labels q).length ≤ (arrowSupport p).card + 1 := by
  classical
  let P (n : ℕ) := ∃ w : V, ∃ q : LabeledWalk s t w w,
    Reduced q ∧ 0 < (labels q).length ∧ (labels q).Sublist (labels p) ∧
      (labels q).length = n
  have hex : ∃ n,P n := ⟨(labels p).length,u,p,hr,hpos,List.Sublist.refl _,rfl⟩
  obtain ⟨w,q,hq,hqpos,hqsub,hqn⟩ := Nat.find_spec hex
  have hmin : ∀ (z : V) (r : LabeledWalk s t z z), Reduced r →
      0 < (labels r).length → (labels r).Sublist (labels p) →
      (labels q).length ≤ (labels r).length := by
    intro z r hr hpos hsub
    rw [hqn]
    exact Nat.find_min' hex ⟨z,r,hr,hpos,hsub,rfl⟩
  refine ⟨w,q,hq,hqpos,support_mono_of_labels_sublist p q hqsub,?_⟩
  cases q with
  | nil => simp [labels] at hqpos
  | forward a q =>
    have hv : (vertices q).Nodup := by
      by_contra hn
      have ht : Reduced q := (show List.IsChain _ ((a,true)::labels q) from hq).tail
      obtain ⟨z,r,hr,hpos,hsub⟩ := repeated_vertex_closed_subwalk q ht hn
      have hm := hmin z r hr hpos ((hsub.cons (a,true)).trans hqsub)
      have hl := hsub.length_le
      simp only [labels,List.length_cons] at hm
      omega
    have hc : (labels q).length = (arrowSupport q).card := by
      unfold arrowSupport
      rw [List.toFinset_card_of_nodup (distinct_vertices_distinct_arrows q hv),List.length_map]
    have hs : arrowSupport q ⊆ arrowSupport p :=
      support_mono_of_labels_sublist p q ((List.Sublist.refl (labels q)).cons (a,true) |>.trans hqsub)
    have hb := Finset.card_le_card hs
    simp only [labels,List.length_cons]
    omega
  | backward a q =>
    have hv : (vertices q).Nodup := by
      by_contra hn
      have ht : Reduced q := (show List.IsChain _ ((a,false)::labels q) from hq).tail
      obtain ⟨z,r,hr,hpos,hsub⟩ := repeated_vertex_closed_subwalk q ht hn
      have hm := hmin z r hr hpos ((hsub.cons (a,false)).trans hqsub)
      have hl := hsub.length_le
      simp only [labels,List.length_cons] at hm
      omega
    have hc : (labels q).length = (arrowSupport q).card := by
      unfold arrowSupport
      rw [List.toFinset_card_of_nodup (distinct_vertices_distinct_arrows q hv),List.length_map]
    have hs : arrowSupport q ⊆ arrowSupport p :=
      support_mono_of_labels_sublist p q ((List.Sublist.refl (labels q)).cons (a,false) |>.trans hqsub)
    have hb := Finset.card_le_card hs
    simp only [labels,List.length_cons]
    omega

end LabeledWalk
end KroneckerAbelianCover
end

/- Original module: KroneckerAbelianGirthGrowth -/
section
/-! Girth growth for the actual labeled universal abelian cover. The extraction
bound used is support cardinality plus one, giving the recurrence 2*g-2. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

def ReducedGirthBound (s t : A → V) (g : ℕ) : Prop :=
  ∀ (u : V) (p : LabeledWalk s t u u),
    Reduced p → 0 < (labels p).length → g ≤ (labels p).length

theorem abelian_girth_bound (g : ℕ) (h : ReducedGirthBound s t g) :
    ReducedGirthBound (arrowSource s) (arrowTarget t) (2*g-2) := by
  intro u p hr hp
  have hpr : Reduced (project p) := (projection_reduced_iff p).2 hr
  have hpp : 0 < (labels (project p)).length := by rw [projection_length]; exact hp
  obtain ⟨w,q,hq,hpos,_hs,hlen⟩ := closed_support_bounded_witness (project p) hpr hpp
  have hg := h w q hq hpos
  have hc := closed_projection_support_bound p
  omega

end LabeledWalk
end KroneckerAbelianCover
end

/- Original module: KroneckerAbelianIteratedGirth -/
section
/-! The actual iterated abelian-cover quivers have uniformly increasing lower
bounds on lengths of nonempty reduced closed walks, even for a base with loops
or parallel arrows. No identification with universal-tree moduli is asserted. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

theorem balanced_reduced_min_three {u v : V} (p : LabeledWalk s t u v)
    (hr : Reduced p) (hp : 0 < (labels p).length)
    (h : ∀ a, forwardCount p a = backwardCount p a) :
    3 ≤ (labels p).length := by
  by_contra hn
  have hl : (labels p).length ≤ 2 := by omega
  cases p with
  | nil => simp [labels] at hp
  | forward a p =>
    have hb := h a
    clear h hp hn
    simp only [Reduced,labels,forwardCount,backwardCount,List.length_cons] at *
    generalize hw : t a = w at *
    cases p with
    | nil => simp [forwardCount,backwardCount] at hb
    | forward b p =>
      simp only [labels,forwardCount,backwardCount,List.length_cons] at *
      generalize hz : t b = z at *
      cases p with
      | nil =>
        by_cases hba : b = a <;> simp_all [labels,forwardCount,backwardCount]
      | forward c p => simp only [labels,List.length_cons] at hl; omega
      | backward c p => simp only [labels,List.length_cons] at hl; omega
    | backward b p =>
      simp only [labels,forwardCount,backwardCount,List.length_cons] at *
      generalize hz : s b = z at *
      cases p with
      | nil =>
        by_cases hba : b = a <;> simp_all [labels,forwardCount,backwardCount]
      | forward c p => simp only [labels,List.length_cons] at hl; omega
      | backward c p => simp only [labels,List.length_cons] at hl; omega
  | backward a p =>
    have hb := h a
    clear h hp hn
    simp only [Reduced,labels,forwardCount,backwardCount,List.length_cons] at *
    generalize hw : s a = w at *
    cases p with
    | nil => simp [forwardCount,backwardCount] at hb
    | forward b p =>
      simp only [labels,forwardCount,backwardCount,List.length_cons] at *
      generalize hz : t b = z at *
      cases p with
      | nil =>
        by_cases hba : b = a <;> simp_all [labels,forwardCount,backwardCount]
      | forward c p => simp only [labels,List.length_cons] at hl; omega
      | backward c p => simp only [labels,List.length_cons] at hl; omega
    | backward b p =>
      simp only [labels,forwardCount,backwardCount,List.length_cons] at *
      generalize hz : s b = z at *
      cases p with
      | nil =>
        by_cases hba : b = a <;> simp_all [labels,forwardCount,backwardCount]
      | forward c p => simp only [labels,List.length_cons] at hl; omega
      | backward c p => simp only [labels,List.length_cons] at hl; omega

theorem first_abelian_girth : ReducedGirthBound (arrowSource s) (arrowTarget t) 3 := by
  intro u p hr hp
  rw [← projection_length p] at hp ⊢
  exact balanced_reduced_min_three (project p) ((projection_reduced_iff p).2 hr)
    hp (closed_project_balanced p)

end LabeledWalk

structure TypedQuiver where
  V : Type
  A : Type
  source : A → V
  target : A → V

noncomputable def TypedQuiver.abelian (Q : TypedQuiver) : TypedQuiver := by
  classical
  exact ⟨Vertex Q.V Q.A, Q.A × Character Q.A, arrowSource Q.source, arrowTarget Q.target⟩

noncomputable def TypedQuiver.iterate (Q : TypedQuiver) : ℕ → TypedQuiver
  | 0 => Q
  | n+1 => (Q.iterate n).abelian

namespace TypedQuiver
open LabeledWalk

set_option backward.isDefEq.respectTransparency false in
theorem iterate_girth (Q : TypedQuiver) (n : ℕ) :
    ReducedGirthBound (Q.iterate (n+1)).source (Q.iterate (n+1)).target (2^n+2) := by
  classical
  induction n with
  | zero => simpa [iterate,abelian] using
      (first_abelian_girth (s := Q.source) (t := Q.target))
  | succ n ih =>
    have h := abelian_girth_bound (2^n+2) ih
    have he : 2*(2^n+2)-2 = 2^(n+1)+2 := by rw [Nat.pow_succ]; omega
    rw [he] at h
    exact h

end TypedQuiver
end KroneckerAbelianCover
end
