import KroneckerAbelianWalkProjection

/- Original module: KroneckerAbelianBalancedSixWalk -/
section
/-! A concrete discriminator for the iteration bridge: the first abelian cover
of the three-arrow Kronecker quiver still has a nonempty reduced closed walk.
Thus balance alone cannot identify a tree or prove the iteration theorem. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} {s t : A → V}

def labels {u v : V} : LabeledWalk s t u v → List (A × Bool)
  | .nil _ => []
  | .forward a p => (a,true) :: labels p
  | .backward a p => (a,false) :: labels p

def Reduced {u v : V} (p : LabeledWalk s t u v) : Prop :=
  (labels p).IsChain (fun x y => x.1 ≠ y.1 ∨ x.2 = y.2)

end LabeledWalk
namespace BalancedSixWalk
open LabeledWalk

def source (_ : Fin 3) : Bool := false
def target (_ : Fin 3) : Bool := true

def six : LabeledWalk source target false false :=
  .forward 0 (.backward 1 (.forward 2 (.backward 0 (.forward 1 (.backward 2 (.nil false))))))

theorem six_reduced : Reduced six := by
  unfold Reduced
  decide

theorem six_nonempty : (labels six).length = 6 := by decide

theorem six_balanced (a : Fin 3) : forwardCount six a = backwardCount six a := by
  fin_cases a <;> decide

/-- Despite being a nonempty reduced labeled walk, this path lifts closed from
every character. No girth-growth theorem follows merely from balance. -/
theorem six_lift_closes (χ : Character (Fin 3)) :
    (false,χ + displacement six) = (false,χ) :=
  (lift_closed_iff six χ).mpr six_balanced

end BalancedSixWalk
end KroneckerAbelianCover
end

/- Original module: KroneckerAbelianBalancedSupportBound -/
section
/-! Uniform support bound for balanced walks. The arrow set may be infinite,
so this lemma applies at later abelian-cover stages as well as at the base.
Cycle extraction and girth growth are deliberately not assumptions here. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
open scoped BigOperators
variable {V A : Type} [DecidableEq A] {s t : A → V}

def arrowSupport {u v : V} (p : LabeledWalk s t u v) : Finset A :=
  ((labels p).map Prod.fst).toFinset

theorem unsigned_count {u v : V} (p : LabeledWalk s t u v) (a : A) :
    ((labels p).map Prod.fst).count a = forwardCount p a + backwardCount p a := by
  induction p with
  | nil => simp [labels,forwardCount,backwardCount]
  | forward b p ih =>
    by_cases h : b = a
    · subst b
      simp [labels,forwardCount,backwardCount,ih,Nat.add_comm,Nat.add_left_comm]
    · simp [labels,forwardCount,backwardCount,h,ih]
  | backward b p ih =>
    by_cases h : b = a
    · subst b
      simp [labels,forwardCount,backwardCount,ih,Nat.add_assoc,Nat.add_comm]
    · simp [labels,forwardCount,backwardCount,h,ih]

/-- Each used label in a balanced walk must occur in both orientations. -/
theorem balanced_used_twice {u v : V} (p : LabeledWalk s t u v)
    (h : ∀ a,forwardCount p a = backwardCount p a) {a : A} (ha : a ∈ arrowSupport p) :
    2 ≤ ((labels p).map Prod.fst).count a := by
  have hp : 0 < ((labels p).map Prod.fst).count a := by
    exact List.count_pos_iff.mpr (List.mem_toFinset.mp ha)
  rw [unsigned_count] at hp ⊢
  have he := h a
  omega

/-- Balanced support uses at most half the walk length in distinct arrow labels.
No global finiteness hypothesis on vertices or arrows is needed. -/
theorem balanced_support_twice_card_le_length {u v : V} (p : LabeledWalk s t u v)
    (h : ∀ a,forwardCount p a = backwardCount p a) :
    2 * (arrowSupport p).card ≤ (labels p).length := by
  calc
    2 * (arrowSupport p).card = ∑ _a ∈ arrowSupport p, (2 : ℕ) := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ arrowSupport p, ((labels p).map Prod.fst).count a :=
      Finset.sum_le_sum (fun a ha => balanced_used_twice p h ha)
    _ = (labels p).length := by
      simpa only [arrowSupport,List.length_map] using
        List.sum_toFinset_count_eq_length ((labels p).map Prod.fst)

theorem labels_project {u v : Vertex V A}
    (p : LabeledWalk (arrowSource s) (arrowTarget t) u v) :
    labels (project p) = (labels p).map (fun e => (e.1.1,e.2)) := by
  induction p with
  | nil => rfl
  | forward e p ih => exact congrArg (List.cons (e.1, true)) ih
  | backward e p ih => exact congrArg (List.cons (e.1, false)) ih

theorem projection_length {u v : Vertex V A}
    (p : LabeledWalk (arrowSource s) (arrowTarget t) u v) :
    (labels (project p)).length = (labels p).length := by
  rw [labels_project,List.length_map]

/-- Every actual closed walk upstairs projects to a base edge support of at most
half its projected length. This is the counting half of the girth-growth route. -/
theorem closed_projection_support_bound {u : Vertex V A}
    (p : LabeledWalk (arrowSource s) (arrowTarget t) u u) :
    2 * (arrowSupport (project p)).card ≤ (labels p).length := by
  rw [← projection_length p]
  exact balanced_support_twice_card_le_length (project p) (closed_project_balanced p)

end LabeledWalk
end KroneckerAbelianCover
end

/- Original module: KroneckerAbelianReductionProjection -/
section
/-! Projection preserves and reflects adjacent cancellation of actual labeled
cover walks. Unique source/target lifting is used at the possible cancellation,
so equal projected labels are not silently identified as equal cover arrows. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

def stepStart (s t : A → V) (x : A × Bool) : V := if x.2 then s x.1 else t x.1
def stepEnd (s t : A → V) (x : A × Bool) : V := if x.2 then t x.1 else s x.1

def projectStep (x : (A × Character A) × Bool) : A × Bool := (x.1.1,x.2)
def NonCancel (x y : A × Bool) : Prop := x.1 ≠ y.1 ∨ x.2 = y.2

/-- Matching endpoints and the same original label determine the same arrow
whenever the directions are opposite. -/
theorem noncancel_project_iff (x y : (A × Character A) × Bool)
    (h : stepEnd (arrowSource s) (arrowTarget t) x =
      stepStart (arrowSource s) (arrowTarget t) y) :
    NonCancel (projectStep x) (projectStep y) ↔ NonCancel x y := by
  rcases x with ⟨e,ε⟩
  rcases y with ⟨f,η⟩
  cases ε <;> cases η
  · simp [NonCancel,projectStep]
  · simp only [stepEnd,stepStart,Bool.false_eq_true,↓reduceIte] at h
    simp only [NonCancel,projectStep]
    simp
    have he : e.1 = f.1 → e = f := by
      intro he
      exact Prod.ext he (congrArg (fun z : Vertex V A => z.2) h)
    exact ⟨fun hn hh => hn (congrArg Prod.fst hh), fun hn hh => hn (he hh)⟩
  · simp only [stepEnd,stepStart,Bool.false_eq_true,↓reduceIte] at h
    simp only [NonCancel,projectStep]
    simp
    have he : e.1 = f.1 → e = f := by
      intro he
      apply Prod.ext he
      have hc := congrArg (fun z : Vertex V A => z.2) h
      change e.2 + unit e.1 = f.2 + unit f.1 at hc
      rw [he] at hc
      exact add_right_cancel hc
    exact ⟨fun hn hh => hn (congrArg Prod.fst hh), fun hn hh => hn (he hh)⟩
  · simp [NonCancel,projectStep]

/-- Prefix formulation keeps endpoint compatibility explicit in the induction. -/
theorem projection_chain_prefix {u v : Vertex V A}
    (p : LabeledWalk (arrowSource s) (arrowTarget t) u v)
    (x : (A × Character A) × Bool)
    (hx : stepEnd (arrowSource s) (arrowTarget t) x = u) :
    List.IsChain NonCancel (x :: labels p) ↔
      List.IsChain NonCancel (projectStep x :: labels (project p)) := by
  induction p generalizing x with
  | nil w => simp [labels,project]
  | forward e p ih =>
    simp only [labels,project,List.isChain_cons_cons]
    exact and_congr (noncancel_project_iff x (e,true) hx).symm (ih (e,true) rfl)
  | backward e p ih =>
    simp only [labels,project,List.isChain_cons_cons]
    exact and_congr (noncancel_project_iff x (e,false) hx).symm (ih (e,false) rfl)

/-- Nonbacktracking is preserved in both directions by this actual cover map. -/
theorem projection_reduced_iff {u v : Vertex V A}
    (p : LabeledWalk (arrowSource s) (arrowTarget t) u v) :
    Reduced (project p) ↔ Reduced p := by
  cases p with
  | nil => simp [Reduced,labels,project]
  | forward e p => exact (projection_chain_prefix p (e,true) rfl).symm
  | backward e p => exact (projection_chain_prefix p (e,false) rfl).symm

end LabeledWalk
end KroneckerAbelianCover
end

/- Original module: KroneckerLabeledWalkTrace -/
section
/-! Vertex traces and exact splitting of actual labeled walks. These retain
multigraph arrow labels instead of passing to a collapsed simple graph. -/
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} {s t : A → V}

def vertices {u v : V} : LabeledWalk s t u v → List V
  | .nil u => [u]
  | .forward a p => s a :: vertices p
  | .backward a p => t a :: vertices p

theorem start_mem_vertices {u v : V} (p : LabeledWalk s t u v) : u ∈ vertices p := by
  cases p <;> simp [vertices]

theorem finish_mem_vertices {u v : V} (p : LabeledWalk s t u v) : v ∈ vertices p := by
  induction p with
  | nil => simp [vertices]
  | forward a p ih => exact List.mem_cons_of_mem _ ih
  | backward a p ih => exact List.mem_cons_of_mem _ ih

/-- Split at any visited vertex, preserving the exact concatenated label list. -/
theorem split_at_vertex {u v : V} (p : LabeledWalk s t u v) (w : V)
    (hw : w ∈ vertices p) :
    ∃ q : LabeledWalk s t u w, ∃ r : LabeledWalk s t w v,
      labels p = labels q ++ labels r := by
  induction p with
  | nil u =>
    simp only [vertices,List.mem_singleton] at hw
    subst w
    exact ⟨.nil u,.nil u,rfl⟩
  | forward a p ih =>
    rcases List.mem_cons.mp hw with h | h
    · subst w
      exact ⟨.nil _,.forward a p,rfl⟩
    · obtain ⟨q,r,he⟩ := ih h
      exact ⟨.forward a q,r,by simp only [labels,he,List.cons_append]⟩
  | backward a p ih =>
    rcases List.mem_cons.mp hw with h | h
    · subst w
      exact ⟨.nil _,.backward a p,rfl⟩
    · obtain ⟨q,r,he⟩ := ih h
      exact ⟨.backward a q,r,by simp only [labels,he,List.cons_append]⟩

variable [DecidableEq A]

theorem arrow_endpoints_mem {u v : V} (p : LabeledWalk s t u v) {a : A}
    (ha : a ∈ arrowSupport p) : s a ∈ vertices p ∧ t a ∈ vertices p := by
  induction p with
  | nil => simp [arrowSupport,labels] at ha
  | forward b p ih =>
    simp only [arrowSupport,labels,List.map_cons,List.toFinset_cons,Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (start_mem_vertices p)⟩
    · exact ⟨List.mem_cons_of_mem _ (ih ha).1,List.mem_cons_of_mem _ (ih ha).2⟩
  | backward b p ih =>
    simp only [arrowSupport,labels,List.map_cons,List.toFinset_cons,Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact ⟨List.mem_cons_of_mem _ (start_mem_vertices p),List.mem_cons_self⟩
    · exact ⟨List.mem_cons_of_mem _ (ih ha).1,List.mem_cons_of_mem _ (ih ha).2⟩

/-- A vertex-simple walk cannot repeat an original arrow label, even reversing it. -/
theorem distinct_vertices_distinct_arrows {u v : V} (p : LabeledWalk s t u v)
    (h : (vertices p).Nodup) : ((labels p).map Prod.fst).Nodup := by
  induction p with
  | nil => simp [labels]
  | forward a p ih =>
    have hh := List.nodup_cons.mp h
    simp only [labels,List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hh.2⟩
    intro ha
    exact hh.1 (arrow_endpoints_mem p (List.mem_toFinset.mpr ha)).1
  | backward a p ih =>
    have hh := List.nodup_cons.mp h
    simp only [labels,List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hh.2⟩
    intro ha
    exact hh.1 (arrow_endpoints_mem p (List.mem_toFinset.mpr ha)).2

theorem support_mono_of_labels_sublist {u v w z : V}
    (p : LabeledWalk s t u v) (q : LabeledWalk s t w z)
    (h : (labels q).Sublist (labels p)) : arrowSupport q ⊆ arrowSupport p := by
  intro a ha
  exact List.mem_toFinset.mpr ((h.map Prod.fst).subset (List.mem_toFinset.mp ha))

end LabeledWalk
end KroneckerAbelianCover
end
