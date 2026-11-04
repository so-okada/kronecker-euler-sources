import KroneckerComponentRoots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.BigOperators

/-! Finite colored gradings, with all binomial color choices retained.
Restriction and extension are maps on the actual finite sets of colorings. -/
set_option autoImplicit false
namespace KroneckerColoring
open KroneckerStack KroneckerCompatibility KroneckerComponent KroneckerComponentRoots
open scoped BigOperators

abbrev Palette (m : ℕ) := (g : Fin (m+1)) × Fin (Nat.choose m g.val)
abbrev Coloring (m n : ℕ) := Fin n → Palette m

def grade {m : ℕ} (x : Palette m) : ℕ := x.1.val

def zeroColor (m : ℕ) : Palette m := ⟨⟨0,by omega⟩,⟨0,by simp⟩⟩

@[simp]
theorem grade_zero (m : ℕ) : grade (zeroColor m)=0 := rfl

theorem grade_le {m : ℕ} (x : Palette m) : grade x≤m := by
  have h := x.1.isLt
  exact Nat.le_of_lt_succ h

theorem grade_zero_unique {m : ℕ} {x : Palette m} (hx : grade x=0) :
    x=zeroColor m := by
  rcases x with ⟨⟨g,hg⟩,⟨c,hc⟩⟩
  change g=0 at hx
  subst g
  have hc0 : c=0 := by simpa using hc
  subst c
  rfl

def restrict {m n k : ℕ} (g : Coloring m (n+k)) : Coloring m n :=
  fun i => g (i.castAdd k)

def extend {m n : ℕ} (k : ℕ) (g : Coloring m n) : Coloring m (n+k) :=
  Fin.append g (fun _ => zeroColor m)

def ZeroOutside {m n k : ℕ} (g : Coloring m (n+k)) : Prop :=
  ∀ j : Fin k, grade (g (Fin.natAdd n j))=0

@[simp]
theorem restrict_extend {m n : ℕ} (k : ℕ) (g : Coloring m n) :
    restrict (extend k g)=g := by
  funext i
  simp [restrict,extend]

theorem extend_zero_outside {m n : ℕ} (k : ℕ) (g : Coloring m n) :
    ZeroOutside (extend k g) := by
  intro j
  simp [extend]

theorem extend_restrict {m n k : ℕ} {g : Coloring m (n+k)} (hz : ZeroOutside g) :
    extend k (restrict g)=g := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [extend,restrict]
  · intro j
    simpa [extend] using (grade_zero_unique (hz j)).symm

def zeroExtensionEquiv (m n k : ℕ) :
    Coloring m n ≃ {g : Coloring m (n+k) // ZeroOutside g} where
  toFun g := ⟨extend k g,extend_zero_outside k g⟩
  invFun g := restrict g.val
  left_inv g := restrict_extend k g
  right_inv g := Subtype.ext (extend_restrict g.property)

def paint {m : ℕ} (h : Bool) (x : Palette m) : Edge :=
  if h then Edge.H (grade x) else Edge.V (grade x)

@[simp]
theorem paint_grade {m : ℕ} (h : Bool) (x : Palette m) :
    (paint h x).grade=grade x := by
  cases h <;> rfl

def word {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n) : List Edge :=
  List.ofFn (fun i : Fin n => paint (shape i.val) (g i))

/-- The cyclic edge sequence of a finite colored path. Its values on the
first period are the literal colored path. The empty path has a harmless
grade-zero extension. -/
def trace {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n) (i : ℕ) : Edge :=
  if hn : n=0 then Edge.H 0
  else paint (shape (i%n)) (g ⟨i%n,Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩)

theorem trace_before {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n)
    (i : ℕ) (hi : i<n) :
    trace shape g i=paint (shape i) (g ⟨i,hi⟩) := by
  simp [trace,Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hi),Nat.mod_eq_of_lt hi]

theorem segment_ofFn (E : ℕ → Edge) (s n : ℕ) :
    KroneckerComponent.segment E s n=List.ofFn (fun i : Fin n => E (s+i.val)) := by
  induction n generalizing s with
  | zero => simp [KroneckerComponent.segment]
  | succ n ih =>
    rw [KroneckerComponent.segment,ih,List.ofFn_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Nat.add_left_comm,Nat.add_comm]

theorem word_eq_segment {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n) :
    word shape g=KroneckerComponent.segment (trace shape g) 0 n := by
  rw [word,segment_ofFn]
  congr 1
  funext i
  simpa using (trace_before shape g i.val i.isLt).symm

theorem word_grade_bounds {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n) :
    ∀ e ∈ word shape g,e.grade≤m := by
  intro e he
  simp only [word,List.mem_ofFn] at he
  obtain ⟨i,rfl⟩ := he
  simpa using grade_le (g i)

theorem restrict_word {m n k : ℕ} (shape : ℕ → Bool) (g : Coloring m (n+k)) :
    word shape (restrict g)=KroneckerComponent.segment (trace shape g) 0 n := by
  rw [word,segment_ofFn]
  congr 1
  funext i
  simpa [restrict, Fin.castAdd, Fin.castLE] using (trace_before shape g i.val (by omega)).symm

theorem zero_outside_trace {m n k : ℕ} (shape : ℕ → Bool)
    {g : Coloring m (n+k)} (hz : ZeroOutside g) :
    ∀ j,n≤j→j<n+k→(trace shape g j).grade=0 := by
  intro j hj hjk
  rw [trace_before shape g j hjk,paint_grade]
  have h := hz ⟨j-n,by omega⟩
  simpa only [Fin.natAdd, Nat.add_sub_of_le hj] using h

def HTotal {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n) : ℤ :=
  ∑ i : Fin n,hGrade (paint (shape i.val) (g i))

def VTotal {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n) : ℤ :=
  ∑ i : Fin n,vGrade (paint (shape i.val) (g i))

def HEdges (shape : ℕ → Bool) (n : ℕ) : ℤ :=
  ∑ i : Fin n,if shape i.val then 1 else 0

def VEdges (shape : ℕ → Bool) (n : ℕ) : ℤ :=
  ∑ i : Fin n,if shape i.val then 0 else 1

theorem word_stat {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n) (f : Edge → ℤ) :
    ((word shape g).map f).sum=∑ i : Fin n,f (paint (shape i.val) (g i)) := by
  simp [word,List.map_ofFn,List.sum_ofFn]

theorem word_debt {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n) :
    ((word shape g).map Edge.debtChange).sum=HTotal shape g-VEdges shape n := by
  rw [word_stat]
  simp only [HTotal,VEdges,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : shape i.val <;> simp [paint,Edge.debtChange,hGrade]

theorem word_credit {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n) :
    credit (word shape g)=HEdges shape n-VTotal shape g := by
  rw [credit,word_stat]
  simp only [HEdges,VTotal,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : shape i.val <;> simp [paint,Edge.credit,vGrade]

theorem node_totals {m n c : ℕ} (shape : ℕ → Bool) (g : Coloring m n)
    (hc : NodeRun (word shape g) c) :
    HTotal shape g=VEdges shape n ∧ HEdges shape n-VTotal shape g=(c:ℤ)+1 := by
  have hd := node_debt_balance hc
  have hb := node_credit hc
  rw [word_debt] at hd
  rw [word_credit] at hb
  exact ⟨by omega,hb⟩

theorem extend_htotal {m n : ℕ} (shape : ℕ → Bool) (k : ℕ) (g : Coloring m n) :
    HTotal shape (extend k g)=HTotal shape g := by
  rw [HTotal,Fin.sum_univ_add]
  have hz : (∑ j : Fin k,hGrade (paint (shape (Fin.natAdd n j).val)
      (extend k g (Fin.natAdd n j))))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    cases h : shape (Fin.natAdd n j).val <;> simp [paint,extend,hGrade]
  rw [hz,add_zero]
  simp [extend,HTotal]

theorem extend_vtotal {m n : ℕ} (shape : ℕ → Bool) (k : ℕ) (g : Coloring m n) :
    VTotal shape (extend k g)=VTotal shape g := by
  rw [VTotal,Fin.sum_univ_add]
  have hz : (∑ j : Fin k,vGrade (paint (shape (Fin.natAdd n j).val)
      (extend k g (Fin.natAdd n j))))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    cases h : shape (Fin.natAdd n j).val <;> simp [paint,extend,vGrade]
  rw [hz,add_zero]
  simp [extend,VTotal]

end KroneckerColoring
