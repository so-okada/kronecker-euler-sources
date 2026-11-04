import KroneckerManuscriptExchangeDefinitions
import KroneckerNaturalNodes

/-! The manuscript's double-plus notation, balance operations, and geometric
adjacent-exchange parameters. `true` denotes E and `false` denotes N.
List concatenation is Lean's `++`; path concatenation is `concat`.
No additional external input is used. -/
noncomputable section
set_option autoImplicit false

namespace KroneckerManuscriptNotationSync
open KroneckerPaperPaths KroneckerStack KroneckerDebtUnits
open KroneckerManuscriptExchangeDefinitions

scoped infixr:65 " ⧺ " => KroneckerPaperPaths.concat

@[simp] theorem concat_direction_lists (U V : TNEPath) :
    (U ⧺ V).steps = U.steps ++ V.steps := rfl
@[simp] theorem concat_empty_left (P : TNEPath) : empty ⧺ P = P := empty_concat P
@[simp] theorem concat_empty_right (P : TNEPath) : P ⧺ empty = P := concat_empty P

theorem vertical_domain_iff (h : ℕ) (z : BalState) :
    VDomain h z ↔ ∃ z', KroneckerBoundaryListComparison.step z (.V h) = some z' := by
  rcases z with ⟨b,L⟩
  cases L with
  | nil => simp [VDomain, KroneckerBoundaryListComparison.step]
  | cons a L =>
    simp only [VDomain, List.cons.injEq]
    constructor
    · rintro ⟨a', L', ⟨ha, hL⟩, hi⟩
      subst a'; subst L'
      exact ⟨⟨b - (h : ℤ), L⟩, by simp [KroneckerBoundaryListComparison.step, hi]⟩
    · rintro ⟨z', hz⟩
      by_cases hi : a ≤ b - (h : ℤ)
      · exact ⟨a,L,⟨rfl,rfl⟩,hi⟩
      · simp [KroneckerBoundaryListComparison.step, hi] at hz

/-- The comparison assertion at every prefix, including the empty prefix. -/
theorem balance_comparison_prefixes {δ : ℕ} {z z' zf : BalState}
    {es : List KroneckerStack.Edge}
    (hb : z'.balance = z.balance + (δ : ℤ))
    (hL : ListComparison (δ : ℤ) z.stack z'.stack)
    (hex : KroneckerBoundaryListComparison.execute es z = some zf) (r : ℕ) :
    ∃ w w', KroneckerBoundaryListComparison.execute (es.take r) z = some w ∧
      KroneckerBoundaryListComparison.execute (es.take r) z' = some w' ∧
      w'.balance = w.balance + (δ : ℤ) ∧
      ListComparison (δ : ℤ) w.stack w'.stack ∧ w.stack.length = w'.stack.length := by
  have hc : KroneckerBoundaryListComparison.Compared (δ : ℤ) z z' := ⟨hb,hL⟩
  have he : KroneckerBoundaryListComparison.execute (es.take r ++ es.drop r) z = some zf := by
    simpa only [List.take_append_drop] using hex
  obtain ⟨w,w',hw,hw',hww,hlen⟩ := KroneckerBoundaryListComparison.prefix_comparison hc he
  exact ⟨w,w',hw,hw',hww.1,hww.2,hlen⟩
end KroneckerManuscriptNotationSync

namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths
open KroneckerPaperPathGradings (Horizontal Vertical)

def horizontalPrefix (Y : TNEPath) (r : ℕ) : List (Horizontal Y) :=
  ((List.ofFn (edgeEquiv Y)).take r).filterMap fun e =>
    if h : Y.steps.get ((edgeEquiv Y).symm e) = true then some ⟨e,h⟩ else none

/-- The reverse path-ordered list in Definition 9.2. The explicit precursor
argument is immaterial whenever it satisfies the h-precursor condition. -/
def BalList {Y : TNEPath} (g : Grading Y) (p : Vertical Y → Horizontal Y)
    (r : ℕ) : List ℤ :=
  (horizontalPrefix Y r).reverse.flatMap fun x =>
    List.replicate (Debt g p x r).toNat (eBal g x.val)

@[simp] theorem BalList_zero {Y : TNEPath} (g : Grading Y)
    (p : Vertical Y → Horizontal Y) : BalList g p 0 = [] := by
  simp [BalList, horizontalPrefix]

theorem BalList_precursor_independent {Y : TNEPath} (g : Grading Y)
    (p q : Vertical Y → Horizontal Y) (hp : IsHPrecursor g p)
    (hq : IsHPrecursor g q) (r : ℕ) : BalList g p r = BalList g q r := by
  rw [hPrecursor_unique g p q hp hq]

theorem BalList_repeat_count {Y : TNEPath} (g : Grading Y)
    (p : Vertical Y → Horizontal Y) (hp : IsHPrecursor g p)
    (x : Horizontal Y) (r : ℕ) (hr : r ≤ Y.steps.length) :
    ((Debt g p x r).toNat : ℤ) = Debt g p x r :=
  Int.toNat_of_nonneg (debt_nonnegative g p hp x r hr)
end KroneckerNaturalPathGradings

namespace KroneckerManuscriptExchangeDefinitions.AdjShellExch
open KroneckerPaperPaths

def X (ξ : AdjShellExch) : TNEPath := KroneckerAdjacentExchangeLemma.source ξ.spec ξ.origin
def X' (ξ : AdjShellExch) : TNEPath :=
  ofSteps (KroneckerExchangePath.targetPath ξ.right ξ.P ξ.Q) ξ.origin
def Y (ξ : AdjShellExch) : TNEPath :=
  KroneckerManuscriptShell.path ξ.X (ξ.u.val+1) (ξ.v.val+1)
def Y' (ξ : AdjShellExch) : TNEPath :=
  KroneckerManuscriptShell.path ξ.X' (ξ.u.val+1) (ξ.v.val+1)

def r (ξ : AdjShellExch) : ℕ := ξ.u.val + 1 + 2 + ξ.P.length
def i (ξ : AdjShellExch) : ℕ := ξ.P.count true + 3
def j (ξ : AdjShellExch) : ℕ := ξ.u.val + 1 + ξ.P.count false + 1

theorem source_steps (ξ : AdjShellExch) :
    ξ.X.steps = [true] ++ ξ.P ++ (if ξ.right then [true,false] else [false,true]) ++ ξ.Q := by
  cases h : ξ.right <;> simp [X, spec, KroneckerAdjacentExchangeLemma.spec,
    KroneckerAdjacentExchangeLemma.source, KroneckerWrappedExchangeWitness.ExchangeSpec.source,
    KroneckerExchangePath.sourcePath, h, List.append_assoc]

theorem source_origin (ξ : AdjShellExch) : ξ.X.origin = ξ.origin := by
  apply ofSteps_origin_of_ne_nil
  change KroneckerExchangePath.sourcePath ξ.right ξ.P ξ.Q ≠ []
  cases ξ.right <;> simp [KroneckerExchangePath.sourcePath]

theorem same_step_counts (ξ : AdjShellExch) (b : Bool) :
    ξ.X.steps.count b = ξ.X'.steps.count b := by
  cases h : ξ.right <;> cases b <;>
    simp [X, X', spec, KroneckerAdjacentExchangeLemma.spec,
      KroneckerAdjacentExchangeLemma.source, KroneckerWrappedExchangeWitness.ExchangeSpec.source,
      KroneckerExchangePath.sourcePath, KroneckerExchangePath.targetPath, h,
      List.count_append, Nat.add_comm, Nat.add_left_comm]

theorem target_eq (ξ : AdjShellExch) :
    ξ.Y' = KroneckerAdjacentExchangeLemma.target ξ.spec := rfl

/-- The map retains the geometric source origin carried by ξ. -/
def exchange (ξ : AdjShellExch) :
    KroneckerAdjacentExchangeLemma.ColoredSet ξ.X →
      KroneckerAdjacentExchangeLemma.ColoredSet ξ.Y' :=
  KroneckerAdjacentExchangeLemma.exchange ξ.spec ξ.origin

theorem exchange_surplus (ξ : AdjShellExch)
    (a : KroneckerAdjacentExchangeLemma.ColoredSet ξ.X) :
    a.1 ≤ (ξ.exchange a).1 ∧ (ξ.exchange a).1 ≤ a.1 + 3 :=
  KroneckerAdjacentExchangeLemma.exchange_surplus ξ.spec ξ.origin a

theorem exchange_fiber (ξ : AdjShellExch)
    (b : KroneckerAdjacentExchangeLemma.ColoredSet ξ.Y') :
    Nat.card {a // ξ.exchange a = b} ≤ 8 :=
  KroneckerAdjacentExchangeLemma.exchange_fiber ξ.spec ξ.origin b
end KroneckerManuscriptExchangeDefinitions.AdjShellExch

#print axioms KroneckerManuscriptNotationSync.concat_direction_lists
#print axioms KroneckerManuscriptNotationSync.concat_empty_left
#print axioms KroneckerManuscriptNotationSync.concat_empty_right
#print axioms KroneckerManuscriptNotationSync.vertical_domain_iff
#print axioms KroneckerManuscriptNotationSync.balance_comparison_prefixes
#print axioms KroneckerNaturalPathGradings.BalList
#print axioms KroneckerNaturalPathGradings.BalList_zero
#print axioms KroneckerNaturalPathGradings.BalList_precursor_independent
#print axioms KroneckerNaturalPathGradings.BalList_repeat_count
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.X
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.X'
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.Y
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.Y'
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.r
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.i
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.j
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.source_steps
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.source_origin
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.same_step_counts
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.target_eq
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.exchange
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.exchange_surplus
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.exchange_fiber

namespace KroneckerManuscriptNotationSync
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerAdjacentExchangeLemma
open KroneckerManuscriptExchangeDefinitions

def shellColors {X : TNEPath} (u v : Fin 2) (a : ColoredGrading 3 X) :
    ColoredGrading 3 (KroneckerManuscriptShell.path X (u.val+1) (v.val+1)) :=
  KroneckerManuscriptShell.coloring X a.1 a.2 (u.val+1) (v.val+1) 1 0
    (by have := u.isLt; omega) (by have := v.isLt; omega) (by decide)

/-- The set of maps satisfying the wrapped-exchange conclusions. The count
conditions record the equal path lengths inherent in an exchange decomposition. -/
def WrapExch (X X' : TNEPath) (u v : Fin 2) :
    Set (ColoredSet X → ColoredSet (KroneckerManuscriptShell.path X' (u.val+1) (v.val+1))) :=
  {Φ | X.steps.count true = X'.steps.count true ∧
    X.steps.count false = X'.steps.count false ∧
    (∀ a, (a.1 ≤ (Φ a).1 ∧ (Φ a).1 ≤ a.1 + 3) ∧
      horizontalData (edges (Φ a).2.val) = horizontalData (edges (shellColors u v a.2.val)) ∧
      (((verticalData (edges (shellColors u v a.2.val))).zip
        (verticalData (edges (Φ a).2.val))).filter (fun p => p.1 != p.2)).length ≤ 1) ∧
    ∀ b, Nat.card {a // Φ a = b} ≤ 8}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem adjacent_exchange_mem (ξ : AdjShellExch) :
    ξ.exchange ∈ WrapExch ξ.X ξ.X' ξ.u ξ.v := by
  refine ⟨ξ.same_step_counts true, ξ.same_step_counts false, ?_, ξ.exchange_fiber⟩
  intro a
  have h := KroneckerAdjacentExchangeLemma.exchange_colors ξ.spec ξ.origin a
  rw [← KroneckerAdjacentExchangeLemma.shell_edges ξ.spec a.2.val] at h
  exact ⟨ξ.exchange_surplus a,h⟩

theorem WrapExch_nonempty (ξ : AdjShellExch) :
    (WrapExch ξ.X ξ.X' ξ.u ξ.v).Nonempty := ⟨ξ.exchange,adjacent_exchange_mem ξ⟩
end KroneckerManuscriptNotationSync

#print axioms KroneckerManuscriptNotationSync.WrapExch
#print axioms KroneckerManuscriptNotationSync.adjacent_exchange_mem
#print axioms KroneckerManuscriptNotationSync.WrapExch_nonempty
