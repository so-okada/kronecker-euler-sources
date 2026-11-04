import KroneckerBoundaryListComparison
import KroneckerExchangeIntermediateLemma

noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptExchangeDefinitions
open KroneckerDebtUnits KroneckerStack

abbrev IntList := List ℤ
abbrev BalState := UnitState

/-- The boundary balance list represented by a compressed stack state. -/
def BalList (z : State) : IntList := units z.stack

theorem flatten_stack (z : State) : (flatten z).stack = BalList z := rfl

def HStep (s : ℕ) (z : BalState) : BalState :=
  ⟨z.balance + 1, List.replicate s (z.balance + 1) ++ z.stack⟩
def VDomain (h : ℕ) (z : BalState) : Prop :=
  ∃ a L, z.stack = a :: L ∧ a ≤ z.balance - (h : ℤ)
def VStep (h : ℕ) (z : {z : BalState // VDomain h z}) : BalState :=
  ⟨z.val.balance - (h : ℤ), z.val.stack.tail⟩
def ListComparison (δ : ℤ) (L L' : IntList) : Prop :=
  List.Forall₂ (fun a a' => a' ≤ a + δ) L L'

theorem horizontal_step (s : ℕ) (z : BalState) :
    KroneckerBoundaryListComparison.step z (.H s) = some (HStep s z) := rfl

theorem vertical_step (h : ℕ) (z : {z : BalState // VDomain h z}) :
    KroneckerBoundaryListComparison.step z.val (.V h) = some (VStep h z) := by
  obtain ⟨a, L, hs, ha⟩ := z.property
  simp [KroneckerBoundaryListComparison.step, VStep, hs, ha]

theorem comparison_iff (δ : ℤ) (z z' : BalState) :
    KroneckerBoundaryListComparison.Compared δ z z' ↔
      z'.balance = z.balance + δ ∧ ListComparison δ z.stack z'.stack := Iff.rfl

/-- P and Q are NE-path direction lists. `right=true` encodes (A,B)=(EN,NE);
`right=false` encodes (NE,EN). Fin 2 encodes the manuscript's positive lengths 1,2. -/
structure AdjShellExch where
  P : List Bool
  Q : List Bool
  origin : KroneckerPaperPaths.LatticePoint
  u : Fin 2
  v : Fin 2
  right : Bool

def AdjShellExch.spec (ξ : AdjShellExch) :
    KroneckerWrappedExchangeWitness.ExchangeSpec 3 :=
  KroneckerAdjacentExchangeLemma.spec ξ.right ξ.P ξ.Q (ξ.u.val+1) (ξ.v.val+1)
    (by have := ξ.u.isLt; omega) (by have := ξ.v.isLt; omega)

abbrev repairIndex := KroneckerExchangeIntermediateLemma.changeIndex
abbrev repairIndex_horizontal := @KroneckerExchangeIntermediateLemma.changeIndex_sameDebt
abbrev balance_operations_comparison := @KroneckerBoundaryListComparison.execute_comparison
end KroneckerManuscriptExchangeDefinitions

#print axioms KroneckerManuscriptExchangeDefinitions.HStep
#print axioms KroneckerManuscriptExchangeDefinitions.BalList
#print axioms KroneckerManuscriptExchangeDefinitions.flatten_stack
#print axioms KroneckerManuscriptExchangeDefinitions.VDomain
#print axioms KroneckerManuscriptExchangeDefinitions.VStep
#print axioms KroneckerManuscriptExchangeDefinitions.ListComparison
#print axioms KroneckerManuscriptExchangeDefinitions.horizontal_step
#print axioms KroneckerManuscriptExchangeDefinitions.vertical_step
#print axioms KroneckerManuscriptExchangeDefinitions.comparison_iff
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch
#print axioms KroneckerManuscriptExchangeDefinitions.AdjShellExch.spec
#print axioms KroneckerManuscriptExchangeDefinitions.repairIndex
#print axioms KroneckerManuscriptExchangeDefinitions.repairIndex_horizontal
#print axioms KroneckerManuscriptExchangeDefinitions.balance_operations_comparison
