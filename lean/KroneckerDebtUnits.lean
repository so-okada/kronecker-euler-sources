import KroneckerComponentRoots

/-! Expand each node's debt into one copy of its baseline per debt unit. -/
set_option autoImplicit false
namespace KroneckerDebtUnits
open KroneckerStack

def units (xs : List Node) : List ℤ := xs.flatMap (fun x => List.replicate x.debt x.baseline)

structure UnitState where
  balance : ℤ
  stack : List ℤ
  deriving DecidableEq, Repr

def flatten (s : State) : UnitState := ⟨s.balance,units s.stack⟩

def unitStep (s : UnitState) (e : Edge) : Option UnitState :=
  match s.stack with
  | [] => none
  | x::xs => match e with
    | .H g => some ⟨s.balance+1,List.replicate g (s.balance+1)++x::xs⟩
    | .V g => if x ≤ s.balance-(g : ℤ) then some ⟨s.balance-(g : ℤ),xs⟩ else none

def unitExecute : List Edge → UnitState → Option UnitState
  | [],s => some s
  | e::es,s => (unitStep s e).bind (unitExecute es)


theorem units_cons (x : Node) (xs : List Node) :
    units (x::xs)=List.replicate x.debt x.baseline++units xs := rfl


end KroneckerDebtUnits
