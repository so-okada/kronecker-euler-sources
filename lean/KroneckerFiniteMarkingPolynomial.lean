import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
namespace KroneckerFiniteMarkingPolynomial
open MvPolynomial Finsupp
open scoped BigOperators

variable {A D : Type*} [Fintype A] [Fintype D]

/-- The exponent profile records the actual available marks in each class. -/
noncomputable def profilePolynomial (N : A → D → ℕ) : MvPolynomial D ℚ :=
  ∑ a,monomial (Finsupp.equivFunOnFinite.symm (N a)) 1


theorem first_marking_derivative (N : A → D → ℕ) (d : D) :
    eval (fun _ => (1 : ℚ)) (pderiv d (profilePolynomial N))=
      ∑ a,(N a d : ℚ) := by
  classical
  simp [profilePolynomial,map_sum,pderiv_monomial,eval_monomial,Finsupp.prod]

/-- Repeated differentiation selects two ordered distinct marks. -/
theorem repeated_marking_derivative (N : A → D → ℕ) (d : D) :
    eval (fun _ => (1 : ℚ)) (pderiv d (pderiv d (profilePolynomial N)))=
      ∑ a,(N a d : ℚ)*(N a d-1 : ℕ) := by
  classical
  simp [profilePolynomial,map_sum,pderiv_monomial,eval_monomial,Finsupp.prod,Finsupp.tsub_apply]

theorem mixed_marking_derivative (N : A → D → ℕ) {d e : D} (hde : d≠e) :
    eval (fun _ => (1 : ℚ)) (pderiv e (pderiv d (profilePolynomial N)))=
      ∑ a,(N a d : ℚ)*N a e := by
  classical
  simp [profilePolynomial,map_sum,pderiv_monomial,eval_monomial,Finsupp.prod,Finsupp.tsub_apply,hde]

end KroneckerFiniteMarkingPolynomial
