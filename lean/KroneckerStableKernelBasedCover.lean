import KroneckerStableMatrixKernelCover

/-! Adding a stable base point to each nonempty kernel chart gives an indexed
open cover with a fixed source frame on every member. Empty charts are omitted. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableKernelBasedCover
open KroneckerStableMatrixKernelCover KroneckerStableRectangularMatrices
variable (m a b : ℕ)
abbrev Index := Σ S : Matrix (Fin m × Fin a) (Fin b) ℂ,chart S
def domain (c : Index m a b) : Set (Stable m a b) := chart c.1
theorem domain_open (c : Index m a b) : IsOpen (domain m a b c) := chart_open c.1
theorem cover (ha : 0<a) (M : Stable m a b) : ∃ c : Index m a b,M ∈ domain m a b c := by
  obtain ⟨S,hS⟩ := KroneckerStableMatrixKernelCover.cover ha M
  exact ⟨⟨S,⟨M,hS⟩⟩,hS⟩
end KroneckerStableKernelBasedCover
