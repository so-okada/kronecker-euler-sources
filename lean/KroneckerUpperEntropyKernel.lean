import KroneckerLowerEntropyTransfer

/-! An actual positive observable bounded by C*beta^a*R^k/k has joint
entropy limsup at most log beta. Positivity before applying log is explicit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUpperEntropyKernel
open Filter KroneckerLowerEntropyKernel KroneckerLowerEntropyTransfer
open scoped Topology

def upper (C R : ℝ) (a k : ℕ) : ℝ := C/(k : ℝ)*(256/27 : ℝ)^a*R^k
def correction (C R : ℝ) (a k : ℕ) : ℝ := Real.log C/a + (k : ℝ)/a*Real.log R





variable {α : Type*} {l : Filter α} (a k : α → ℕ)

theorem correction_tendsto (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0)) (C R : ℝ) :
    Tendsto (fun i => correction C R (a i) (k i)) l (𝓝 0) := by
  have h₁ := constant_over_height a ha (Real.log C)
  have h₂ := hk.mul_const (Real.log R)
  simpa [correction] using h₁.add h₂

def UpperLimit (l : Filter α) (f : α → ℝ) (L : ℝ) : Prop :=
  ∀ c : ℝ, L < c → ∀ᶠ i in l, f i ≤ c


theorem tendsto_of_bounds {f : α → ℝ} {L : ℝ}
    (hl : LowerLimit l f L) (hu : UpperLimit l f L) : Tendsto f l (𝓝 L) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    obtain ⟨d, hcd, hd⟩ := exists_between hc
    exact (hl d hd).mono fun _ h => hcd.trans_le h
  · intro c hc
    obtain ⟨d, hd, hdc⟩ := exists_between hc
    exact (hu d hd).mono fun _ h => h.trans_lt hdc




end KroneckerUpperEntropyKernel
