import KroneckerChainLatticeParameters

set_option autoImplicit false
namespace KroneckerLatticeFiberCount
open KroneckerChainLatticeParameters KroneckerFiniteStateBins KroneckerFiniteBinLattices
open KroneckerChainIncidence

/-- There are two independent lattice choices at every connector, including the last. -/
theorem lattice_fiber_card {n : ℕ} (x : ℝ) (P : StateBins n) :
    (Fintype.card (LatticeFor x P) : ℝ)=∏ t : Connector n,
      (Fintype.card (BinPoint x (offset x t) (stateValue (P.1 t))) : ℝ)*
      (Fintype.card (PositiveBinPoint x (-offset x t) (rightBin P.2 t)) : ℝ) := by
  simp only [LatticeFor,LeftPoints,RightPoints,Fintype.card_prod,Fintype.card_pi,
    Nat.cast_mul,Nat.cast_prod,Finset.prod_mul_distrib]

theorem lattice_fiber_lower {n : ℕ} (x : ℝ) (P : StateBins n) (hx : 256≤x) :
    (x/256-1)^(2*(n+1))≤(Fintype.card (LatticeFor x P) : ℝ) := by
  have hq : 0≤x/256-1 := by linarith
  rw [lattice_fiber_card]
  calc
    (x/256-1)^(2*(n+1))=∏ _t : Connector n,(x/256-1)*(x/256-1) := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_two,←pow_mul]
    _≤_ := Finset.prod_le_prod₀ (fun _ _ => mul_nonneg hq hq) (fun t _ =>
      mul_le_mul (bin_point_lower x (offset x t) _ (by linarith))
        (positive_bin_point_lower x (-offset x t) _ (by linarith)) hq (by positivity))


end KroneckerLatticeFiberCount
