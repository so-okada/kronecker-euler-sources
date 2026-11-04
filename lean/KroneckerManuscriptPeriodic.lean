import KroneckerGeometricCounts
import KroneckerManuscriptGradingSets

/-! Proposition 3.8 and Definition 3.9 with natural-valued geometric gradings.
The three proposition statements precede ell and do not use that definition. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace KroneckerManuscriptPeriodic
open KroneckerPaperPaths KroneckerNaturalPathGradings

private theorem power_count (m : ℕ) (rs : List ℕ) (o : LatticePoint) (j : ℕ) :
    connectedCount m (power (runPath rs o) j) 0 =
      KroneckerPeriodicWords.periodicCount m rs j := by
  rw [connectedCount_eq_bounded,
    KroneckerPaperPathGradings.connectedCount_power_runPath]

/-- Claim 1 of Proposition 3.8. -/
theorem shifted_supermultiplicativity (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) (i j : ℕ) :
    connectedCount m (power (runPath rs o) i) 0 *
        connectedCount m (power (runPath rs o) j) 0 ≤
      connectedCount m (power (runPath rs o) (i+j+2)) 0 := by
  simp only [power_count]
  exact KroneckerPeriodicWords.periodicCount_supermultiplicative m hm rs hne hr i j

/-- Claim 2 of Proposition 3.8: convergence to the supremum and positivity. -/
theorem limit_eq_sup (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) :
    Tendsto (fun j : ℕ =>
      Real.log (connectedCount m (power (runPath rs o) j) 0 : ℝ) / (j : ℝ))
      atTop (𝓝 (sSup ((fun j : ℕ =>
        Real.log (connectedCount m (power (runPath rs o) j) 0 : ℝ) /
          ((j : ℝ)+2)) '' Set.Ici 1))) ∧
    0 < sSup ((fun j : ℕ =>
      Real.log (connectedCount m (power (runPath rs o) j) 0 : ℝ) /
        ((j : ℝ)+2)) '' Set.Ici 1) := by
  simp only [connectedCount_eq_bounded]
  rw [← KroneckerPaperPathGradings.geometric_periodic_sup]
  exact ⟨KroneckerPaperPathGradings.geometric_periodic_limit m hm rs o hne hr,
    KroneckerPeriodicGrowth.periodicGrowth_pos m hm rs hne hr⟩

/-- Claim 3 of Proposition 3.8, expressed using the limit. -/
theorem finite_bound (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) (j : ℕ) :
    (connectedCount m (power (runPath rs o) j) 0 : ℝ) ≤
      Real.exp (((j : ℝ)+2) * limUnder atTop (fun k : ℕ =>
        Real.log (connectedCount m (power (runPath rs o) k) 0 : ℝ) / (k : ℝ))) := by
  have ht := KroneckerPaperPathGradings.geometric_periodic_limit m hm rs o hne hr
  simp only [connectedCount_eq_bounded]
  rw [ht.limUnder_eq, mul_comm]
  exact KroneckerPaperPathGradings.geometric_periodic_finite_bound m hm rs o hne hr j

/-- Definition 3.9. Its limit exists for the runs in Proposition 3.8. -/
def ell (m : ℕ) (W : TNEPath) : ℝ :=
  limUnder atTop (fun j : ℕ => Real.log (connectedCount m (power W j) 0 : ℝ) / (j : ℝ))

theorem ell_eq_growth (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) :
    ell m (runPath rs o) = KroneckerPeriodicTail.periodicGrowth m rs := by
  unfold ell
  simp only [connectedCount_eq_bounded]
  exact (KroneckerPaperPathGradings.geometric_periodic_limit m hm rs o hne hr).limUnder_eq

theorem ell_limit (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) :
    Tendsto (fun j : ℕ =>
      Real.log (connectedCount m (power (runPath rs o) j) 0 : ℝ) / (j : ℝ))
      atTop (𝓝 (ell m (runPath rs o))) := by
  rw [ell_eq_growth m hm rs o hne hr]
  simpa only [connectedCount_eq_bounded] using
    KroneckerPaperPathGradings.geometric_periodic_limit m hm rs o hne hr

end KroneckerManuscriptPeriodic

