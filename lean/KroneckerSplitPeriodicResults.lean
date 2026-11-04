import KroneckerManuscriptPeriodic

/-! Periodic counts, shifted supermultiplicativity, the limit and its finite bound. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace KroneckerSplitPeriodicResults
open KroneckerPaperPaths KroneckerNaturalPathGradings

def periodicCount (m : ℕ) (W : TNEPath) (j : ℕ) : ℕ :=
  connectedCount m (power W j) 0

theorem shifted_supermultiplicativity (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) (i j : ℕ) :
    periodicCount m (runPath rs o) i *
        periodicCount m (runPath rs o) j ≤
      periodicCount m (runPath rs o) (i+j+2) :=
  KroneckerManuscriptPeriodic.shifted_supermultiplicativity m hm rs o hne hr i j

theorem limit_eq_sup (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) :
    Tendsto (fun j : ℕ =>
      Real.log (periodicCount m (runPath rs o) j : ℝ) / (j : ℝ))
      atTop (𝓝 (sSup ((fun j : ℕ =>
        Real.log (periodicCount m (runPath rs o) j : ℝ) /
          ((j : ℝ)+2)) '' Set.Ici 1))) ∧
    0 < sSup ((fun j : ℕ =>
      Real.log (periodicCount m (runPath rs o) j : ℝ) /
        ((j : ℝ)+2)) '' Set.Ici 1) :=
  KroneckerManuscriptPeriodic.limit_eq_sup m hm rs o hne hr

theorem finite_bound (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) (j : ℕ) :
    (periodicCount m (runPath rs o) j : ℝ) ≤
      Real.exp (((j : ℝ)+2) * limUnder atTop (fun k : ℕ =>
        Real.log (periodicCount m (runPath rs o) k : ℝ) / (k : ℝ))) :=
  KroneckerManuscriptPeriodic.finite_bound m hm rs o hne hr j

end KroneckerSplitPeriodicResults
#print axioms KroneckerSplitPeriodicResults.shifted_supermultiplicativity
#print axioms KroneckerSplitPeriodicResults.limit_eq_sup
#print axioms KroneckerSplitPeriodicResults.finite_bound
