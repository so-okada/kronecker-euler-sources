import KroneckerManuscriptDimensions

/-! The total dimensions in Definition 7.16 require finite support, not a finite
ambient quiver. These sums agree with the finite-vertex definitions. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Classical
namespace KroneckerManuscriptQuiverDefinitions.Representation

/-- Dimension sum over one specified part of a finite-support representation. -/
def partDim {Q : Quiver} (R : Representation Q) (hR : R.support.Finite)
    (S : Set Q.Vert) : ℕ := by
  classical
  exact ∑ v ∈ hR.toFinset, if v ∈ S then R.dimension v else 0

def finiteSrcDim {Q : Quiver} (B : Q.Bipartition)
    (R : Representation Q) (hR : R.support.Finite) : ℕ := R.partDim hR B.sources

def finiteSnkDim {Q : Quiver} (B : Q.Bipartition)
    (R : Representation Q) (hR : R.support.Finite) : ℕ := R.partDim hR B.sinks

def finiteTotalDimensionPair {Q : Quiver} (B : Q.Bipartition)
    (R : Representation Q) (hR : R.support.Finite) : ℕ × ℕ :=
  (R.finiteSrcDim B hR, R.finiteSnkDim B hR)

theorem dimension_eq_zero_outside_support {Q : Quiver} (R : Representation Q)
    {v : Q.Vert} (hv : v ∉ R.support) : R.dimension v = 0 := by
  have h := mt (R.mem_support_iff_dimension_pos v).mpr hv
  omega

theorem partDim_eq_sum {Q : Quiver} [Fintype Q.Vert]
    (R : Representation Q) (hR : R.support.Finite) (S : Set Q.Vert) :
    R.partDim hR S = ∑ v, if v ∈ S then R.dimension v else 0 := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  have hz : R.dimension v = 0 :=
    R.dimension_eq_zero_outside_support (by simpa only [Set.Finite.mem_toFinset] using hv)
  simp [hz]

@[simp] theorem finiteSrcDim_eq {Q : Quiver} [Fintype Q.Vert]
    (B : Q.Bipartition) (R : Representation Q) (hR : R.support.Finite) :
    R.finiteSrcDim B hR = R.SrcDim B := R.partDim_eq_sum hR B.sources

@[simp] theorem finiteSnkDim_eq {Q : Quiver} [Fintype Q.Vert]
    (B : Q.Bipartition) (R : Representation Q) (hR : R.support.Finite) :
    R.finiteSnkDim B hR = R.SnkDim B := R.partDim_eq_sum hR B.sinks

@[simp] theorem finiteTotalDimensionPair_eq {Q : Quiver} [Fintype Q.Vert]
    (B : Q.Bipartition) (R : Representation Q) (hR : R.support.Finite) :
    R.finiteTotalDimensionPair B hR = R.totalDimensionPair B := by
  simp [finiteTotalDimensionPair, totalDimensionPair]

end KroneckerManuscriptQuiverDefinitions.Representation
