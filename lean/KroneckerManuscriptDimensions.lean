import KroneckerManuscriptRevision

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace KroneckerManuscriptQuiverDefinitions.Representation

/-- Total source dimension for the specified fixed bipartition. -/
def SrcDim {Q : Quiver} [Fintype Q.Vert] (B : Q.Bipartition)
    (R : Representation Q) : ℕ := by
  classical
  exact ∑ v : Q.Vert, if v ∈ B.sources then R.dimension v else 0

/-- Total sink dimension for the specified fixed bipartition. -/
def SnkDim {Q : Quiver} [Fintype Q.Vert] (B : Q.Bipartition)
    (R : Representation Q) : ℕ := by
  classical
  exact ∑ v : Q.Vert, if v ∈ B.sinks then R.dimension v else 0

def totalDimensionPair {Q : Quiver} [Fintype Q.Vert] (B : Q.Bipartition)
    (R : Representation Q) : ℕ × ℕ := (R.SrcDim B, R.SnkDim B)

end KroneckerManuscriptQuiverDefinitions.Representation
