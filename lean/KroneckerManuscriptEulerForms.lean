import KroneckerManuscriptQuiverDefinitions

/-! Integer Euler and Tits forms on the manuscript's quivers.
The formulas are defined for every finite quiver, hence for the acyclic case. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace KroneckerManuscriptQuiverDefinitions.Quiver

def EulerForm (H : Quiver) [Fintype H.Vert] [Fintype H.Edge]
    (d δ : H.Vert → ℤ) : ℤ :=
  (∑ v, d v * δ v) - ∑ e, d (H.source e) * δ (H.target e)

def TitsForm (H : Quiver) [Fintype H.Vert] [Fintype H.Edge]
    (d : H.Vert → ℤ) : ℤ := H.EulerForm d d

theorem tits_eq_euler (H : Quiver) [Fintype H.Vert] [Fintype H.Edge]
    (d : H.Vert → ℤ) : H.TitsForm d = H.EulerForm d d := rfl

end KroneckerManuscriptQuiverDefinitions.Quiver

namespace KroneckerManuscriptEulerForms
open KroneckerManuscriptQuiverDefinitions KroneckerLinearCoverBlocks
open KroneckerSparseBlockQuiver KroneckerCoverTitsForm

@[reducible] def supportQuiver (B : LinearCoverBlock) : Quiver where
  Vert := Vertex B
  Edge := Arrow B
  delta a := (source B a,target B a)

instance (B : LinearCoverBlock) : Fintype (supportQuiver B).Vert :=
  inferInstanceAs (Fintype (Vertex B))
instance (B : LinearCoverBlock) : Fintype (supportQuiver B).Edge :=
  by classical exact inferInstanceAs (Fintype (Arrow B))

def dimension (B : LinearCoverBlock) (v : (supportQuiver B).Vert) : ℤ :=
  Module.finrank ℂ (vertexSpace B v)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem block_tits_eq (B : LinearCoverBlock) :
    (supportQuiver B).TitsForm (dimension B) = titsForm B := by
  simpa only [Quiver.TitsForm,Quiver.EulerForm,supportQuiver,dimension,
    Quiver.source,Quiver.target,pow_two] using sparse_euler_form B

theorem block_tits_one (B : LinearCoverBlock) (h : titsForm B = 1) :
    (supportQuiver B).TitsForm (dimension B) = 1 := (block_tits_eq B).trans h

end KroneckerManuscriptEulerForms

#print axioms KroneckerManuscriptQuiverDefinitions.Quiver.EulerForm
#print axioms KroneckerManuscriptQuiverDefinitions.Quiver.TitsForm
#print axioms KroneckerManuscriptQuiverDefinitions.Quiver.tits_eq_euler
#print axioms KroneckerManuscriptEulerForms.supportQuiver
#print axioms KroneckerManuscriptEulerForms.dimension
#print axioms KroneckerManuscriptEulerForms.block_tits_eq
#print axioms KroneckerManuscriptEulerForms.block_tits_one
