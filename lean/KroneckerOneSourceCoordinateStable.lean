import KroneckerAbstractCoordinatesStable

/- Original module: KroneckerOneDimensionalSubspace -/
section
/-! A subspace of a one-dimensional complex space is either zero or full. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOneDimensionalSubspace
open Module
theorem dichotomy {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
 (h : finrank ℂ V=1) (U : Submodule ℂ V) : U=⊥ ∨ U=⊤ := by
 have hb := U.finrank_le
 by_cases hz : finrank ℂ U=0
 · exact Or.inl (Submodule.finrank_eq_zero.mp hz)
 · exact Or.inr (Submodule.eq_top_of_finrank_eq (by omega))
end KroneckerOneDimensionalSubspace
end
end

/- Original module: KroneckerOneSourceVectors -/
section
/-! Coordinate unit vectors padded by zero give explicit one-source arrow families. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOneSourceVectors
open KroneckerAbstractPairHom KroneckerFiniteQuiverHom
def vector (m b : ℕ) (i : Fin m) : Space b := fun j => if i.val=j.val then 1 else 0
def family (m b : ℕ) : Rep m ℂ (Space b) := fun i => LinearMap.toSpanSingleton ℂ _ (vector m b i)
theorem evaluate (m b : ℕ) (i : Fin m) : family m b i 1=vector m b i := by simp [family]
end KroneckerOneSourceVectors
end
end

/- Original module: KroneckerOneSourceBasis -/
section
/-! When there are enough arrows, the padded one-source family contains every coordinate basis vector. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOneSourceBasis
open KroneckerFiniteQuiverHom
theorem basis (m b : ℕ) (h : b≤m) (j : Fin b) :
 KroneckerOneSourceVectors.vector m b (Fin.castLE h j)=Pi.basisFun ℂ (Fin b) j := by
 ext k
 simp [KroneckerOneSourceVectors.vector,Pi.basisFun_apply,Pi.single_apply,Fin.ext_iff,eq_comm]
end KroneckerOneSourceBasis
end
end

/- Original module: KroneckerOneSourceSpanning -/
section
/-! Every sink subspace containing all one-source arrow images is the full sink. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOneSourceSpanning
open KroneckerFiniteQuiverHom
theorem top (m b : ℕ) (h : b≤m) (W : Submodule ℂ (Space b))
 (hw : ∀ i,KroneckerOneSourceVectors.family m b i 1∈W) : W=⊤ := by
 apply top_unique
 rw [← (Pi.basisFun ℂ (Fin b)).span_eq]
 apply Submodule.span_le.mpr
 rintro x ⟨j,rfl⟩
 rw [← KroneckerOneSourceBasis.basis m b h j]
 have hj := hw (Fin.castLE h j)
 rw [KroneckerOneSourceVectors.evaluate] at hj
 exact hj
end KroneckerOneSourceSpanning
end
end

/- Original module: KroneckerOneSourceStable -/
section
/-! The explicit spanning one-source family is stable against every invariant subspace. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOneSourceStable
open Module KroneckerAbstractPairStability KroneckerFareyWeightIdentity KroneckerFiniteQuiverHom
theorem stable (m b : ℕ) (h : b≤m) : Stable (KroneckerOneSourceVectors.family m b) := by
 intro U hp hproper
 rcases KroneckerOneDimensionalSubspace.dichotomy (by simp : finrank ℂ ℂ=1) U.source with hs|hs
 · rw [hs] at hp ⊢
   simp only [finrank_bot,zero_add] at hp
   simpa [KroneckerFareyWeightIdentity.weight] using (show -(finrank ℂ U.sink:ℤ)<0 by exact neg_neg_of_pos (by exact_mod_cast hp))
 · have ht : U.sink=⊤ := KroneckerOneSourceSpanning.top m b h U.sink (fun i => U.invariant i 1 (by rw [hs];trivial))
   rw [hs,ht] at hproper
   simp at hproper
end KroneckerOneSourceStable
end
end

/- Original module: KroneckerOneSourceCoordinateStable -/
section
/-! The explicit source-one construction yields a stable representation in canonical coordinates. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOneSourceCoordinateStable
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel
theorem exists_stable (m b : ℕ) (h : b≤m) : ∃ R : PairRep m 1 b,PairStable R := by
 let e : Space 1 ≃ₗ[ℂ] ℂ := (Module.finBasisOfFinrankEq ℂ ℂ (by simp : finrank ℂ ℂ=1)).equivFun.symm
 let f := LinearEquiv.refl ℂ (Space b)
 exact ⟨KroneckerAbstractPairCoordinates.family (KroneckerOneSourceVectors.family m b) e f,
  KroneckerAbstractCoordinatesStable.stable _ _ _ (KroneckerOneSourceStable.stable m b h)⟩
end KroneckerOneSourceCoordinateStable
end
end
