import KroneckerPairStableSubobjectCases

/- Original module: KroneckerFareyRightProperWeight -/
section
/-! A proper stable subobject of the upper-slope endpoint has total character at most minus two. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyRightProperWeight
open KroneckerFareyWeightIdentity
theorem negative_two (a b c d u w : ℤ) (ha : 0<a) (hc : 0<c)
 (h : a*d-c*b=1) (hu : 0≤u) (hw : weight c d u w<0) :
 weight (a+c) (b+d) u w≤ -2 := by
 have hi := right a b c d u w h
 have hh : weight c d u w≤ -1 := by omega
 have hm := mul_le_mul_of_nonneg_left hh (show 0≤a+c by omega)
 have : weight (a+c) (b+d) u w< -1 := by nlinarith
 omega
end KroneckerFareyRightProperWeight
end
end

/- Original module: KroneckerFareySubobjectRightCases -/
section
/-! Upper-endpoint subobjects have total weight zero, at most minus two, or minus one with geometric alternatives. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareySubobjectRightCases
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractPairStability KroneckerFareyWeightIdentity
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
theorem cases {S : Rep m V W} (hs : Stable S) (U : Subobject S) (a b : ℕ)
 (ha : 0<a) (hc : 0<finrank ℂ V) (hdet : (a:ℤ)*finrank ℂ W-(finrank ℂ V:ℤ)*b=1) :
 let q := weight ((a:ℤ)+finrank ℂ V) ((b:ℤ)+finrank ℂ W) (finrank ℂ U.source) (finrank ℂ U.sink)
 (q=0 ∧ U.source=⊥ ∧ U.sink=⊥) ∨ q≤ -2 ∨ (q= -1 ∧ U.source=⊤ ∧ U.sink=⊤) := by
 dsimp
 rcases KroneckerPairStableSubobjectCases.cases hs U with h|h|h
 · left;rcases h with ⟨h,g⟩;rw [h,g];simp [weight]
 · right;left
   exact KroneckerFareyRightProperWeight.negative_two _ _ _ _ _ _ (by exact_mod_cast ha) (by exact_mod_cast hc) hdet (by positivity) h
 · right;right;rcases h with ⟨h,g⟩;rw [h,g];simp only [finrank_top]
   exact ⟨(endpoints _ _ _ _ hdet).2,True.intro,True.intro⟩
end KroneckerFareySubobjectRightCases
end
end
