import KroneckerPairStableSubobjectCases

/- Original module: KroneckerFareyLeftProperWeight -/
section
/-! A proper stable subobject of the lower-slope endpoint has negative total character. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyLeftProperWeight
open KroneckerFareyWeightIdentity
theorem negative (a b c d u w : ℤ) (ha : 0<a) (hc : 0<c)
 (h : a*d-c*b=1) (hu : u≤a) (hw : weight a b u w<0) :
 weight (a+c) (b+d) u w<0 := by
 have hi := left a b c d u w h
 have hh : weight a b u w≤ -1 := by omega
 have hm := mul_le_mul_of_nonneg_left hh (show 0≤a+c by omega)
 nlinarith
end KroneckerFareyLeftProperWeight
end
end

/- Original module: KroneckerFareySubobjectLeftCases -/
section
/-! Lower-endpoint subobjects have total weight zero, negative, or one with the corresponding geometric alternatives. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareySubobjectLeftCases
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractPairStability KroneckerFareyWeightIdentity
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
theorem cases {R : Rep m V W} (hs : Stable R) (U : Subobject R) (c d : ℕ)
 (ha : 0<finrank ℂ V) (hc : 0<c) (hdet : (finrank ℂ V:ℤ)*d-c*(finrank ℂ W)=1) :
 let q := weight ((finrank ℂ V:ℤ)+c) ((finrank ℂ W:ℤ)+d) (finrank ℂ U.source) (finrank ℂ U.sink)
 (q=0 ∧ U.source=⊥ ∧ U.sink=⊥) ∨ q≤ -1 ∨ (q=1 ∧ U.source=⊤ ∧ U.sink=⊤) := by
 dsimp
 rcases KroneckerPairStableSubobjectCases.cases hs U with h|h|h
 · left;rcases h with ⟨h,g⟩;rw [h,g];simp [weight]
 · right;left
   have hu : (finrank ℂ U.source:ℤ)≤finrank ℂ V := by exact_mod_cast U.source.finrank_le
   have hh := KroneckerFareyLeftProperWeight.negative _ _ (c:ℤ) d _ _ (by exact_mod_cast ha) (by exact_mod_cast hc) hdet hu h
   omega
 · right;right;rcases h with ⟨h,g⟩;rw [h,g];simp only [finrank_top]
   exact ⟨(endpoints _ _ _ _ hdet).1,True.intro,True.intro⟩
end KroneckerFareySubobjectLeftCases
end
end
