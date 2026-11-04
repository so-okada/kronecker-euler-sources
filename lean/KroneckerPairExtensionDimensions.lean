import KroneckerPairExtensionSplit

/- Original module: KroneckerCentralStripEulerStrict -/
section
/-! The ordered central strip makes the rectangular Euler pairing strictly negative. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCentralStripEulerStrict
theorem negative (m r s : ℝ) (hm : 2<m) (hr : 1≤r) (hrs : r≤s)
 (hs : s≤m-1) : 1-s*(m-r)<0 := by
 have hmr : 1≤m-r := by linarith
 have hsr : 1≤s := le_trans hr hrs
 have hh := mul_le_mul_of_nonneg_left hmr (show 0≤s by linarith)
 by_cases he : s=1
 · subst s
   nlinarith
 · have : 1<s := lt_of_le_of_ne hsr (Ne.symm he)
   nlinarith
end KroneckerCentralStripEulerStrict
end
end

/- Original module: KroneckerCentralStripIntegerEuler -/
section
/-! Dimension inequalities in the central strip force positive extension parameter surplus. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCentralStripIntegerEuler
theorem surplus (m a b c d : ℕ) (hm : 3≤m) (ha : 0<a) (hc : 0<c)
 (hab : a≤b) (hcd : c≤d) (hbd : b*c≤d*a) (hupper : d≤(m-1)*c) :
 a*c+b*d<m*a*d := by
 have haR : (0:ℝ)<a := by exact_mod_cast ha
 have hcR : (0:ℝ)<c := by exact_mod_cast hc
 have hmR : (2:ℝ)<m := by exact_mod_cast hm
 have habR : (a:ℝ)≤b := by exact_mod_cast hab
 have hcdR : (c:ℝ)≤d := by exact_mod_cast hcd
 have hbdR : (b:ℝ)*c≤d*a := by exact_mod_cast hbd
 have huR : (d:ℝ)≤((m:ℝ)-1)*c := by
  have hh : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by
   rw [Nat.cast_sub (by omega : 1≤m),Nat.cast_one]
  have hu : (d:ℝ)≤((m-1:ℕ):ℝ)*c := by exact_mod_cast hupper
  rwa [hh] at hu
 have h := KroneckerCentralStripEulerStrict.negative (m:ℝ) ((b:ℝ)/a) ((d:ℝ)/c) hmR
  ((le_div_iff₀ haR).mpr (by simpa using habR))
  ((div_le_div_iff₀ haR hcR).mpr hbdR)
  ((div_le_iff₀ hcR).mpr huR)
 have hp := mul_lt_mul_of_pos_right h (mul_pos haR hcR)
 field_simp at hp
 have hh : (a:ℝ)*c+b*d<m*a*d := by nlinarith
 exact_mod_cast hh
end KroneckerCentralStripIntegerEuler
end
end

/- Original module: KroneckerPairExtensionDifferential -/
section
/-! Coboundary parameters form a linear image; splitting is exactly membership in that image. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairExtensionDifferential
open KroneckerAbstractPairHom KroneckerPairExtensionSplit
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
def differential (R : Rep m V W) (S : Rep m X Y) :
 ((V →ₗ[ℂ] X)×(W →ₗ[ℂ] Y)) →ₗ[ℂ] (Fin m → V →ₗ[ℂ] Y) where
 toFun f i := f.2.comp (R i)-(S i).comp f.1
 map_add' f g := by funext i;apply LinearMap.ext;intro v;simp;abel
 map_smul' c f := by funext i;apply LinearMap.ext;intro v;simp [smul_sub]
theorem split_iff (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y) :
 Split R S z ↔ z∈LinearMap.range (differential R S) := by
 constructor
 · rintro ⟨f,g,h⟩;refine ⟨(f,g),?_⟩;funext i;apply LinearMap.ext;intro v
   exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h i v)
 · rintro ⟨⟨f,g⟩,h⟩;refine ⟨f,g,?_⟩;intro i v
   have hi := LinearMap.congr_fun (congrFun h i) v
   change g (R i v)-S i (f v)=z i v at hi
   exact (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)
end KroneckerPairExtensionDifferential
end
end

/- Original module: KroneckerPairExtensionSurplus -/
section
/-! A strict arrow-parameter dimension surplus guarantees a nonsplit actual extension. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairExtensionSurplus
open Module KroneckerAbstractPairHom KroneckerPairExtensionSplit KroneckerPairExtensionDifferential
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
theorem exists_nonsplit (R : Rep m V W) (S : Rep m X Y)
 (h : finrank ℂ ((V →ₗ[ℂ] X)×(W →ₗ[ℂ] Y)) < finrank ℂ (Fin m → V →ₗ[ℂ] Y)) :
 ∃ z : Fin m → V →ₗ[ℂ] Y,¬Split R S z := by
 by_contra hn
 push Not at hn
 have hs : Function.Surjective (differential R S) := by intro z;exact (split_iff R S z).mp (hn z)
 have hh := (differential R S).finrank_range_add_finrank_ker
 rw [LinearMap.range_eq_top.mpr hs,finrank_top] at hh
 omega
end KroneckerPairExtensionSurplus
end
end

/- Original module: KroneckerPairExtensionDimensions -/
section
/-! The central-strip arithmetic surplus produces nonsplit extensions for actual finite coordinate representations. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairExtensionDimensions
open Module KroneckerReflectionPairModel KroneckerFiniteQuiverHom KroneckerPairExtensionSplit
open KroneckerPairExtensionSurplus
theorem dimensions (m a b c d : ℕ) :
 finrank ℂ ((Space a →ₗ[ℂ] Space c)×(Space b →ₗ[ℂ] Space d))=a*c+b*d ∧
 finrank ℂ (Fin m → Space a →ₗ[ℂ] Space d)=m*(a*d) := by
 constructor <;> simp [Space,Module.finrank_prod,Module.finrank_linearMap,Module.finrank_pi_fintype]
theorem exists_nonsplit {m a b c d : ℕ} (R : PairRep m a b) (S : PairRep m c d)
 (h : a*c+b*d<m*a*d) : ∃ z : Fin m → Space a →ₗ[ℂ] Space d,¬Split R S z := by
 apply KroneckerPairExtensionSurplus.exists_nonsplit R S
 rw [(dimensions m a b c d).1,(dimensions m a b c d).2]
 nlinarith
end KroneckerPairExtensionDimensions
end
end
