import KroneckerCanonicalReflectionHomeomorphism
import KroneckerNegativeTitsSymmetry

section

/- Original module: KroneckerGeometricDimensionRelation -/
section
/-! A dimension relation records the actual moduli homeomorphism together
with exact Tits and gcd preservation, so geometric descent keeps all three. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerGeometricDimensionRelation
open KroneckerCanonicalKroneckerModuli KroneckerNegativeTitsSymmetry
structure Rel (m a b c d : ℕ) where
  homeomorph : space m a b ≃ₜ space m c d
  tits_eq : tits m c d=tits m a b
  gcd_eq : Nat.gcd c d=Nat.gcd a b
def refl (m a b : ℕ) : Rel m a b a b := ⟨Homeomorph.refl _,rfl,rfl⟩
def trans {m a b c d e f : ℕ} (x : Rel m a b c d) (y : Rel m c d e f) : Rel m a b e f :=
  ⟨x.homeomorph.trans y.homeomorph,y.tits_eq.trans x.tits_eq,y.gcd_eq.trans x.gcd_eq⟩
def exchange (m a b : ℕ) : Rel m a b b a :=
  ⟨KroneckerExchangeOrbitHomeomorphism.homeomorph m a b,
    KroneckerNegativeTitsSymmetry.exchange m a b,Nat.gcd_comm b a⟩
def reflection (m a b : ℕ) (h : tits m a b<0) : Rel m a b (m*a-b) a := by
  have hb := KroneckerReflectionInteriorDimensions.positive m a b (positive m a b h).1 h
  exact ⟨KroneckerCanonicalReflectionHomeomorphism.homeomorph m a b (positive m a b h).1 hb.le,
    (KroneckerNegativeTitsSymmetry.reflection m a b h).2,KroneckerReflectionPrimitive.gcd m a b hb.le⟩
end KroneckerGeometricDimensionRelation
end
end

/- Original module: KroneckerNegativeTitsDescentSize -/
section
/-! Above the fundamental upper edge 2b=m*a, sink reflection strictly
reduces the total dimension while preserving positivity and negative Tits form. -/
set_option autoImplicit false
namespace KroneckerNegativeTitsDescentSize
open KroneckerNegativeTitsSymmetry
theorem decrease (m a b : ℕ) (h : tits m a b<0) (hedge : m*a<2*b) :
    (m*a-b)+a<a+b := by
  have hb := KroneckerReflectionInteriorDimensions.positive m a b (positive m a b h).1 h
  omega
theorem step_negative (m a b : ℕ) (h : tits m a b<0) : tits m (m*a-b) a<0 := by
  rw [(reflection m a b h).2]
  exact h
end KroneckerNegativeTitsDescentSize
end

/- Original module: KroneckerSortedGeometricDescent -/
section
/-! One descent step sorts the reflected dimensions, strictly reduces their
total size, and supplies the actual moduli homeomorphism with arithmetic invariants. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSortedGeometricDescent
open KroneckerNegativeTitsSymmetry KroneckerGeometricDimensionRelation
theorem step (m a b : ℕ) (h : tits m a b<0) (hedge : m*a<2*b) :
    ∃ c d : ℕ,0<c ∧ c≤d ∧ c+d<a+b ∧ tits m c d<0 ∧ Nonempty (Rel m a b c d) := by
  have hc := (KroneckerNegativeTitsSymmetry.reflection m a b h).1
  have ha := (positive m a b h).1
  have hn := KroneckerNegativeTitsDescentSize.step_negative m a b h
  have hs := KroneckerNegativeTitsDescentSize.decrease m a b h hedge
  by_cases hh : m*a-b≤a
  · exact ⟨m*a-b,a,hc,hh,hs,hn,⟨KroneckerGeometricDimensionRelation.reflection m a b h⟩⟩
  · refine ⟨a,m*a-b,ha,by omega,by omega,?_,?_⟩
    · rw [KroneckerNegativeTitsSymmetry.exchange];exact hn
    · exact ⟨trans (KroneckerGeometricDimensionRelation.reflection m a b h)
        (KroneckerGeometricDimensionRelation.exchange m (m*a-b) a)⟩
end KroneckerSortedGeometricDescent
end
end

/- Original module: KroneckerFundamentalSortedReduction -/
section
/-! Strong induction on total dimension reduces every sorted negative-Tits
pair to 0<c≤d and 2d≤m*c, preserving the actual moduli homeomorphism, Tits and gcd. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFundamentalSortedReduction
open KroneckerNegativeTitsSymmetry KroneckerGeometricDimensionRelation
theorem exists_reduction (m a b : ℕ) (h : tits m a b<0) (hab : a≤b) :
    ∃ c d : ℕ,0<c ∧ c≤d ∧ 2*d≤m*c ∧ Nonempty (Rel m a b c d) := by
  have aux : ∀ n a b : ℕ,a+b=n → tits m a b<0 → a≤b →
      ∃ c d : ℕ,0<c ∧ c≤d ∧ 2*d≤m*c ∧ Nonempty (Rel m a b c d) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b hn ht hab
      by_cases hf : 2*b≤m*a
      · exact ⟨a,b,(positive m a b ht).1,hab,hf,⟨refl m a b⟩⟩
      · obtain ⟨c,d,hc,hcd,hs,ht',⟨e⟩⟩ := KroneckerSortedGeometricDescent.step m a b ht (by omega)
        obtain ⟨u,v,hu,huv,hv,⟨f⟩⟩ := ih (c+d) (by omega) c d rfl ht' hcd
        exact ⟨u,v,hu,huv,hv,⟨trans e f⟩⟩
  exact aux (a+b) a b rfl h hab
end KroneckerFundamentalSortedReduction
end
end

/- Original module: KroneckerFundamentalGeometricReduction -/
section
/-! Every negative-Tits dimension vector is geometrically equivalent to a
fundamental-region vector, without assuming nonemptiness or finite homology. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFundamentalGeometricReduction
open KroneckerNegativeTitsSymmetry KroneckerGeometricDimensionRelation
theorem exists_reduction (m a b : ℕ) (h : tits m a b<0) :
    ∃ c d : ℕ,0<c ∧ c≤d ∧ 2*d≤m*c ∧ Nonempty (Rel m a b c d) := by
  by_cases hab : a≤b
  · exact KroneckerFundamentalSortedReduction.exists_reduction m a b h hab
  · have ht : tits m b a<0 := by rw [KroneckerNegativeTitsSymmetry.exchange];exact h
    obtain ⟨c,d,hc,hcd,hd,⟨e⟩⟩ := KroneckerFundamentalSortedReduction.exists_reduction m b a ht (by omega)
    exact ⟨c,d,hc,hcd,hd,⟨trans (KroneckerGeometricDimensionRelation.exchange m a b) e⟩⟩
end KroneckerFundamentalGeometricReduction
end
end
end

section

/-! Every negative-Tits canonical Euler characteristic equals that of a
fundamental-region dimension pair, with exact Tits and primitive data retained. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFundamentalEulerReduction
open KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
variable (H : ∀ m a b,Admissible (space m a b))
theorem reduction (m a b : ℕ) (ht : tits m a b<0) :
    ∃ c d : ℕ,0<c ∧ c≤d ∧ 2*d≤m*c ∧ tits m c d=tits m a b ∧ Nat.gcd c d=Nat.gcd a b ∧
      ordinaryEuler (space m a b) (H m a b)=ordinaryEuler (space m c d) (H m c d) := by
  obtain ⟨c,d,hc,hcd,hd,⟨e⟩⟩ := KroneckerFundamentalGeometricReduction.exists_reduction m a b ht
  exact ⟨c,d,hc,hcd,hd,e.tits_eq,e.gcd_eq,KroneckerHomologyHomeomorphism.euler_eq e.homeomorph _ _⟩
end KroneckerFundamentalEulerReduction
end
end

section

/-! Interior nonemptiness for primitive dimensions reduces to the fundamental
region through proved geometric homeomorphisms and gcd preservation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFundamentalNonemptyReduction
open KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli
theorem transfer (m : ℕ)
    (h : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 → Nonempty (space m c d))
    (a b : ℕ) (hp : Nat.Coprime a b) (ht : tits m a b<0) : Nonempty (space m a b) := by
  obtain ⟨c,d,hc,hcd,hd,⟨e⟩⟩ := KroneckerFundamentalGeometricReduction.exists_reduction m a b ht
  have hcp : Nat.Coprime c d := by change Nat.gcd c d=1;rw [e.gcd_eq];exact hp
  exact e.homeomorph.toEquiv.nonempty_congr.mpr (h c d hc hcd hd hcp (by rw [e.tits_eq];exact ht))
end KroneckerFundamentalNonemptyReduction
end
end

