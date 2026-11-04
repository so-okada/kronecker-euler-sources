import KroneckerManuscriptBipartiteStability
import KroneckerStableCoverIndexFinite
import KroneckerManuscriptFixedLocalization

/-! Cover weights, connected support and the localization bound, in that order. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerSplitCoverLemmas
open KroneckerManuscriptBipartiteStability

theorem cover_weights (a k u v : ℕ) :
    positiveWeight a (a+k) a (a+k)=0 ∧
    positiveWeight a (a+k) u v=(a : ℤ)*v-(a+k : ℕ)*u ∧
    (0 < positiveWeight a (a+k) u v ↔ (a+k)*u < a*v) := by
  refine ⟨?_,rfl,positiveWeight_pos_iff a (a+k) u v⟩
  unfold positiveWeight
  ring

open KroneckerReducedColorWords KroneckerCoverSupportRadius
open KroneckerStableCoverIndexFinite KroneckerFiniteQuiverHom

theorem connected_support (d : Word →₀ ℕ) (R : CoverRepresentation d)
    (θ : SupportVertex d → ℤ) (hR : Stable θ R) :
    (supportGraph d).Preconnected :=
  stable_cover_support_preconnected d R θ hR

open KroneckerManuscriptFixedCoverCount KroneckerOrdinarySingularEuler
open KroneckerScopedModuli KroneckerScopedWeistApplication

theorem localization_bound {n a : ℕ} {x : ℝ} (hx : 100000 ≤ x)
    (ha : ((n : ℝ)+2)*x=a) (hc : a.Coprime (n+2)) :
    ((coverClasses hx ha).card : ℤ) ≤
      ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+n+2))
        (baseAdmissible KroneckerReadableMain.geometry a (a+n+2)) :=
  fixed_cover_localization_manuscript hx ha hc

end KroneckerSplitCoverLemmas

#print axioms KroneckerSplitCoverLemmas.cover_weights
#print axioms KroneckerSplitCoverLemmas.connected_support
#print axioms KroneckerSplitCoverLemmas.localization_bound
