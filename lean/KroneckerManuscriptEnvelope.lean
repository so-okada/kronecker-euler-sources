import KroneckerExplicitFiniteBound
import KroneckerManuscriptCorollaries

set_option autoImplicit false
namespace KroneckerManuscriptCorollaries
open KroneckerManuscriptTarget KroneckerReadableMain KroneckerScopedCanonicalPublishedEuler

/-- Corollary 10.5, together with the nonnegativity of the profile.
This profile is the witness constructed in `KroneckerReadableMain.main`. -/
theorem profile_envelope (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interval m) :
    0 ≤ profile m hm r ∧ profile m hm r ≤
      (m : ℝ) * Real.log 2 * Real.sqrt (((m : ℝ) + 2) / ((m : ℝ) - 2)) *
        Real.sqrt ((KroneckerEndpointRoots.upperRoot m - r) *
          (r - KroneckerEndpointRoots.lowerRoot m)) := by
  exact KroneckerLimitEnvelopeWithError.limit_bounds (family geometry) m
    (KroneckerExplicitFiniteBound.error m) (KroneckerExplicitFiniteBound.finite_envelope m hm)
    r (profile m hm r) (slope_approximable m hm r hr) (profile_joint m hm r hr)

end KroneckerManuscriptCorollaries
