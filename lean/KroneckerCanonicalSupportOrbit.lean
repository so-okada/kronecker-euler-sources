import KroneckerCanonicalStableOrbit
import KroneckerFiniteSupportStability

/-! Canonical topological moduli for any finite-support representation dimension,
using the full induced support quiver rather than ambient infinite products. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalSupportOrbit
open KroneckerAbelianCover KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportStability KroneckerFiniteQuiverHom
attribute [local instance] Classical.decEq Classical.propDecidable
variable (Q : TypedQuiver) (d : Q.V →₀ ℕ) [Fintype (supportQuiver Q d).A]
  (θ : Q.V → ℤ)
local instance vertices : Fintype (supportQuiver Q d).V :=
  inferInstanceAs (Fintype (SupportVertex d))

def space : TopCat.{0} :=
  KroneckerCanonicalStableOrbit.space (supportQuiver Q d).source (supportQuiver Q d).target
    (supportDimension d) (supportCharacter d θ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem nonempty_iff : Nonempty (space Q d θ) ↔
    ∃ R : Representation Q.source Q.target d, FiniteSupportStable d θ R := by
  rw [space,KroneckerCanonicalStableOrbit.space_nonempty_iff]
  constructor
  · rintro ⟨R,hR⟩
    refine ⟨extendByZero Q d R,?_⟩
    apply (finiteSupportStable_iff_restrict Q d θ _).mpr
    simpa only [restrict_extend] using hR
  · rintro ⟨R,hR⟩
    exact ⟨restrictToSupport Q d R,(finiteSupportStable_iff_restrict Q d θ R).mp hR⟩

end KroneckerCanonicalSupportOrbit
