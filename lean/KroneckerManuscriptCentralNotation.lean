import KroneckerManuscriptFiniteStatements

/-! The Euler-characteristic notation in Definition 7.1. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerManuscriptCentralNotation
open KroneckerManuscriptTarget

def E (M : ModuliFamily) (r a : ℕ) : ℤ := euler M 3 a (a+r)

theorem E_eq (M : ModuliFamily) (r a : ℕ) :
    E M r a = euler M 3 a (a+r) := rfl

theorem E_real (G : KroneckerScopedModuli.Geometry) (r a : ℕ) :
    (E (KroneckerScopedCanonicalPublishedEuler.family G) r a : ℝ) =
      KroneckerScopedWeistCentralLowerLimit.E G a r := rfl

end KroneckerManuscriptCentralNotation

