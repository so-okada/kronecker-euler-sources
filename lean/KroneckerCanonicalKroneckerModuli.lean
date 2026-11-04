import KroneckerCanonicalStableOrbit
import KroneckerManuscriptTarget

/-! A fixed all-m family of actual stable complex matrix-orbit spaces.
The analytic King comparison and finite homology are not proved here.
This replaces an unspecified topological family by one concrete construction. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalKroneckerModuli
open KroneckerFiniteQuiverHom KroneckerOrdinarySingularEuler

/-- The manuscript dimension vector `(a,b)`: `a` is the dimension at the source
(vertex `0`) and `b` at the target (vertex `1`). -/
def dimension (a b : ℕ) (i : Fin 2) : ℕ := if i=0 then a else b

/-- Internal weight `(b,-a)`. For a nonzero proper subrepresentation of source
and target dimensions `(u,v)`, stability requires `b*u-a*v < 0`, equivalently the
manuscript condition `a*v-b*u > 0` in equation (1.1). -/
def character (a b : ℕ) (i : Fin 2) : ℤ := if i=0 then b else -(a : ℤ)

def source (m : ℕ) : Fin m → Fin 2 := fun _ => 0

def target (m : ℕ) : Fin m → Fin 2 := fun _ => 1

def space (m a b : ℕ) : TopCat.{0} :=
  KroneckerCanonicalStableOrbit.space (source m) (target m) (dimension a b) (character a b)

theorem space_nonempty_iff (m a b : ℕ) : Nonempty (space m a b) ↔
    ∃ R : Representation (source m) (target m) (dimension a b), Stable (character a b) R :=
  KroneckerCanonicalStableOrbit.space_nonempty_iff _ _ _ _

/-- Finite homology remains a named external geometric input. -/
def family (H : ∀ m a b, Admissible (space m a b)) : KroneckerManuscriptTarget.ModuliFamily :=
  ⟨space,H⟩

theorem allowed_iff (H : ∀ m a b, Admissible (space m a b)) (m a b : ℕ) :
    KroneckerManuscriptTarget.Allowed (family H) m a b ↔
    0<a ∧ 0<b ∧ a.Coprime b ∧
      ∃ R : Representation (source m) (target m) (dimension a b), Stable (character a b) R := by
  simp only [KroneckerManuscriptTarget.Allowed, family, space_nonempty_iff]

end KroneckerCanonicalKroneckerModuli
