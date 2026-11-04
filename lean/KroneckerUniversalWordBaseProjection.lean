import KroneckerProperBipartiteQuiver

/-! The parity-oriented universal colored-word quiver projects as an actual
quiver map to the original three-arrow Kronecker quiver. Its original-vertex
character agrees with the project's parity character, and its proper coloring
retains actual arrow colors and source/target multiplicities. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalWordBaseProjection
open KroneckerAbelianCover KroneckerReducedColorWords KroneckerWordParity
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerProperBipartiteQuiver
open KroneckerThreeArrowBaseQuiver KroneckerTypedQuiverMaps
attribute [local instance] Classical.decEq Classical.propDecidable

def baseVertex (w : Word) : Fin 2 := ⟨parity w,Nat.mod_lt _ (by omega)⟩

def baseMap : QuiverMap coloredCoverQuiver baseQuiver where
  vertex := baseVertex
  arrow := Prod.fst
  source a := by apply Fin.ext; exact a.2.property.symm
  target a := by
    apply Fin.ext
    change 1 = parity (toggle a.1 a.2.val)
    rw [toggle_parity,a.2.property]

def coloring : Coloring coloredCoverQuiver where
  side := parity
  side_lt _ := Nat.mod_lt _ (by omega)
  color := Prod.fst
  source_side a := a.2.property
  target_side a := by change parity (toggle a.1 a.2.val) = 1; rw [toggle_parity,a.2.property]
  source_injective a b hc hs := Prod.ext hc (Subtype.ext hs)
  target_injective a b hc ht := by
    apply Prod.ext hc
    apply Subtype.ext
    apply (show Function.Involutive (toggle a.1) from toggle_involution a.1).injective
    simpa only [coloredCoverQuiver,← hc] using ht

theorem character_eq (θ : Fin 2 → ℤ) :
    θ ∘ baseVertex = KroneckerQuiverPullbackStability.parityCharacter (θ 0) (θ 1) := by
  funext w
  unfold KroneckerQuiverPullbackStability.parityCharacter
  by_cases h : parity w = 0
  · rw [ite_eq_left h]
    exact congrArg θ (Fin.ext h)
  · rw [ite_eq_right h]
    apply congrArg θ
    apply Fin.ext
    have hp : parity w < 2 := Nat.mod_lt _ (by omega)
    change parity w = 1
    omega

end KroneckerUniversalWordBaseProjection
