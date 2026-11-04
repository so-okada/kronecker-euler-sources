import KroneckerEmbeddedSupportQuiverIso
import KroneckerIteratedFiniteSupportArrows

/-! The actual finite-quiver Euler pairing and self-Euler form are preserved by
weighted isomorphisms of induced support quivers. Every actual parallel arrow
contributes to the arrow sum; no unlabeled graph replacement is made. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFiniteSupportEulerTransport
open KroneckerAbelianCover KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

def finiteEuler (Q : TypedQuiver) [Fintype Q.V] [Fintype Q.A] (d e : Q.V → ℕ) : ℤ :=
  (∑ v, (d v : ℤ) * e v) - ∑ a, (d (Q.source a) : ℤ) * e (Q.target a)

theorem finiteEuler_transport {Q R : TypedQuiver} [Fintype Q.V] [Fintype Q.A]
    [Fintype R.V] [Fintype R.A] (f : TypedQuiverIso Q R) (d e : R.V → ℕ) :
    finiteEuler Q (d ∘ f.vertexEquiv) (e ∘ f.vertexEquiv) = finiteEuler R d e := by
  unfold finiteEuler
  congr 1
  · exact f.vertexEquiv.sum_comp (fun v => (d v : ℤ) * e v)
  · have h := f.arrowEquiv.sum_comp (fun a => (d (R.source a) : ℤ) * e (R.target a))
    simpa only [f.map_source,f.map_target,Function.comp_apply] using h

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)
local instance supportQuiverVertexFintype (Q : TypedQuiver) (d : Q.V →₀ ℕ) :
    Fintype (supportQuiver Q d).V := supportFintype d
local instance supportQuiverArrowFintype (Q : TypedQuiver) (d : Q.V →₀ ℕ)
    [Finite (SupportArrow Q.source Q.target d)] : Fintype (supportQuiver Q d).A := Fintype.ofFinite (SupportArrow Q.source Q.target d)

def supportEuler (Q : TypedQuiver) (d : Q.V →₀ ℕ) [Finite (SupportArrow Q.source Q.target d)] : ℤ :=
  finiteEuler (supportQuiver Q d) (supportDimension d) (supportDimension d)

theorem supportEuler_iso {Q R : TypedQuiver} (d : Q.V →₀ ℕ) (e : R.V →₀ ℕ)
    [Finite (SupportArrow Q.source Q.target d)] [Finite (SupportArrow R.source R.target e)]
    (f : TypedQuiverIso (supportQuiver Q d) (supportQuiver R e))
    (h : ∀ v, supportDimension e (f.vertexEquiv v) = supportDimension d v) :
    supportEuler Q d = supportEuler R e := by
  have he : supportDimension e ∘ f.vertexEquiv = supportDimension d := funext h
  have hh := finiteEuler_transport f (supportDimension e) (supportDimension e)
  rw [he] at hh
  exact hh

end KroneckerFiniteSupportEulerTransport
