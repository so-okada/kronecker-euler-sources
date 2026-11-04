import KroneckerQuiverPullbackComposition
import KroneckerFiniteSupportIsomorphisms

/-! Actual isomorphisms transport bijectively under typed-quiver pullback. -/
set_option autoImplicit false
namespace KroneckerQuiverPullbackIsomorphisms
open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackSubrepresentations KroneckerFiniteSupportIsomorphisms

theorem transport_commutes_iff {V : Type} (d : V → ℕ)
    (E : ∀ v, Space (d v) → Space (d v)) {u v u' v' : V}
    (hu : u = u') (hv : v = v') (L M : Space (d u) →ₗ[ℂ] Space (d v)) :
    (∀ x, E v' (transportArrow d hu hv L x) = transportArrow d hu hv M (E u' x)) ↔
      (∀ x, E v (L x) = M (E u x)) := by
  cases hu
  cases hv
  rfl

noncomputable def pullIso {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S T : Representation R.source R.target (fun v => d v))
    (e : Iso S T) : Iso (pullRepresentation f d S) (pullRepresentation f d T) where
  map v := e.map (f.vertexEquiv v)
  commutes a := (transport_commutes_iff (fun v => d v) (fun v => e.map v)
    (f.map_source a) (f.map_target a) (S.arrow (f.arrowEquiv a)) (T.arrow (f.arrowEquiv a))).mpr
      (e.commutes (f.arrowEquiv a))

theorem pullIso_injective {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S T : Representation R.source R.target (fun v => d v)) :
    Function.Injective (pullIso f d S T) := by
  intro e k h
  apply iso_ext
  funext w
  obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective w
  exact congrArg (fun t => t.map v) h

theorem pullIso_surjective {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S T : Representation R.source R.target (fun v => d v)) :
    Function.Surjective (pullIso f d S T) := by
  intro e
  let W := Equiv.piCongrLeft (fun w => Space (d w) ≃ₗ[ℂ] Space (d w)) f.vertexEquiv e.map
  have hw (v : Q.V) : W (f.vertexEquiv v) = e.map v :=
    Equiv.piCongrLeft_apply_apply _ _ _ v
  have hc : ∀ a x, W (R.target a) (S.arrow a x) = T.arrow a (W (R.source a) x) := by
    intro a
    obtain ⟨b, rfl⟩ := f.arrowEquiv.surjective a
    apply (transport_commutes_iff (fun v => d v) (fun v => W v)
      (f.map_source b) (f.map_target b) (S.arrow (f.arrowEquiv b)) (T.arrow (f.arrowEquiv b))).mp
    intro x
    rw [hw, hw]
    exact e.commutes b x
  refine ⟨⟨W, hc⟩, ?_⟩
  apply iso_ext
  funext v
  exact hw v

noncomputable def pullIsoEquiv {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S T : Representation R.source R.target (fun v => d v)) :
    Iso S T ≃ Iso (pullRepresentation f d S) (pullRepresentation f d T) :=
  Equiv.ofBijective (pullIso f d S T) ⟨pullIso_injective f d S T, pullIso_surjective f d S T⟩


end KroneckerQuiverPullbackIsomorphisms
