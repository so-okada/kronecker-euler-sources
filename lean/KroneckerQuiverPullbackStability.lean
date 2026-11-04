import KroneckerFiniteSupportDeckRepresentationTransport
import KroneckerFiniteSupportStability

/- Original module: KroneckerQuiverPullbackSubrepresentations -/
section
/-! All vertexwise subrepresentations under an actual typed-quiver isomorphism.
No finiteness of the ambient vertices or arrows is assumed. -/
set_option autoImplicit false
namespace KroneckerQuiverPullbackSubrepresentations
open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportSubrepresentations

def transportArrow {V : Type} (d : V → ℕ) {u v u' v' : V}
    (hu : u = u') (hv : v = v') (L : Space (d u) →ₗ[ℂ] Space (d v)) :
    Space (d u') →ₗ[ℂ] Space (d v') := by
  rw [← hu, ← hv]
  exact L

theorem transport_invariant {V : Type} (d : V → ℕ)
    (U : ∀ v, Submodule ℂ (Space (d v))) {u v u' v' : V}
    (hu : u = u') (hv : v = v') (L : Space (d u) →ₗ[ℂ] Space (d v))
    (hi : ∀ x, x ∈ U u → L x ∈ U v) :
    ∀ x, x ∈ U u' → transportArrow d hu hv L x ∈ U v' := by
  cases hu
  cases hv
  exact hi

theorem transport_invariant_iff {V : Type} (d : V → ℕ)
    (U : ∀ v, Submodule ℂ (Space (d v))) {u v u' v' : V}
    (hu : u = u') (hv : v = v') (L : Space (d u) →ₗ[ℂ] Space (d v)) :
    (∀ x, x ∈ U u' → transportArrow d hu hv L x ∈ U v') ↔
      (∀ x, x ∈ U u → L x ∈ U v) := by
  cases hu
  cases hv
  rfl

noncomputable def pullSubrep {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S : Representation R.source R.target (fun v => d v))
    (U : Subrep S) : Subrep (pullRepresentation f d S) where
  space v := U.space (f.vertexEquiv v)
  invariant := by
    intro a x hx
    exact transport_invariant (fun v => d v) U.space
      (f.map_source a) (f.map_target a) (S.arrow (f.arrowEquiv a))
      (U.invariant (f.arrowEquiv a)) x hx

theorem pullSubrep_injective {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S : Representation R.source R.target (fun v => d v)) :
    Function.Injective (pullSubrep f d S) := by
  intro U W h
  apply subrep_ext
  funext w
  obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective w
  exact congrArg (fun T => T.space v) h

/-- A family of invariant subspaces descends along the inverse vertex
equivalence; arrow surjectivity checks every original arrow. -/
theorem pullSubrep_surjective {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S : Representation R.source R.target (fun v => d v)) :
    Function.Surjective (pullSubrep f d S) := by
  intro U
  let W := Equiv.piCongrLeft (fun w => Submodule ℂ (Space (d w)))
    f.vertexEquiv U.space
  have hw (v : Q.V) : W (f.vertexEquiv v) = U.space v := by
    exact Equiv.piCongrLeft_apply_apply _ _ _ v
  have invariant : ∀ a x, x ∈ W (R.source a) → S.arrow a x ∈ W (R.target a) := by
    intro a
    obtain ⟨b, rfl⟩ := f.arrowEquiv.surjective a
    apply (transport_invariant_iff (fun w => d w) W
      (f.map_source b) (f.map_target b) (S.arrow (f.arrowEquiv b))).mp
    intro x hx
    rw [hw] at hx ⊢
    exact U.invariant b x hx
  refine ⟨⟨W, invariant⟩, ?_⟩
  apply subrep_ext
  funext v
  exact hw v

/-- Pullback identifies ALL subrepresentations, with inverse obtained by
reindexing the dependent family of vertex submodules. -/
noncomputable def pullSubrepEquiv {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S : Representation R.source R.target (fun v => d v)) :
    Subrep S ≃ Subrep (pullRepresentation f d S) :=
  Equiv.ofBijective (pullSubrep f d S)
    ⟨pullSubrep_injective f d S, pullSubrep_surjective f d S⟩


end KroneckerQuiverPullbackSubrepresentations
end

/- Original module: KroneckerQuiverPullbackStability -/
section
/-! Support dimensions, characters and King stability under quiver pullback. -/
set_option autoImplicit false
namespace KroneckerQuiverPullbackStability
open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackSubrepresentations
open scoped BigOperators

noncomputable local instance supportFintype {V : Type} [DecidableEq V]
    (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

/-- The actual finite support is reindexed bijectively, including empty support. -/
def pullSupportEquiv {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) :
    SupportVertex (pullDimension f d) ≃ SupportVertex d where
  toFun v := ⟨f.vertexEquiv v.val, by
    simpa only [Finsupp.mem_support_iff, pullDimension_apply] using v.property⟩
  invFun w := ⟨f.vertexEquiv.symm w.val, by
    simpa only [Finsupp.mem_support_iff, pullDimension_apply,
      Equiv.apply_symm_apply] using w.property⟩
  left_inv v := by
    apply Subtype.ext
    exact f.vertexEquiv.symm_apply_apply v.val
  right_inv w := by
    apply Subtype.ext
    exact f.vertexEquiv.apply_symm_apply w.val

theorem pull_total_dimension {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) :
    supportTotalDimension (pullDimension f d) = supportTotalDimension d := by
  exact (pullSupportEquiv f d).sum_comp (fun w => d w.val)

theorem pull_balance {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) (θ : R.V → ℤ) :
    supportBalance (pullDimension f d) (fun v => θ (f.vertexEquiv v)) =
      supportBalance d θ := by
  exact (pullSupportEquiv f d).sum_comp (fun w => θ w.val * (d w.val : ℤ))

theorem pull_size {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ)
    (S : Representation R.source R.target (fun v => d v)) (U : Subrep S) :
    supportSize (pullDimension f d) (pullSubrep f d S U) = supportSize d U := by
  exact (pullSupportEquiv f d).sum_comp (fun w => Module.finrank ℂ (U.space w.val))

theorem pull_weight {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) (θ : R.V → ℤ)
    (S : Representation R.source R.target (fun v => d v)) (U : Subrep S) :
    supportWeight (pullDimension f d) (fun v => θ (f.vertexEquiv v))
      (pullSubrep f d S U) = supportWeight d θ U := by
  exact (pullSupportEquiv f d).sum_comp
    (fun w => θ w.val * (Module.finrank ℂ (U.space w.val) : ℤ))

/-- King stability is equivalent in both directions, using every
subrepresentation and the actual pullback arrow maps. -/
theorem pull_stable_iff {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) (θ : R.V → ℤ)
    (S : Representation R.source R.target (fun v => d v)) :
    FiniteSupportStable (pullDimension f d) (fun v => θ (f.vertexEquiv v))
      (pullRepresentation f d S) ↔ FiniteSupportStable d θ S := by
  constructor
  · intro h
    refine ⟨(pull_balance f d θ) ▸ h.1, ?_⟩
    intro U hn hp
    have hw := h.2 (pullSubrep f d S U)
      (by rw [pull_size]; exact hn)
      (by rw [pull_size, pull_total_dimension]; exact hp)
    rwa [pull_weight] at hw
  · intro h
    refine ⟨by rw [pull_balance]; exact h.1, ?_⟩
    intro U hn hp
    obtain ⟨W, rfl⟩ := pullSubrep_surjective f d S U
    rw [pull_size] at hn
    rw [pull_size, pull_total_dimension] at hp
    rw [pull_weight]
    exact h.2 W hn hp

open KroneckerReducedColorWords KroneckerCoverDeckTranslations

/-- A character descending from the two vertices of the Kronecker quiver. -/
def parityCharacter (a b : ℤ) (w : Word) : ℤ :=
  if KroneckerWordParity.parity w = 0 then a else b

theorem deck_preserves_character (g : Deck) (a b : ℤ) (w : Word) :
    parityCharacter a b (g w) = parityCharacter a b w := by
  simp only [parityCharacter, g.preserves_parity]

/-- Stability for the original two-vertex character is invariant under the
actual parity-oriented deck pullback. No abstract stability-preserving action
is assumed. -/
theorem deck_stable_iff (g : Deck) (d : Word →₀ ℕ) (a b : ℤ)
    (S : Representation coloredCoverQuiver.source coloredCoverQuiver.target
      (fun w => d w)) :
    FiniteSupportStable (deckPullDimension g d) (parityCharacter a b)
      (deckPullRepresentationEquiv g d S) ↔
      FiniteSupportStable d (parityCharacter a b) S := by
  classical
  have hθ : (fun w => parityCharacter a b ((deckQuiverAuto g).vertexEquiv w)) =
      parityCharacter a b := by
    funext w
    exact deck_preserves_character g a b w
  have h := pull_stable_iff (deckQuiverAuto g) d (parityCharacter a b) S
  rw [hθ] at h
  exact h

end KroneckerQuiverPullbackStability
end
