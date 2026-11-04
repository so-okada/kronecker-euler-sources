import KroneckerCoverDeckTranslations
import Mathlib.Data.Finsupp.Basic

set_option autoImplicit false
namespace KroneckerDeckDimensionClasses
open KroneckerReducedColorWords KroneckerCoverDeckTranslations KroneckerColorWordCover

def Deck.refl : Deck where
  equiv := Equiv.refl _
  commutes _ _ := rfl
  preserves_parity _ := rfl

def Deck.symm (d : Deck) : Deck where
  equiv := d.equiv.symm
  commutes c w := by
    apply d.equiv.injective
    change d.equiv (d.equiv.symm (toggle c w)) = d.equiv (toggle c (d.equiv.symm w))
    rw [d.equiv.apply_symm_apply, d.commutes, d.equiv.apply_symm_apply]
  preserves_parity w := by
    have h := d.preserves_parity (d.equiv.symm w)
    rw [d.equiv.apply_symm_apply] at h
    exact h.symm

def Deck.trans (d e : Deck) : Deck where
  equiv := d.equiv.trans e.equiv
  commutes c w := by
    change e (d (toggle c w)) = toggle c (e (d w))
    rw [d.commutes, e.commutes]
  preserves_parity w := (e.preserves_parity (d w)).trans (d.preserves_parity w)

def Deck.graphIso (d : Deck) : cover ≃g cover where
  toEquiv := d.equiv
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨c,h⟩
      exact ⟨c,d.equiv.injective ((d.commutes c u).trans h)⟩
    · rintro ⟨c,h⟩
      exact ⟨c,(d.commutes c u).symm.trans (congrArg d h)⟩

def dimensionSetoid : Setoid (Word →₀ ℕ) where
  r D E := ∃ d : Deck, ∀ w, E (d w) = D w
  iseqv := by
    constructor
    · intro D
      exact ⟨Deck.refl,fun _ => rfl⟩
    · rintro D E ⟨d,h⟩
      refine ⟨Deck.symm d,fun w => ?_⟩
      have hh := h (d.equiv.symm w)
      rw [d.equiv.apply_symm_apply] at hh
      exact hh.symm
    · rintro D E F ⟨d,h⟩ ⟨e,k⟩
      exact ⟨Deck.trans d e,fun w => (k (d w)).trans (h w)⟩

abbrev DimensionClass := Quotient dimensionSetoid


end KroneckerDeckDimensionClasses
