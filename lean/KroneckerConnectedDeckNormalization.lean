import KroneckerBoundedCoverDimensions
import KroneckerDeckDimensionClasses

/- Original module: KroneckerCoverSupportRadius -/
section
set_option autoImplicit false
namespace KroneckerCoverSupportRadius
open KroneckerReducedColorWords KroneckerColorWordCover KroneckerWordParity
open KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses
open KroneckerBoundedCoverDimensions

abbrev SupportVertex (d : Word →₀ ℕ) := {w : Word // w ∈ d.support}

def supportGraph (d : Word →₀ ℕ) : SimpleGraph (SupportVertex d) :=
  cover.induce (d.support : Set Word)

def supportInclusion (d : Word →₀ ℕ) : supportGraph d →g cover where
  toFun := Subtype.val
  map_rel' h := h

/-- A cover walk controls reduced-word length without assuming a geodesic. -/
theorem walk_word_length_bound {u v : Word} (p : cover.Walk u v) :
    v.val.length ≤ u.val.length + p.length := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have hex : ∃ c, toggle c u = v := h
    obtain ⟨c,hc⟩ := hex
    have hs := toggle_length c u
    rw [hc] at hs
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- A simple path inside positive support has fewer edges than total dimension. -/
theorem support_path_length_lt_total (d : Word →₀ ℕ)
    {u v : SupportVertex d} (p : (supportGraph d).Path u v) :
    p.val.length < d.sum (fun _ n => n) := by
  classical
  have hp := p.property.length_lt
  have hc : Fintype.card (SupportVertex d) = d.support.card := Fintype.card_coe _
  rw [hc] at hp
  exact lt_of_lt_of_le hp (support_card_le_total d)

/-- Deck translates of a connected finite support are bounded around the translated root. -/
theorem translated_support_radius (d : Word →₀ ℕ)
    (hconn : (supportGraph d).Preconnected) (r : SupportVertex d) (g : Deck)
    (w : SupportVertex d) :
    (g w.val).val.length < (g r.val).val.length + d.sum (fun _ n => n) := by
  classical
  apply (hconn r w).elim_path
  intro p
  let f : supportGraph d →g cover := (KroneckerDeckDimensionClasses.Deck.graphIso g).toHom.comp (supportInclusion d)
  have hb := walk_word_length_bound (p.val.map f)
  have hp := support_path_length_lt_total d p
  simp only [SimpleGraph.Walk.length_map] at hb
  change (g w.val).val.length ≤ (g r.val).val.length + p.val.length at hb
  omega

end KroneckerCoverSupportRadius
end

/- Original module: KroneckerConnectedDeckNormalization -/
section
set_option autoImplicit false
namespace KroneckerConnectedDeckNormalization
open KroneckerReducedColorWords KroneckerColorWordCover KroneckerWordParity
open KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses
open KroneckerCoverSupportRadius

/-- Push the actual dimension function along a color- and parity-preserving deck map. -/
def deckPush (g : Deck) (d : Word →₀ ℕ) : Word →₀ ℕ :=
  Finsupp.equivMapDomain g.equiv d

theorem deckPush_at (g : Deck) (d : Word →₀ ℕ) (w : Word) :
    deckPush g d (g w) = d w := by simp [deckPush]

theorem deckPush_total (g : Deck) (d : Word →₀ ℕ) :
    (deckPush g d).sum (fun _ n => n) = d.sum (fun _ n => n) := by
  simp [deckPush]

theorem deckPush_dimensionSetoid (g : Deck) (d : Word →₀ ℕ) :
    dimensionSetoid d (deckPush g d) := ⟨g, deckPush_at g d⟩

/-- Both parity classes have fixed short anchors; a sink is never sent to the empty word. -/
theorem exists_short_root_deck (r : Word) :
    ∃ g : Deck, (g r).val.length ≤ 1 := by
  by_cases h : parity r = 0
  · obtain ⟨g,hg⟩ := deck_transitive_same_parity (u := r) (v := root) h
    exact ⟨g, by rw [hg]; decide⟩
  · have hp : parity r = 1 := by
      have ht : parity r < 2 := Nat.mod_lt _ (by decide)
      omega
    have ho : parity (toggle 0 root) = 1 := by decide
    obtain ⟨g,hg⟩ := deck_transitive_same_parity (u := r) (v := toggle 0 root) (hp.trans ho.symm)
    exact ⟨g, by rw [hg]; decide⟩

/-- Every nonempty connected support has a deck representative in the actual word ball
of radius equal to its total dimension, with the same total dimension. -/
theorem normalize_connected_dimensions (d : Word →₀ ℕ)
    (hne : d.support.Nonempty) (hconn : (supportGraph d).Preconnected) :
    ∃ e : Word →₀ ℕ, dimensionSetoid d e ∧
      e.sum (fun _ n => n) = d.sum (fun _ n => n) ∧
      ∀ w ∈ e.support, w.val.length ≤ d.sum (fun _ n => n) := by
  classical
  obtain ⟨r,hr⟩ := hne
  obtain ⟨g,hg⟩ := exists_short_root_deck r
  refine ⟨deckPush g d, deckPush_dimensionSetoid g d, deckPush_total g d, ?_⟩
  intro w hw
  have hv : g.equiv.symm w ∈ d.support := by
    apply Finsupp.mem_support_iff.mpr
    have hh := Finsupp.mem_support_iff.mp hw
    simpa [deckPush] using hh
  have hb := translated_support_radius d hconn ⟨r,hr⟩ g ⟨g.equiv.symm w,hv⟩
  simp only [Equiv.apply_symm_apply] at hb
  omega


end KroneckerConnectedDeckNormalization
end
