import KroneckerPaperConnected

/-!
# Literal node inequalities and cyclic compatibility

These theorems compose the proved predecessor, node, trace, and witness
dictionaries. A RootComponent places the cut immediately before a complete
horizontal-shadow component. Extension statements require grade zero on every
added edge. They assert compatibility of the enlarged cyclic word, not
connectedness of that enlarged word.
-/
set_option autoImplicit false
namespace KroneckerPaperCompatibility
noncomputable section
open KroneckerStack KroneckerCompatibility KroneckerShadow
open KroneckerPredecessor KroneckerPaperTraceBridge KroneckerPaperConnected

/-- On a complete component, literal connectedness is precisely cyclic
compatibility. Neither side assumes a grade bound or a color condition. -/
theorem connected_iff_cyclic {E : ℕ → Edge} {n : ℕ}
    (hr : RootComponent E n) :
    KroneckerPaperConnected.Connected E n ↔ CyclicCompatible E n := by
  constructor
  · intro hc
    have hn := connected_nodeRun hc
    rw [wordList, KroneckerPaperExecutionTrace.orderedList_eq_segment] at hn
    exact KroneckerComponent.node_compatible hr hn
  · intro hc
    obtain ⟨c, hn⟩ := KroneckerComponent.compatible_node hr hc
    apply nodeRun_connected (c := c)
    simpa [wordList, KroneckerPaperExecutionTrace.orderedList_eq_segment] using hn

/-- For a specified predecessor map on a complete component, the literal
owned-edge inequalities are equivalent to cyclic compatibility. -/
theorem ownedBalance_iff_cyclic {E : ℕ → Edge} {n : ℕ} {p : Fin n → Fin n}
    (hp : ValidThrough (sample E n) p n) (hr : RootComponent E n) :
    OwnedBalance (sample E n) p ↔ CyclicCompatible E n := by
  constructor
  · intro hb
    apply (connected_iff_cyclic hr).mp
    exact ⟨p, hp, hb, root_component_full_node hr hp⟩
  · intro hc
    obtain ⟨f, ht, hf⟩ := valid_has_trace hp
    have hg := (compatibility_iff_guarded hr ht).mp hc
    exact guarded_ownedBalance hr ht hg hf

/-- The same equivalence with the component hypothesis expressed by the
literal full-root node. -/
theorem ownedBalance_iff_cyclic_of_fullRoot {E : ℕ → Edge} {n : ℕ}
    {p : Fin n → Fin n} (hp : ValidThrough (sample E n) p n)
    (hr : FullRoot (sample E n) p) :
    OwnedBalance (sample E n) p ↔ CyclicCompatible E n :=
  ownedBalance_iff_cyclic hp (fullRoot_rootComponent hp hr)

theorem ownedBalance_iff_shadowBaselines {E : ℕ → Edge} {n : ℕ}
    {p : Fin n → Fin n} (hp : ValidThrough (sample E n) p n)
    (hr : RootComponent E n) :
    OwnedBalance (sample E n) p ↔ ShadowBaselines E n :=
  (ownedBalance_iff_cyclic hp hr).trans (cyclic_iff_shadow_baselines hr)

/-- Restricting a compatible ambient cyclic word to a complete component
gives a literal connected grading. Grades outside the component are arbitrary. -/
theorem compatible_restriction {E : ℕ → Edge} {n N : ℕ}
    (hr : RootComponent E n) (hn : n ≤ N) (hc : CyclicCompatible E N) :
    KroneckerPaperConnected.Connected E n := by
  apply (connected_iff_cyclic hr).mpr
  apply (cyclic_iff_linear hr).mpr
  intro u v huv hvn hu hv
  simpa [ite_eq_left (show u ≤ v by omega)] using
    hc u v (by omega) (by omega) hu hv

/-- Adding any word of grade-zero edges outside the component preserves
compatibility, with the precise literal connected predicate on the component. -/
theorem zero_extension_iff_connected {E : ℕ → Edge} {n N : ℕ}
    (hr : RootComponent E n) (hn : n ≤ N)
    (hz : ∀ j, n ≤ j → j < N → (E j).grade = 0) :
    CyclicCompatible E N ↔ KroneckerPaperConnected.Connected E n :=
  (KroneckerComponent.zero_extension_compatible hr hn hz).trans
    (connected_iff_cyclic hr).symm

theorem zero_extension_iff_ownedBalance {E : ℕ → Edge} {n N : ℕ}
    {p : Fin n → Fin n} (hp : ValidThrough (sample E n) p n)
    (hr : RootComponent E n) (hn : n ≤ N)
    (hz : ∀ j, n ≤ j → j < N → (E j).grade = 0) :
    CyclicCompatible E N ↔ OwnedBalance (sample E n) p :=
  (KroneckerComponent.zero_extension_compatible hr hn hz).trans
    (ownedBalance_iff_cyclic hp hr).symm

/-- Literal connectedness itself supplies the complete-component hypothesis
needed for extension by grade-zero edges. -/
theorem connected_zero_extension {E : ℕ → Edge} {n N : ℕ}
    (hc : KroneckerPaperConnected.Connected E n) (hn : n ≤ N)
    (hz : ∀ j, n ≤ j → j < N → (E j).grade = 0) : CyclicCompatible E N := by
  have hroot : RootComponent E n := by
    obtain ⟨p, hp, _, hr⟩ := hc
    exact fullRoot_rootComponent hp hr
  exact (zero_extension_iff_connected hroot hn hz).mpr hc

#print axioms connected_iff_cyclic
#print axioms ownedBalance_iff_cyclic
#print axioms compatible_restriction
#print axioms zero_extension_iff_connected
end
end KroneckerPaperCompatibility
