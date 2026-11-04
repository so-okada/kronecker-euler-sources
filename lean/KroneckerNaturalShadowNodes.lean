import KroneckerNaturalShadows

/-! Shadow nodes, compatibility and extension: manuscript labels
`lem:shadow-nodes`, `lem:compatibility` and `lem:shadow-extension`.
The ambient grading has values in ℕ. No color bound is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths KroneckerPredecessor KroneckerPaperTraceBridge

private theorem ambient_first {P : TNEPath} {g : Grading P} {u v : Edge P}
    (hg : 0 < g (edgeEquiv P u)) (hs : FirstHShadow g u v) :
    KroneckerPaperPathGradings.AmbientFirstShadow (bounded g) u v :=
  (KroneckerPaperPathGradings.ambientFirstShadow_iff (bounded g) u v).mpr
    ((firstH_ofBounded_iff (bounded g) u v hg).mp hs)

theorem NEReal_shadow_nodes {P : TNEPath} (g : Grading P) (u v : Edge P)
    (hg : 0 < g (edgeEquiv P u)) (hs : FirstHShadow g u v) :
    let h := NERealGrading g u v
    let U := sample (geometricTrace h) (cyclicLength u v)
    ∃ p : Fin (cyclicLength u v) → Fin (cyclicLength u v),
      ValidThrough U p (cyclicLength u v) ∧ KroneckerPaperConnected.FullRoot U p ∧
      ∀ x, KroneckerPredecessor.IsHorizontal U x → 0 < (U x).grade →
        ∃ z, KroneckerPredecessor.IsNode U p x z ∧
          intervalVerticalCount U x.val (z.val+1) = intervalHorizontalGrade U x.val (z.val+1) ∧
          ∀ k, x.val < k → k ≤ z.val →
            intervalVerticalCount U x.val k < intervalHorizontalGrade U x.val k :=
  KroneckerPaperPathGradings.firstShadow_all_nodes (bounded g) u v
    ((firstH_ofBounded_iff (bounded g) u v hg).mp hs)

theorem NEReal_shadow_compatible_of_balance {P : TNEPath} (g : Grading P) (u v : Edge P)
    (hg : 0 < g (edgeEquiv P u)) (hs : FirstHShadow g u v)
    (p : Fin (cyclicLength u v) → Fin (cyclicLength u v))
    (hp : ValidThrough
      (sample (geometricTrace (NERealGrading g u v)) (cyclicLength u v)) p (cyclicLength u v))
    (hb : OwnedBalance
      (sample (geometricTrace (NERealGrading g u v)) (cyclicLength u v)) p) :
    Compatible (NERealGrading g u v) :=
  (KroneckerPaperPathGradings.NEReal_shadow_balance_iff
    (bounded g) u v (ambient_first hg hs) p hp).mpr hb

theorem NEReal_shadow_balance_of_compatible {P : TNEPath} (g : Grading P) (u v : Edge P)
    (hg : 0 < g (edgeEquiv P u)) (hs : FirstHShadow g u v)
    (p : Fin (cyclicLength u v) → Fin (cyclicLength u v))
    (hp : ValidThrough
      (sample (geometricTrace (NERealGrading g u v)) (cyclicLength u v)) p (cyclicLength u v))
    (hc : Compatible (NERealGrading g u v)) :
    OwnedBalance (sample (geometricTrace (NERealGrading g u v)) (cyclicLength u v)) p :=
  (KroneckerPaperPathGradings.NEReal_shadow_balance_iff
    (bounded g) u v (ambient_first hg hs) p hp).mp hc

theorem NEReal_shadow_balance_iff {P : TNEPath} (g : Grading P) (u v : Edge P)
    (hg : 0 < g (edgeEquiv P u)) (hs : FirstHShadow g u v)
    (p : Fin (cyclicLength u v) → Fin (cyclicLength u v))
    (hp : ValidThrough
      (sample (geometricTrace (NERealGrading g u v)) (cyclicLength u v)) p (cyclicLength u v)) :
    Compatible (NERealGrading g u v) ↔ OwnedBalance
      (sample (geometricTrace (NERealGrading g u v)) (cyclicLength u v)) p :=
  ⟨NEReal_shadow_balance_of_compatible g u v hg hs p hp,
    NEReal_shadow_compatible_of_balance g u v hg hs p hp⟩

theorem NEReal_shadow_zero_extension {P : TNEPath} (g : Grading P) (u v : Edge P)
    (hg : 0 < g (edgeEquiv P u)) (hs : FirstHShadow g u v)
    (hz : ∀ k, cyclicLength u v ≤ k → k < P.steps.length →
      (geometricTrace g (u.val+k)).grade = 0) :
    Compatible g ↔ ConnectedGrading (NERealGrading g u v) :=
  KroneckerPaperPathGradings.NEReal_shadow_zero_extension (bounded g) u v (ambient_first hg hs) hz

theorem NEReal_shadow_connected {P : TNEPath} (g : Grading P) (u v : Edge P)
    (hg : 0 < g (edgeEquiv P u)) (hs : FirstHShadow g u v) (hc : Compatible g) :
    let h := NERealGrading g u v
    ConnectedGrading h :=
  KroneckerPaperPathGradings.NEReal_shadow_connected (bounded g) u v (ambient_first hg hs) hc

theorem NEReal_shadow_surp_nonnegative {P : TNEPath} (g : Grading P) (u v : Edge P)
    (hg : 0 < g (edgeEquiv P u)) (hs : FirstHShadow g u v) (hc : Compatible g) :
    let h := NERealGrading g u v
    0 ≤ Surp (NEReal P u v) h :=
  connected_surp_nonnegative (NEReal_shadow_connected g u v hg hs hc)

theorem NEReal_surp_formula {P : TNEPath} (g : Grading P) (u v : Edge P) :
    let h := NERealGrading g u v
    Surp (NEReal P u v) h =
      ((cyclicE P u v).card : ℤ)-1-∑ w ∈ cyclicN P u v, (g w : ℤ) :=
  KroneckerPaperPathGradings.NEReal_surp_formula (bounded g) u v

theorem maximalHShadow_connected {P : TNEPath} (g : Grading P) (C : CyclicSubpath P)
    (hs : MaximalHShadowSubpath g C) (hc : Compatible g) :
    ConnectedGrading (NERealGrading g C.first C.last) :=
  NEReal_shadow_connected g C.first C.last hs.1 hs.2.1 hc

end KroneckerNaturalPathGradings
