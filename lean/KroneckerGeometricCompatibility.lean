import KroneckerGeometricCyclicBridge
import KroneckerCyclicWitnessTransport

set_option autoImplicit false

namespace KroneckerPaperPathGradings
noncomputable section
open KroneckerPaperPaths KroneckerCompatibility

def Compatible {m : ℕ} {P : TNEPath} (g : Grading m P) : Prop :=
  ∀ u v : KroneckerPaperPaths.Edge P,
    PositiveH (geometricTrace g) u.val → PositiveV (geometricTrace g) v.val →
      HWitness (geometricTrace (cyclicGrading g u v)) 0 (cyclicLength u v - 1) ∨
      VWitness (geometricTrace (cyclicGrading g u v)) 0 (cyclicLength u v - 1)

theorem cyclic_pair_correspondence {m : ℕ} {P : TNEPath}
    (g : Grading m P) (u v : KroneckerPaperPaths.Edge P) :
    (HWitness (geometricTrace (cyclicGrading g u v)) 0 (cyclicLength u v - 1) ∨
      VWitness (geometricTrace (cyclicGrading g u v)) 0 (cyclicLength u v - 1)) ↔
    (HWitness (geometricTrace g) u.val
        (KroneckerSourceCompatibility.lift P.steps.length u.val v.val) ∨
      VWitness (geometricTrace g) u.val
        (KroneckerSourceCompatibility.lift P.steps.length u.val v.val)) := by
  have he : ∀ k, k < cyclicLength u v →
      geometricTrace (cyclicGrading g u v) k = geometricTrace g (u.val + k) := by
    intro k hk
    exact cyclicTrace_correspondence g u v ⟨k, by simpa using hk⟩
  have hl := cyclicLength_lift u v
  have hs : u.val + cyclicLength u v - 1 =
      KroneckerSourceCompatibility.lift P.steps.length u.val v.val := by omega
  simpa only [hs] using or_congr
    (hwitness_subpath (cyclicLength_pos u v) he)
    (vwitness_subpath (cyclicLength_pos u v) he)

theorem compatible_iff_core {m : ℕ} {P : TNEPath} (g : Grading m P) :
    Compatible g ↔ CyclicCompatible (geometricTrace g) P.steps.length := by
  constructor
  · intro h u v hu hv hU hV
    exact (cyclic_pair_correspondence g ⟨u, hu⟩ ⟨v, hv⟩).mp
      (h ⟨u, hu⟩ ⟨v, hv⟩ hU hV)
  · intro h u v hU hV
    exact (cyclic_pair_correspondence g u v).mpr (h u.val v.val u.isLt v.isLt hU hV)

theorem compatible_iff_source {m : ℕ} {P : TNEPath} (g : Grading m P) :
    Compatible g ↔ KroneckerSourceCompatibility.Cyclic (geometricTrace g) P.steps.length :=
  (compatible_iff_core g).trans
    (KroneckerSourceCompatibility.cyclic_iff (geometricTrace_periodic g)).symm

theorem compatible_witness_counts {m : ℕ} {P : TNEPath} (g : Grading m P) :
    Compatible g ↔ ∀ u v : KroneckerPaperPaths.Edge P,
      PositiveH (geometricTrace g) u.val → PositiveV (geometricTrace g) v.val →
      let E := geometricTrace (cyclicGrading g u v)
      (∃ k, 0 < k ∧ k < cyclicLength u v - 1 ∧ Vertical E k ∧
        intervalSum hGrade E 0 (k + 1) = intervalSum vCount E 0 (k + 1)) ∨
      (∃ k, 0 < k ∧ k < cyclicLength u v - 1 ∧ Horizontal E k ∧
        intervalSum hCount E k (cyclicLength u v - k) =
          intervalSum vGrade E k (cyclicLength u v - k)) := by
  unfold Compatible
  simp only [hwitness_counts, vwitness_counts, Nat.sub_zero]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro v
  have hlen : cyclicLength u v - 1 + 1 = cyclicLength u v := by
    have := cyclicLength_pos u v
    omega
  simp only [hlen]

theorem compatible_connected_component {m : ℕ} {P : TNEPath} (g : Grading m P)
    (hroot : RootComponent (geometricTrace g) P.steps.length) :
    Compatible g ↔ KroneckerPaperConnected.Connected (geometricTrace g) P.steps.length :=
  (compatible_iff_core g).trans (KroneckerPaperCompatibility.connected_iff_cyclic hroot).symm

theorem geometricTrace_translate {m : ℕ} {P : TNEPath} (g : Grading m P)
    (t : LatticePoint) : geometricTrace (translateGrading g t) = geometricTrace g := by
  unfold geometricTrace
  rw [translateGrading_occurrences]
  rfl

theorem compatible_translate {m : ℕ} {P : TNEPath} (g : Grading m P)
    (t : LatticePoint) : Compatible (translateGrading g t) ↔ Compatible g := by
  rw [compatible_iff_core, compatible_iff_core, geometricTrace_translate]
  rfl

end
end KroneckerPaperPathGradings
