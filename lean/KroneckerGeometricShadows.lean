import KroneckerGeometricCompatibility
import KroneckerCyclicCutInvariance

set_option autoImplicit false

namespace KroneckerCompatibility
open KroneckerStack

theorem walk_prefix_congr {E F : ℕ → Edge} {n : ℕ}
    (h : ∀ k, k < n → E k = F k) (f : Edge → ℤ) (k : ℕ) (hk : k ≤ n) :
    walk f E k = walk f F k := by
  have hh := walk_subpath (a := 0) (l := n) (E := F) (F := E)
    (by simpa only [Nat.zero_add] using h) f k hk
  simpa only [Nat.zero_add, walk, sub_zero] using hh

theorem rootComponent_prefix_congr {E F : ℕ → Edge} {n : ℕ}
    (h : ∀ k, k < n → E k = F k) : RootComponent E n ↔ RootComponent F n := by
  by_cases hn : 0 < n
  · have hzero := h 0 hn
    have hd : ∀ k, k ≤ n → debt E k = debt F k := walk_prefix_congr h Edge.debtChange
    simp only [RootComponent, PositiveH, hzero, hd n le_rfl]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply forall_congr'
    intro k
    apply imp_congr_right
    intro _
    apply imp_congr_right
    intro hk
    rw [hd k hk.le]
  · simp only [RootComponent, hn, false_and]

theorem connected_prefix_congr {E F : ℕ → Edge} {n : ℕ}
    (h : ∀ k, k < n → E k = F k) :
    KroneckerPaperConnected.Connected E n ↔ KroneckerPaperConnected.Connected F n := by
  have hs : KroneckerPaperTraceBridge.sample E n = KroneckerPaperTraceBridge.sample F n := by
    funext k
    exact h k.val k.isLt
  unfold KroneckerPaperConnected.Connected
  rw [hs]

theorem root_iff_first_vertical_return (E : ℕ → Edge) (n : ℕ) :
    RootComponent E n ↔ 0 < n ∧ PositiveH E 0 ∧ Vertical E (n - 1) ∧
      debt E n = 0 ∧ ∀ k, 0 < k → k < n → Vertical E (k - 1) → debt E k ≠ 0 := by
  constructor
  · intro hr
    refine ⟨hr.1, hr.2.1, ?_, hr.2.2.1, fun k hk hkn _ => ne_of_gt (hr.2.2.2 k hk hkn)⟩
    obtain ⟨g, hg, he⟩ := hr.2.1
    have h1 : 0 < debt E 1 := by simp [debt, walk, he, Edge.debtChange]; exact hg
    have hn : 1 < n := by
      have hz := hr.2.2.1
      by_contra hh
      have hn1 : n = 1 := by have := hr.1; omega
      rw [hn1] at hz
      omega
    have hp := hr.2.2.2 (n - 1) (by omega) (by omega)
    have hz : debt E (n - 1 + 1) = 0 := by simpa [Nat.sub_add_cancel hr.1] using hr.2.2.1
    rw [debt_step] at hz
    cases he' : E (n - 1) with
    | H j => simp only [he', Edge.debtChange] at hz; omega
    | V j => exact ⟨j, he'⟩
  · rintro ⟨hn, hH, _, hz, hp⟩
    apply (root_iff_first_return E n).mpr
    refine ⟨hn, hH, hz, ?_⟩
    intro k hk hkn hkz
    obtain ⟨g, hg, he⟩ := hH
    have h1 : 0 < debt E 1 := by simp [debt, walk, he, Edge.debtChange]; exact hg
    obtain ⟨e, hle, hlt, hv, hd⟩ := debt_crossing E 0 (by omega : 1 ≤ k) h1 (by omega)
    exact hp (e + 1) (by omega) (by omega) (by simpa using hv) hd

end KroneckerCompatibility

namespace KroneckerPaperPathGradings
noncomputable section
open KroneckerPaperPaths KroneckerCompatibility


def FirstShadow {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P) : Prop :=
  let F := geometricTrace (cyclicGrading g u v)
  PositiveH (geometricTrace g) u.val ∧
    intervalSum hGrade F 0 (cyclicLength u v) = intervalSum vCount F 0 (cyclicLength u v) ∧
    ∀ k, 0 < k → k < cyclicLength u v →
      intervalSum hGrade F 0 k ≠ intervalSum vCount F 0 k

theorem firstShadow_iff_root {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P) :
    FirstShadow g u v ↔ RootComponent (geometricTrace (cyclicGrading g u v)) (cyclicLength u v) := by
  let F := geometricTrace (cyclicGrading g u v)
  have he : F 0 = geometricTrace g u.val := by
    have hh := cyclicTrace_correspondence g u v
      ⟨0, by simpa using cyclicLength_pos u v⟩
    simpa only [Nat.add_zero] using hh
  have hd (k : ℕ) : debt F k = intervalSum hGrade F 0 k - intervalSum vCount F 0 k := by
    simpa only [Nat.zero_add, debt, walk, sub_zero] using debt_interval F 0 k
  rw [root_iff_first_return]
  constructor
  · rintro ⟨hH, hz, hp⟩
    refine ⟨cyclicLength_pos u v, ?_, ?_, ?_⟩
    · change PositiveH F 0
      simpa only [PositiveH, he] using hH
    · change debt F (cyclicLength u v) = 0
      rw [hd, hz, sub_self]
    · intro k hk hkl
      change debt F k ≠ 0
      rw [hd, sub_ne_zero]
      exact hp k hk hkl
  · rintro ⟨_, hH, hz, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · change PositiveH F 0 at hH
      simpa only [PositiveH, he] using hH
    · exact sub_eq_zero.mp ((hd _).symm.trans hz)
    · intro k hk hkl
      exact sub_ne_zero.mp (by rw [← hd]; exact hp k hk hkl)

theorem firstShadow_iff_first_vertical_equality {m : ℕ} {P : TNEPath}
    (g : Grading m P) (u v : Edge P) :
    FirstShadow g u v ↔
      let F := geometricTrace (cyclicGrading g u v)
      PositiveH F 0 ∧ Vertical F (cyclicLength u v - 1) ∧
        intervalSum hGrade F 0 (cyclicLength u v) = intervalSum vCount F 0 (cyclicLength u v) ∧
        ∀ k, 0 < k → k < cyclicLength u v → Vertical F (k - 1) →
          intervalSum hGrade F 0 k ≠ intervalSum vCount F 0 k := by
  rw [firstShadow_iff_root, root_iff_first_vertical_return]
  have hd (F : ℕ → KroneckerStack.Edge) (k : ℕ) :
      debt F k = intervalSum hGrade F 0 k - intervalSum vCount F 0 k := by
    simpa only [Nat.zero_add, debt, walk, sub_zero] using debt_interval F 0 k
  simp only [cyclicLength_pos, true_and, hd, sub_eq_zero, ne_eq]

theorem firstShadow_predecessor_and_root {m : ℕ} {P : TNEPath}
    (g : Grading m P) (u v : Edge P) (hs : FirstShadow g u v) :
    let F := geometricTrace (cyclicGrading g u v)
    let n := cyclicLength u v
    ∃ p : Fin n → Fin n,
      KroneckerPredecessor.ValidThrough (KroneckerPaperTraceBridge.sample F n) p n ∧
      KroneckerPaperConnected.FullRoot (KroneckerPaperTraceBridge.sample F n) p := by
  have hr := (firstShadow_iff_root g u v).mp hs
  obtain ⟨f, hf⟩ := KroneckerShadow.root_trace_exists hr
  obtain ⟨p, hp⟩ := KroneckerPaperTraceBridge.followsTrace_exists hf
  have hv := KroneckerPaperTraceBridge.followsTrace_valid hf hp
  exact ⟨p, hv, KroneckerPredecessor.root_component_full_node hr hv⟩

theorem firstShadow_ownedBalance {m : ℕ} {P : TNEPath}
    (g : Grading m P) (u v : Edge P) (hs : FirstShadow g u v)
    (p : Fin (cyclicLength u v) → Fin (cyclicLength u v))
    (hp : KroneckerPredecessor.ValidThrough
      (KroneckerPaperTraceBridge.sample (geometricTrace (cyclicGrading g u v)) (cyclicLength u v))
      p (cyclicLength u v)) :
    Compatible (cyclicGrading g u v) ↔ KroneckerPredecessor.OwnedBalance
      (KroneckerPaperTraceBridge.sample (geometricTrace (cyclicGrading g u v)) (cyclicLength u v)) p := by
  rw [compatible_iff_core, cyclicRealization_length]
  exact (KroneckerPaperCompatibility.ownedBalance_iff_cyclic hp
    ((firstShadow_iff_root g u v).mp hs)).symm

theorem firstShadow_compatible_restriction {m : ℕ} {P : TNEPath}
    (g : Grading m P) (u v : Edge P) (hs : FirstShadow g u v) (hc : Compatible g) :
    KroneckerPaperConnected.Connected (geometricTrace (cyclicGrading g u v)) (cyclicLength u v) := by
  have he : ∀ k, k < cyclicLength u v →
      geometricTrace (cyclicGrading g u v) k = geometricTrace g (u.val + k) := by
    intro k hk
    exact cyclicTrace_correspondence g u v ⟨k, by simpa using hk⟩
  have hr := (rootComponent_prefix_congr he).mp ((firstShadow_iff_root g u v).mp hs)
  have ht := (cyclicCompatible_shift (geometricTrace_periodic g) u.isLt).mpr
    ((compatible_iff_core g).mp hc)
  exact (connected_prefix_congr he).mpr
    (KroneckerPaperCompatibility.compatible_restriction hr (cyclicLength_le u v) ht)

theorem firstShadow_zero_extension {m : ℕ} {P : TNEPath}
    (g : Grading m P) (u v : Edge P) (hs : FirstShadow g u v)
    (hz : ∀ k, cyclicLength u v ≤ k → k < P.steps.length →
      (geometricTrace g (u.val + k)).grade = 0) :
    Compatible g ↔ KroneckerPaperConnected.Connected
      (geometricTrace (cyclicGrading g u v)) (cyclicLength u v) := by
  have he : ∀ k, k < cyclicLength u v →
      geometricTrace (cyclicGrading g u v) k = geometricTrace g (u.val + k) := by
    intro k hk
    exact cyclicTrace_correspondence g u v ⟨k, by simpa using hk⟩
  have hr := (rootComponent_prefix_congr he).mp ((firstShadow_iff_root g u v).mp hs)
  exact (compatible_iff_core g).trans
    ((cyclicCompatible_shift (geometricTrace_periodic g) u.isLt).symm.trans
      ((KroneckerPaperCompatibility.zero_extension_iff_connected hr
        (cyclicLength_le u v) hz).trans (connected_prefix_congr he).symm))

end
end KroneckerPaperPathGradings
