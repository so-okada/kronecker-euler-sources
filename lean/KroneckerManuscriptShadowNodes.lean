import KroneckerManuscriptPathDefinitions

set_option autoImplicit false
noncomputable section
namespace KroneckerPaperPathGradings
open KroneckerPaperPaths KroneckerPredecessor KroneckerPaperTraceBridge

theorem firstShadow_all_nodes {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (hs : FirstShadow g u v) :
    let U := sample (geometricTrace (cyclicGrading g u v)) (cyclicLength u v)
    ∃ p : Fin (cyclicLength u v) → Fin (cyclicLength u v),
      ValidThrough U p (cyclicLength u v) ∧ KroneckerPaperConnected.FullRoot U p ∧
      ∀ x, KroneckerPredecessor.IsHorizontal U x → 0 < (U x).grade →
        ∃ z, KroneckerPredecessor.IsNode U p x z ∧
          intervalVerticalCount U x.val (z.val+1) = intervalHorizontalGrade U x.val (z.val+1) ∧
          ∀ k, x.val < k → k ≤ z.val →
            intervalVerticalCount U x.val k < intervalHorizontalGrade U x.val k := by
  dsimp only
  obtain ⟨p,hp,hr⟩ := firstShadow_predecessor_and_root g u v hs
  refine ⟨p,hp,hr,?_⟩
  intro x hx hg
  obtain ⟨a,b,hn,ha,hb⟩ := hr
  have hnX : ∃ z, KroneckerPredecessor.IsNode
      (sample (geometricTrace (cyclicGrading g u v)) (cyclicLength u v)) p x z := by
    by_cases he : x=a
    · exact ⟨b,by simpa only [he] using hn⟩
    · have hx0 : a.val < x.val := by
        have hxne : x.val ≠ a.val := fun h => he (Fin.ext h)
        omega
      obtain ⟨z,hz,_⟩ := hn.interior_node hp hx hx0 (by have := x.isLt; omega) hg
      exact ⟨z,hz⟩
  obtain ⟨z,hz⟩ := hnX
  exact ⟨z,hz,hz.horizontal_shadow_equality hp,
    fun k hxk hkz => hz.horizontal_shadow_prefix hp hxk hkz⟩

end KroneckerPaperPathGradings
#print axioms KroneckerPaperPathGradings.firstShadow_all_nodes
