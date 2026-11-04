import KroneckerNaturalShadows
import KroneckerPublishedEnumerationApplication
import KroneckerDyck
import KroneckerManuscriptShadowSupport

/-! Definitions 2.15--2.16: totals, compatible gradings with fixed totals,
both signs of tightness, and the equivalence used by the finite frame proof. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths

def TEG {P : TNEPath} (g : Grading P) : ℕ :=
  KroneckerSourcePartitions.hTotal (KroneckerWordCounts.pathShape P.steps)
    (fun i => g (edgeEquiv P i))
def TNG {P : TNEPath} (g : Grading P) : ℕ :=
  KroneckerSourcePartitions.vTotal (KroneckerWordCounts.pathShape P.steps)
    (fun i => g (edgeEquiv P i))

theorem TEG_cast {P : TNEPath} (g : Grading P) :
    (TEG g : ℤ) = KroneckerSourceIntervalCounts.hWeight (geometricTrace g) 0 P.steps.length :=
  KroneckerSourcePartitions.horizontal_total_cast _ _
theorem TNG_cast {P : TNEPath} (g : Grading P) :
    (TNG g : ℤ) = KroneckerSourceIntervalCounts.vWeight (geometricTrace g) 0 P.steps.length :=
  KroneckerSourcePartitions.vertical_total_cast _ _

theorem totals_eq_bound {P : TNEPath} (g : Grading P) : TEG g + TNG g = gradeBound g := by
  have h := KroneckerSourceNaturalGradings.natural_total
    (KroneckerWordCounts.pathShape P.steps) (fun i => g (edgeEquiv P i))
  change KroneckerSourceIntervalCounts.hWeight (geometricTrace g) 0 P.steps.length +
    KroneckerSourceIntervalCounts.vWeight (geometricTrace g) 0 P.steps.length = (gradeBound g : ℤ) at h
  rw [← TEG_cast g, ← TNG_cast g] at h
  exact_mod_cast h

def HSupport {P : TNEPath} (g : Grading P) : Prop := N_g g ⊆ ShSet g (E_g g)
def VSupport {P : TNEPath} (g : Grading P) : Prop := E_g g ⊆ ShSet g (N_g g)

theorem hSupport_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) :
    HSupport (ofBounded g) ↔
      ∀ v : KroneckerPaperPathGradings.Vertical P, 0 < (g v.val).val →
        ∃ u : KroneckerPaperPathGradings.Horizontal P, 0 < (g u.val).val ∧
          v.val ∈ KroneckerPaperPathGradings.horizontalShadow g
            ((edgeEquiv P).symm u.val) := by
  constructor
  · intro h v hv
    obtain ⟨u,⟨hu,hgu⟩,hm⟩ := h ⟨v.property,hv⟩
    refine ⟨⟨u,hu⟩,hgu,?_⟩
    change v.val ∈ Sh (ofBounded g) u at hm
    rw [Sh,ite_eq_left hu,hShadow_ofBounded g _ (by
      simpa only [ofBounded,Equiv.apply_symm_apply] using hgu)] at hm
    exact hm
  · intro h v hv
    obtain ⟨u,hgu,hm⟩ := h ⟨v,hv.1⟩ hv.2
    refine ⟨u.val,⟨u.property,hgu⟩,?_⟩
    change v ∈ Sh (ofBounded g) u.val
    rw [Sh,ite_eq_left (show u.val ∈ E P from u.property),hShadow_ofBounded g _ (by simpa using hgu)]
    exact hm

def CompatibleAtTotals {P : TNEPath} (p q : ℕ) (g : Grading P) : Prop :=
  Compatible g ∧ TNG g = p ∧ TEG g = q

def NegativeTight {P : TNEPath} (p q : ℕ) (g : Grading P) : Prop :=
  CompatibleAtTotals p q g ∧ HSupport g

theorem negativeTight_ofBounded {m : ℕ} {P : TNEPath} (p q : ℕ)
    (g : KroneckerPaperPathGradings.Grading m P) :
    NegativeTight p q (ofBounded g) ↔ KroneckerPaperPathGradings.TightAtTotals p q g := by
  have hc := KroneckerPaperPathGradings.ambientCompatible_iff g
  have hh := hSupport_ofBounded g
  have ht := TEG_cast (ofBounded g)
  have hn := TNG_cast (ofBounded g)
  unfold NegativeTight CompatibleAtTotals KroneckerPaperPathGradings.TightAtTotals
    KroneckerPaperPathGradings.Tight
  rw [compatible_ofBounded, hc, hh]
  constructor
  · rintro ⟨⟨hc,hp,hq⟩,hs⟩
    refine ⟨⟨hc,hs⟩,?_,?_⟩
    · exact ht.symm.trans (congrArg (fun n : ℕ => (n : ℤ)) hq)
    · exact hn.symm.trans (congrArg (fun n : ℕ => (n : ℤ)) hp)
  · rintro ⟨⟨hc,hs⟩,hq,hp⟩
    refine ⟨⟨hc,?_,?_⟩,hs⟩
    · exact_mod_cast (hn.trans hp)
    · exact_mod_cast (ht.trans hq)

theorem negativeTight_iff_source {P : TNEPath} (p q : ℕ) (g : Grading P) :
    NegativeTight p q g ↔ KroneckerSourceNaturalGradings.NaturalTight
      (KroneckerWordCounts.pathShape P.steps) p q (fun i => g (edgeEquiv P i)) :=
  (negativeTight_ofBounded p q (bounded g)).trans
    (KroneckerPaperPathGradings.tightAtTotals_iff_source p q (bounded g))

def maximalDyckPath (d₁ d₂ : ℕ) : TNEPath :=
  ofSteps (KroneckerDyck.shapePrefix (KroneckerDyck.pathShape d₁ d₂) (d₁+d₂)) 0

theorem maximalDyckPath_runs {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    (maximalDyckPath d₁ d₂).steps = (List.range d₁).flatMap
      (fun j => KroneckerStack.runShape (KroneckerDyck.runLength d₁ d₂ j)) := by
  have h := KroneckerDyck.path_runs h₁ h₂ d₁
  simpa [KroneckerDyck.boundary, Nat.mul_div_cancel_left _ h₁, maximalDyckPath, ofSteps] using h

def CG (d₁ d₂ p q : ℕ) : Set (Grading (maximalDyckPath d₁ d₂)) :=
  {g | CompatibleAtTotals p q g}

def Tight {P : TNEPath} (d₁ d₂ p q : ℕ) (g : Grading P) : Prop :=
  CompatibleAtTotals p q g ∧
    (((p : ℤ)*d₂-(q : ℤ)*d₁ = (Nat.gcd p q : ℤ) ∧ VSupport g) ∨
     ((p : ℤ)*d₂-(q : ℤ)*d₁ = -(Nat.gcd p q : ℤ) ∧ HSupport g))

theorem tight_negative {P : TNEPath} {d₁ d₂ p q : ℕ} (g : Grading P)
    (hdet : (p : ℤ)*d₂-(q : ℤ)*d₁ = -(Nat.gcd p q : ℤ))
    (hc : 0 < Nat.gcd p q) :
    Tight d₁ d₂ p q g ↔ NegativeTight p q g := by
  unfold Tight NegativeTight
  have hn : (p : ℤ)*d₂-(q : ℤ)*d₁ ≠ (Nat.gcd p q : ℤ) := by omega
  rw [iff_false_intro hn]
  simp only [false_and,false_or,hdet,true_and]

theorem tight_positive {P : TNEPath} {d₁ d₂ p q : ℕ} (g : Grading P)
    (hdet : (p : ℤ)*d₂-(q : ℤ)*d₁ = (Nat.gcd p q : ℤ))
    (hc : 0 < Nat.gcd p q) :
    Tight d₁ d₂ p q g ↔ CompatibleAtTotals p q g ∧ VSupport g := by
  unfold Tight
  have hn : (p : ℤ)*d₂-(q : ℤ)*d₁ ≠ -(Nat.gcd p q : ℤ) := by omega
  rw [iff_false_intro hn]
  simp only [false_and,or_false,hdet,true_and]

theorem tight_det_negative_one {P : TNEPath} {d₁ d₂ p q : ℕ} (g : Grading P)
    (hdet : (p : ℤ)*d₂-(q : ℤ)*d₁ = -1) :
    Tight d₁ d₂ p q g ↔ KroneckerSourceNaturalGradings.NaturalTight
      (KroneckerWordCounts.pathShape P.steps) p q (fun i => g (edgeEquiv P i)) := by
  have hq : (Nat.gcd p q : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.gcd_dvd_right p q
  have hp : (Nat.gcd p q : ℤ) ∣ (p : ℤ) := by exact_mod_cast Nat.gcd_dvd_left p q
  have hdiv : (Nat.gcd p q : ℤ) ∣ (q : ℤ)*d₁-(p : ℤ)*d₂ :=
    dvd_sub (dvd_mul_of_dvd_left hq (d₁ : ℤ)) (dvd_mul_of_dvd_left hp (d₂ : ℤ))
  have hone : (q : ℤ)*d₁-(p : ℤ)*d₂ = 1 := by omega
  rw [hone] at hdiv
  have hc : Nat.gcd p q = 1 := Nat.dvd_one.mp (by exact_mod_cast hdiv)
  exact (tight_negative g (by simpa only [hc,Nat.cast_one] using hdet) (by omega)).trans
    (negativeTight_iff_source p q g)

theorem grade_le_totals {P : TNEPath} {p q : ℕ} {g : Grading P}
    (h : CompatibleAtTotals p q g) (e : GeomEdge P) : g e ≤ p+q := by
  have he := grade_le_bound g e
  rw [← totals_eq_bound,h.2.1,h.2.2] at he
  omega

theorem compatibleAtTotals_finite (P : TNEPath) (p q : ℕ) :
    Finite {g : Grading P // CompatibleAtTotals p q g} := by
  let : Fintype (GeomEdge P) := Fintype.ofEquiv (Edge P) (edgeEquiv P)
  let f : {g : Grading P // CompatibleAtTotals p q g} → (GeomEdge P → Fin (p+q+1)) :=
    fun g e => ⟨g.val e, Nat.lt_succ_of_le (grade_le_totals g.property e)⟩
  apply Finite.of_injective f
  intro g h heq
  apply Subtype.ext
  funext e
  exact congrArg (fun z : GeomEdge P → Fin (p+q+1) => (z e).val) heq

theorem zero_totals_support {P : TNEPath} {g : Grading P}
    (h : CompatibleAtTotals 0 0 g) : HSupport g ∧ VSupport g := by
  have hz : ∀ e, g e = 0 := fun e => Nat.eq_zero_of_le_zero (grade_le_totals h e)
  constructor
  · intro e he
    have hp := he.2
    rw [hz e] at hp
    exact False.elim (Nat.not_lt_zero _ hp)
  · intro e he
    have hp := he.2
    rw [hz e] at hp
    exact False.elim (Nat.not_lt_zero _ hp)

theorem connectedCount_eq_pathCount (m : ℕ) (P : TNEPath) (d : ℕ) :
    connectedCount m P d = KroneckerWordCounts.pathCount m P.steps d :=
  (connectedCount_eq_bounded m P d).trans
    (KroneckerPaperPathGradings.connectedCount_eq_pathCount m P d)

def binomialWeight {P : TNEPath} (m : ℕ) (g : Grading P) : ℕ :=
  ∏ i : Edge P, Nat.choose m (g (edgeEquiv P i))

theorem binomialWeight_zero {P : TNEPath} {m : ℕ} (g : Grading P)
    (e : GeomEdge P) (he : m < g e) : binomialWeight m g = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ ((edgeEquiv P).symm e))
  simpa using Nat.choose_eq_zero_of_lt he

end KroneckerNaturalPathGradings
