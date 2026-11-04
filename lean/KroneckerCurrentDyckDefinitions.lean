import KroneckerNaturalTightness

/-! Definition 2.20: the geometric function pi and
the set TCG of tight compatible natural-valued gradings. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths KroneckerDyck KroneckerColoring

private theorem displacement_shapePrefix (shape : ℕ → Bool) (n : ℕ) :
    displacement (shapePrefix shape n) = (HEdges shape n, VEdges shape n) := by
  induction n with
  | zero => simp [shapePrefix, HEdges, VEdges]; rfl
  | succ n ih =>
    rw [shapePrefix_add shape n 1, displacement_append, ih,
      hedges_succ, vedges_succ]
    cases h : shape n <;> simp [List.ofFn_succ, displacement, stepVector, h]

private theorem take_shapePrefix (shape : ℕ → Bool) {n N : ℕ} (h : n ≤ N) :
    (shapePrefix shape N).take n = shapePrefix shape n := by
  rw [show N = n + (N-n) by omega, shapePrefix_add]
  simp [shapePrefix]

/-- The left or lower endpoint of the i-th edge of the maximal Dyck path. -/
theorem maximalDyckPath_vertex (d₁ d₂ : ℕ) (i : Edge (maximalDyckPath d₁ d₂)) :
    vertex (maximalDyckPath d₁ d₂) i.val =
      (HEdges (pathShape d₁ d₂) i.val, VEdges (pathShape d₁ d₂) i.val) := by
  have hi : i.val ≤ d₁+d₂ := by
    have := i.isLt
    simpa [maximalDyckPath, shapePrefix] using Nat.le_of_lt this
  simp only [vertex, maximalDyckPath, ofSteps_steps]
  have ho : (ofSteps (shapePrefix (pathShape d₁ d₂) (d₁+d₂)) 0).origin = 0 := by
    simp [ofSteps]
  rw [ho, zero_add, take_shapePrefix _ hi, displacement_shapePrefix]

/-- The function pi_(d1,d2) in Definition 2.20(2), with its stated finite range. -/
def pi {d₁ d₂ : ℕ} (e : GeomEdge (maximalDyckPath d₁ d₂)) : Fin (d₁+d₂) :=
  ⟨coord d₁ d₂ ((edgeEquiv _).symm e).val, coord_bound (by
    have := ((edgeEquiv _).symm e).isLt
    simp only [maximalDyckPath, ofSteps_steps, shapePrefix, List.length_ofFn] at this
    omega) _⟩

theorem pi_formula {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (e : GeomEdge (maximalDyckPath d₁ d₂)) :
    ((pi e).val : ℤ) = e.val.1.1 * d₂ - e.val.1.2 * d₁ := by
  obtain ⟨i, rfl⟩ := (edgeEquiv _).surjective e
  simp only [pi, edgeEquiv_symm_apply_apply, edgeEquiv_apply, edge,
    maximalDyckPath_vertex]
  exact coordinate_identity h₁ h₂ i.val

theorem pi_injective {d₁ d₂ : ℕ} (hc : Nat.Coprime d₁ d₂) :
    Function.Injective (pi (d₁ := d₁) (d₂ := d₂)) := by
  intro e f hef
  apply (edgeEquiv _).symm.injective
  apply Fin.ext
  apply coordinate_injective hc
  · simpa [maximalDyckPath, shapePrefix] using ((edgeEquiv _).symm e).isLt
  · simpa [maximalDyckPath, shapePrefix] using ((edgeEquiv _).symm f).isLt
  · exact congrArg Fin.val hef

/-- Tight compatible gradings with vertical total p and horizontal total q. -/
def TCG (d₁ d₂ p q : ℕ) : Set (Grading (maximalDyckPath d₁ d₂)) :=
  {g ∈ CG d₁ d₂ p q | Tight d₁ d₂ p q g}

theorem mem_TCG {d₁ d₂ p q : ℕ} (g : Grading (maximalDyckPath d₁ d₂)) :
    g ∈ TCG d₁ d₂ p q ↔ Tight d₁ d₂ p q g := by
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem TCG_subset_CG (d₁ d₂ p q : ℕ) : TCG d₁ d₂ p q ⊆ CG d₁ d₂ p q :=
  fun _ h => h.1

theorem TCG_finite (d₁ d₂ p q : ℕ) : Finite (TCG d₁ d₂ p q) := by
  let : Finite (CG d₁ d₂ p q) := compatibleAtTotals_finite (maximalDyckPath d₁ d₂) p q
  let f : TCG d₁ d₂ p q → CG d₁ d₂ p q := fun g => ⟨g.val, g.property.1⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : CG d₁ d₂ p q => z.val) h

theorem mem_TCG_negative {d₁ d₂ p q : ℕ}
    (g : Grading (maximalDyckPath d₁ d₂))
    (hdet : (p : ℤ)*d₂-(q : ℤ)*d₁ = -(Nat.gcd p q : ℤ))
    (hc : 0 < Nat.gcd p q) :
    g ∈ TCG d₁ d₂ p q ↔ g ∈ CG d₁ d₂ p q ∧ HSupport g :=
  (mem_TCG g).trans (tight_negative g hdet hc)

theorem mem_TCG_positive {d₁ d₂ p q : ℕ}
    (g : Grading (maximalDyckPath d₁ d₂))
    (hdet : (p : ℤ)*d₂-(q : ℤ)*d₁ = (Nat.gcd p q : ℤ))
    (hc : 0 < Nat.gcd p q) :
    g ∈ TCG d₁ d₂ p q ↔ g ∈ CG d₁ d₂ p q ∧ VSupport g :=
  (mem_TCG g).trans (tight_positive g hdet hc)

theorem mem_TCG_det_negative_one {d₁ d₂ p q : ℕ}
    (g : Grading (maximalDyckPath d₁ d₂))
    (hdet : (p : ℤ)*d₂-(q : ℤ)*d₁ = -1) :
    g ∈ TCG d₁ d₂ p q ↔ KroneckerSourceNaturalGradings.NaturalTight
      (KroneckerWordCounts.pathShape (maximalDyckPath d₁ d₂).steps)
      p q (fun i => g (edgeEquiv _ i)) :=
  (mem_TCG g).trans (tight_det_negative_one g hdet)

end KroneckerNaturalPathGradings
