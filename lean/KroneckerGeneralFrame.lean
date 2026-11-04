import KroneckerFiniteCoefficientIntegration

set_option autoImplicit false

namespace KroneckerGeneralFrame
noncomputable section
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerFiniteCoefficientIntegration
open KroneckerSourceGradingDictionary KroneckerSourcePartitionSums KroneckerSourcePartitions
open KroneckerSourceMaximalPath KroneckerPublishedEnumerationApplication
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerWeights KroneckerTight
open KroneckerDyck KroneckerSourcePositionBridge KroneckerPublishedPositionApplication
open KroneckerSourceIntervalCounts KroneckerSourceCompatibility KroneckerSourceHorizontalShadow
open KroneckerSourcePrefixBounds KroneckerSourceDominantShadow
open scoped BigOperators

theorem weighted_euler (G : Geometry) (S : FiniteEnumeration G)
    (m a b N d₁ d₂ : ℕ) (shape : ℕ → Bool) (hm : 3 ≤ m)
    (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (haD : a ≤ d₁) (hbD : b ≤ d₂) (hN : N = d₁ + d₂)
    (hmax : Maximal d₁ d₂ shape) (hdet : (a : ℤ) * d₂ - (b : ℤ) * d₁ = -1) :
    (weightedCount (fun d : Grades m N => Tight shape a b (representative d)) : ℚ) =
      (m : ℚ) * (euler (family G) m a b : ℚ) := by
  rw [← KroneckerSourceGradingDictionary.weighted_tight_eq,
    ← incoming_partition_enumeration]
  have hd : (a : ℤ) * d₂ - (b : ℤ) * d₁ = -(Nat.gcd a b : ℕ) := by
    simpa only [hc.gcd_eq_one, Nat.cast_one] using hdet
  have hco : ∀ P : Nat.Partition a × Nat.Partition b,
      S.lambda a b P = coefficient N a b shape P := by
    intro P
    rw [hN]
    exact S.count a b d₁ d₂ shape ha hb haD hbD hmax hd P
  rw [partitionSum]
  simp_rw [← hco]
  rw [S.primitive_euler m a b hm ha hb hc, euler_comparison]

theorem tight_located (m a b d₁ d₂ k : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (haD : a < d₁) (hbD : b < d₂)
    (hdet : (b : ℤ) * d₁ - (a : ℤ) * d₂ = 1)
    (hN : a + b + 1 + k = d₁ + d₂)
    (g : Coloring m (a + b + 1 + k))
    (ht : Tight (KroneckerDyck.pathShape d₁ d₂) a b g) :
    LocatedTight (n := a + b + 1) (k := k) (KroneckerDyck.pathShape d₁ d₂) a b g := by
  have h := KroneckerDirectCoprimePosition.tight_position
    (by omega : 0 < d₁) (by omega : 0 < d₂) hN haD hbD hdet g ht
  refine ⟨ht, h.1, ?_⟩
  intro j
  have hz := h.2 (Fin.natAdd (a + b + 1) j).val (by simp)
    (Fin.natAdd (a + b + 1) j).isLt
  rw [trace_before _ _ _ (Fin.natAdd _ j).isLt, paint_grade] at hz
  exact hz

theorem finite_frame_identity (G : Geometry) (S : FiniteEnumeration G)
    (m a b d₁ d₂ k : ℕ) (hm : 3 ≤ m)
    (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (haD : a < d₁) (hbD : b < d₂)
    (hdet : (b : ℤ) * d₁ - (a : ℤ) * d₂ = 1)
    (hN : a + b + 1 + k = d₁ + d₂) :
    (Nat.card {g : Coloring m (a + b + 1) //
      Connected m (word (KroneckerDyck.pathShape d₁ d₂) g) 0} : ℤ) =
      (m : ℤ) * euler (family G) m a b := by
  let e : {g : Coloring m (a + b + 1 + k) // Tight (KroneckerDyck.pathShape d₁ d₂) a b g} ≃
      {g : Coloring m (a + b + 1 + k) //
        LocatedTight (n := a + b + 1) (k := k) (KroneckerDyck.pathShape d₁ d₂) a b g} := {
    toFun := fun g => ⟨g.val, tight_located m a b d₁ d₂ k ha hb hc haD hbD hdet hN g.val g.property⟩
    invFun := fun g => ⟨g.val, g.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have he := frame_edge_counts (show 0 < d₁ by omega) (show 0 < d₂ by omega) hdet
  have hcard := (frame_count (m := m) (k := k) (KroneckerDyck.pathShape d₁ d₂) a b he.1 he.2).trans
    (Nat.card_congr e).symm
  have hq : (Nat.card {g : Coloring m (a + b + 1) //
      Connected m (word (KroneckerDyck.pathShape d₁ d₂) g) 0} : ℚ) =
      (m : ℚ) * (euler (family G) m a b : ℚ) := by
    rw [hcard, tight_count_weighted]
    exact weighted_euler G S m a b (a + b + 1 + k) d₁ d₂ _ hm ha hb hc haD.le hbD.le hN
      (dyck_maximal (by omega) (by omega)) (by omega)
  exact_mod_cast hq

theorem finite_euler_upper (G : Geometry) (S : FiniteEnumeration G)
    (m a b d₁ d₂ k : ℕ) (hm : 3 ≤ m)
    (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (haD : a < d₁) (hbD : b < d₂)
    (hdet : (b : ℤ) * d₁ - (a : ℤ) * d₂ = 1)
    (hN : a + b + 1 + k = d₁ + d₂) :
    (m : ℤ) * euler (family G) m a b ≤ (2 : ℤ) ^ (m * (a + b + 1)) := by
  have hcount := connected_count_bound (m := m) (n := a + b + 1) (c := 0)
    (KroneckerDyck.pathShape d₁ d₂)
  have hi := finite_frame_identity G S m a b d₁ d₂ k hm ha hb hc haD hbD hdet hN
  rw [← hi]
  rw [pow_mul]
  exact_mod_cast hcount

theorem unit_euler_upper (G : Geometry) (S : FiniteEnumeration G)
    (m b : ℕ) (hm : 3 ≤ m) (hb : 0 < b) :
    (m : ℤ) * euler (family G) m 1 b ≤ (2 : ℤ) ^ (m * (1 + b + 1)) := by
  apply finite_euler_upper G S m 1 b 3 (3 * b - 1) (2 * b) hm (by omega) hb
    (by simp) (by omega) (by omega)
  · rw [Nat.cast_sub (by omega : 1 ≤ 3 * b)]
    push_cast
    ring
  · omega

end
end KroneckerGeneralFrame
