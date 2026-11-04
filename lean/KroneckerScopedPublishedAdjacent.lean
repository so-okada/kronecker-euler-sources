import KroneckerWeistUniformLower
import KroneckerWeistUniformConstants
import KroneckerScopedCanonicalPublishedEuler
import KroneckerCentralValueThree
import KroneckerEntropyRootTransfer

section

/- Original module: KroneckerScopedWeistApplication -/
section
/-! Application of the GENERAL published inputs. The full compatible-class
finsum is reduced to the actual finite stable index by proving omitted spaces
empty. Both Euler transport and positivity are then derived, not assumed in a
new family-specific wrapper. The external Geometry input remains explicit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedWeistApplication
open KroneckerScopedModuli KroneckerWeistApplicationGates
open KroneckerWeistStableIndexEquivalence KroneckerWeistIndexedSpaces
open KroneckerWeistCoverEmbedding KroneckerManuscriptCoverParameters
open KroneckerOrdinarySingularEuler KroneckerHomologyHomeomorphism
open KroneckerWeistLocalizationTransfer
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev WordClass := KroneckerWeistClassInjection.Class
def Active (a b : ℕ) (q : WordClass) : Prop := ∃ i : SourceIndex a b, i.val=q

/-- Choose the existing stable representative on active classes, and an
arbitrary representative on the remaining classes of the full source sum. -/
def representativeSection (a b : ℕ) (q : WordClass) : cover.V →₀ ℕ :=
  if h : Active a b q then (representative a b h.choose).1 else q.out

theorem representativeSection_spec (a b : ℕ) (q : WordClass) :
    Quotient.mk (translationSetoid (base a b)) (representativeSection a b q)=q := by
  unfold representativeSection
  split_ifs with h
  · exact (representative_spec a b h.choose).2.2.2.trans h.choose_spec
  · exact Quotient.out_eq q

theorem representativeSection_active (a b : ℕ) (q : SourceIndex a b) :
    representativeSection a b q.val=(representative a b q).1 := by
  have h : Active a b q.val := ⟨q,rfl⟩
  simp only [representativeSection,dite_eq_left h]
  have he : h.choose=q := Subtype.ext h.choose_spec
  rw [he]

def summand (G : Geometry) (a b : ℕ) (q : WordClass) : ℤ :=
  localizationTerm G a b (representativeSection a b q)

/-- A compatible class omitted from SourceIndex has EMPTY moduli. This uses
actual stable representations, not a presumed sign or a presumed Euler zero. -/
theorem omitted_empty (G : Geometry) (a b : ℕ) (ha : 0<a) (q : WordClass)
    (hn : ¬Active a b q)
    (hc : Compatible (base a b) (representativeSection a b q)) :
    IsEmpty (G.space (coverDatum (base a b) (representativeSection a b q))) := by
  apply not_nonempty_iff.mp
  intro h
  let d := representativeSection a b q
  let : KroneckerApplicationScope.Covered (coverDatum (base a b) d) :=
    KroneckerApplicationScope.coverCovered a b d hc
  have hd : d.mapDomain Prod.fst=pairDimension a b := (compatible_dictionary a b d).mp hc
  have hcan : Nonempty (canonical (coverDatum (base a b) d)) :=
    h.map (G.comparison (coverDatum (base a b) d)).symm
  have hs : Nonempty (KroneckerWeistOrbitTopology.coverSpace d a b) := hcan
  obtain ⟨R,hR⟩ := (KroneckerCanonicalSupportOrbit.nonempty_iff cover d
    (fun v => negativeWeight a b v.1)).mp hs
  exact hn ⟨⟨q,⟨d,R⟩,KroneckerWeistApplicationGates.compatible_nonzero a b ha d hd,
    hd,hR,representativeSection_spec a b q⟩,rfl⟩

theorem omitted_zero (G : Geometry) (a b : ℕ) (ha : 0<a) (q : WordClass)
    (hn : ¬Active a b q) : summand G a b q=0 := by
  unfold summand localizationTerm
  split_ifs with hc
  · let := omitted_empty G a b ha q hn hc
    exact ordinaryEuler_empty _
  · rfl

theorem active_term (G : Geometry) (a b : ℕ) (q : SourceIndex a b) :
    summand G a b q.val=G.euler (coverDatum (base a b) (representative a b q).1) := by
  unfold summand
  rw [representativeSection_active]
  apply dite_eq_left
  exact (compatible_dictionary a b _).mpr (representative_spec a b q).2.1

theorem finite_localization (G : Geometry) (W : Weist G) (a b : ℕ) (ha : 0<a)
    [Fintype (SourceIndex a b)] :
    G.euler (base a b)=∑ q : SourceIndex a b,
      G.euler (coverDatum (base a b) (representative a b q).1) := by
  have hW := W.localization a b (base_acyclic a b) (base_connected a b) (base_nonzero a b ha)
    (base_balanced a b) (representativeSection a b) (representativeSection_spec a b)
  change G.euler (base a b)=∑ᶠ q : WordClass,summand G a b q at hW
  rw [hW]
  let s : Finset WordClass := Finset.univ.image (fun q : SourceIndex a b => q.val)
  have hs : Function.support (summand G a b) ⊆ (s : Set WordClass) := by
    intro q hq
    by_contra hn
    apply hq
    apply omitted_zero G a b ha q
    rintro ⟨i,rfl⟩
    exact hn (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [finsum_eq_sum_of_support_subset _ hs]
  change (∑ q ∈ Finset.univ.image (fun q : SourceIndex a b => q.val),summand G a b q)=_
  rw [Finset.sum_image (by intro x _ y _ h;exact Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro q _
  exact active_term G a b q

def baseAdmissible (G : Geometry) (a b : ℕ) :
    Admissible (KroneckerCanonicalKroneckerModuli.space 3 a b) :=
  G.canonicalAdmissible (base a b)

def coverAdmissible (G : Geometry) (a b : ℕ) (q : SourceIndex a b) :
    Admissible (KroneckerWeistIndexedSpaces.space a b q) :=
  G.canonicalAdmissible (coverDatum (base a b) (representative a b q).1)

theorem cover_positive (G : Geometry) (W : Weist G) (a b : ℕ) (hc : a.Coprime b)
    (q : SourceIndex a b) :
    1≤ordinaryEuler (KroneckerWeistIndexedSpaces.space a b q) (coverAdmissible G a b q) := by
  let d := (representative a b q).1
  have hd := representative_spec a b q
  have hn : Nonempty (G.space (coverDatum (base a b) d)) :=
    (space_nonempty a b q).map (G.comparison (coverDatum (base a b) d))
  have hp := W.positive (coverDatum (base a b) d) (cover_acyclic a b d)
    (cover_nonzero a b d hd.1) (cover_balanced a b d hd.2.1)
    (cover_indivisible a b hc d hd.2.1) hn
  rw [←G.euler_comparison (coverDatum (base a b) d)] at hp
  exact hp

/-- The old SourceInput is a RESULT of the source application. There is no
family-specific localization, positivity, or homology premise in this type. -/
def sourceInput (G : Geometry) (W : Weist G) (a b : ℕ) (ha : 0<a)
    (hc : a.Coprime b) [Fintype (SourceIndex a b)] : SourceInput a b where
  base_admissible := baseAdmissible G a b
  cover_admissible := coverAdmissible G a b
  localizes := by
    change ordinaryEuler (canonical (base a b)) _ = _
    rw [G.euler_comparison,finite_localization G W a b ha]
    apply Finset.sum_congr rfl
    intro q _
    exact (G.euler_comparison (coverDatum (base a b) (representative a b q).1)).symm
  positive := cover_positive G W a b hc

end KroneckerScopedWeistApplication
end
end

/- Original module: KroneckerScopedWeistCountedLower -/
section
/-! Complete finite counted-family deduction, relative to the general explicit
analytic geometry input and Weist's general source statements. The manuscript
coprimality is gcd(a,n+2)=1, and is not dropped from the conclusion. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedWeistCountedLower
open KroneckerScopedModuli KroneckerScopedWeistApplication
open KroneckerWeistUniformLower KroneckerWeistStableIndexEquivalence
open KroneckerOrdinarySingularEuler KroneckerManuscriptSupportBound
open KroneckerManuscriptCountedIndex KroneckerEnumeratedCoverClasses
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

theorem index_card_le (G : Geometry) (W : Weist G) (a b : ℕ) (ha : 0<a)
    (hc : a.Coprime b) [Fintype (SourceIndex a b)] :
    (Fintype.card (SourceIndex a b) : ℤ) ≤
      ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a b) (baseAdmissible G a b) := by
  have H := sourceInput G W a b ha hc
  change (Fintype.card (SourceIndex a b) : ℤ)≤ordinaryEuler _ H.base_admissible
  rw [H.localizes]
  calc
    _ = ∑ _q : SourceIndex a b,(1 : ℤ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun q _ => H.positive q)

theorem counted_card_le (G : Geometry) (W : Weist G) (n a : ℕ) (x : ℝ)
    (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) (hc : a.Coprime (n+2)) :
    ((enumeratedCoverClasses hx ha).card : ℤ) ≤
      ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+n+2))
        (baseAdmissible G a (a+n+2)) := by
  let := sourceFintype n a x hx ha
  have hcop : a.Coprime (a+n+2) := by
    simpa only [Nat.add_assoc] using (Nat.coprime_self_add_right.mpr hc)
  have hi : Function.Injective (fun q : {q // q∈enumeratedCoverClasses hx ha} =>
      indexMap (countedIndex hx ha q)) :=
    (indexMap_injective a (a+n+2)).comp (countedIndex_injective hx ha)
  have hcard := Fintype.card_le_of_injective _ hi
  have hcardNat : (enumeratedCoverClasses hx ha).card≤Fintype.card (SourceIndex a (a+n+2)) := by
    simpa using hcard
  have hcard' : ((enumeratedCoverClasses hx ha).card : ℤ)≤Fintype.card (SourceIndex a (a+n+2)) := by
    exact_mod_cast hcardNat
  exact hcard'.trans (index_card_le G W a (a+n+2) (source_total_positive n a x hx ha) hcop)

/-- Quantitative lower bound with no SourceInput/AppliedInput hypothesis.
The constants are supplied by the already proved finite slot count. -/
theorem uniform_lower (G : Geometry) (W : Weist G) :
    ∃ A B : ℝ,0<A ∧ 0<B ∧
      ∀ (n a : ℕ) (x : ℝ) (_hx : 100000≤x) (_ha : ((n : ℝ)+2)*x=a)
        (_hc : a.Coprime (n+2)),
        manuscriptLower n a x A B ≤
          (ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+n+2))
            (baseAdmissible G a (a+n+2)) : ℝ) := by
  obtain ⟨A,B,hA,hB,h⟩ := uniform_source_lower
  refine ⟨A,B,hA,hB,?_⟩
  intro n a x hx ha hc
  let := sourceFintype n a x hx ha
  have hcop : a.Coprime (a+n+2) := by
    simpa only [Nat.add_assoc] using (Nat.coprime_self_add_right.mpr hc)
  exact h n a x hx ha inferInstance
    (sourceInput G W a (a+n+2) (source_total_positive n a x hx ha) hcop)

end KroneckerScopedWeistCountedLower
end
end

/- Original module: KroneckerScopedWeistFiniteLower -/
section
/-! The exact finite estimate displayed in the manuscript, with uniform
C0,q in (0,1]. Analytic Geometry and the general published Weist statements
remain visible. No entropy limit existence is assumed or concluded here. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedWeistFiniteLower
open KroneckerScopedModuli KroneckerOrdinarySingularEuler
open KroneckerScopedWeistApplication KroneckerWeistUniformConstants

theorem finite_lower (G : Geometry) (W : Weist G) :
    ∃ C q : ℝ, 0 < C ∧ C ≤ 1 ∧ 0 < q ∧ q ≤ 1 ∧
      ∀ a k : ℕ, 2 ≤ k → 100000*k ≤ a → a.Coprime k →
        C * (256/27 : ℝ)^a * ((k : ℝ)/a)^(5/2 : ℝ) * q^(k-1) ≤
          (ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+k))
            (baseAdmissible G a (a+k)) : ℝ) := by
  obtain ⟨A, B, hA, hB, H⟩ := KroneckerScopedWeistCountedLower.uniform_lower G W
  refine ⟨C0 A B, q A B, C0_pos hA hB, C0_le_one A B,
    q_pos hA hB, q_le_one A B, ?_⟩
  intro a k hk ha hc
  have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hbound : (100000 : ℝ)*k ≤ a := by exact_mod_cast ha
  have hx : (100000 : ℝ) ≤ (a : ℝ)/k := (le_div_iff₀ hkp).mpr hbound
  have hn : k-2+2 = k := by omega
  have hnR : ((k-2 : ℕ) : ℝ)+2 = (k : ℝ) := by exact_mod_cast hn
  have hscale : (((k-2 : ℕ) : ℝ)+2)*((a : ℝ)/k) = a := by
    rw [hnR]
    field_simp
  have hcop : a.Coprime (k-2+2) := by simpa [hn] using hc
  have he := H (k-2) a ((a : ℝ)/k) hx hscale hcop
  have hl := (normalized_lower hA hB hx (k-2) a).trans he
  have hdim : a+(k-2)+2 = a+k := by omega
  have hpower : k-2+1 = k-1 := by omega
  simpa only [hdim, hpower, ratio_scale hap hkp] using hl

theorem euler_positive_in_finite_region (G : Geometry) (W : Weist G)
    (a k : ℕ) (hk : 2 ≤ k) (ha : 100000*k ≤ a) (hc : a.Coprime k) :
    0 < ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+k))
      (baseAdmissible G a (a+k)) := by
  obtain ⟨C, q, hC, _, hq, _, H⟩ := finite_lower G W
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 < C * (256/27 : ℝ)^a * ((k : ℝ)/a)^(5/2 : ℝ) * q^(k-1) := by
    positivity
  exact_mod_cast hp.trans_le (H a k hk ha hc)

end KroneckerScopedWeistFiniteLower
end
end

/- Original module: KroneckerScopedWeistCentralLowerLimit -/
section
/-! The manuscript's central joint lower-limit consequence for actual ordinary
Euler characteristics, retaining the explicit Geometry and general Weist inputs.
The theorem neither assumes nor supplies existence of the entropy limit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedWeistCentralLowerLimit
open Filter KroneckerScopedModuli KroneckerOrdinarySingularEuler
open KroneckerScopedWeistApplication KroneckerLowerEntropyKernel KroneckerLowerEntropyTransfer
open scoped Topology

def E (G : Geometry) (a k : ℕ) : ℝ :=
  (ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+k))
    (baseAdmissible G a (a+k)) : ℝ)

variable {α : Type*} {l : Filter α} (a k : α → ℕ)

theorem eventually_finite_region
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0)) :
    ∀ᶠ i in l, 100000*k i ≤ a i := by
  filter_upwards [eventually_small_ratio a k ha hk 100000 (by norm_num)] with i hi
  exact_mod_cast hi

theorem euler_eventually_positive (G : Geometry) (W : Weist G)
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0))
    (hprimitive : ∀ᶠ i in l, 2 ≤ k i ∧ (a i).Coprime (k i)) :
    ∀ᶠ i in l, 0 < E G (a i) (k i) := by
  filter_upwards [eventually_finite_region a k ha hk, hprimitive] with i hi hp
  dsimp only [E]
  exact_mod_cast KroneckerScopedWeistFiniteLower.euler_positive_in_finite_region
    G W (a i) (k i) hp.1 hi hp.2

theorem central_lower_limit (G : Geometry) (W : Weist G)
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0))
    (hprimitive : ∀ᶠ i in l, 2 ≤ k i ∧ (a i).Coprime (k i)) :
    LowerLimit l (fun i => Real.log (E G (a i) (k i))/(a i : ℝ))
      (Real.log (256/27 : ℝ)) := by
  obtain ⟨C, q, hC, _, hq, _, H⟩ := KroneckerScopedWeistFiniteLower.finite_lower G W
  apply lower_limit_of_finite_bound a k (fun i => E G (a i) (k i)) hC hq ha hk
    (hprimitive.mono fun _ h => by omega)
  filter_upwards [eventually_finite_region a k ha hk, hprimitive] with i hi hp
  exact H (a i) (k i) hp.1 hi hp.2

theorem existing_limit_lower (G : Geometry) (W : Weist G) [l.NeBot]
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0))
    (hprimitive : ∀ᶠ i in l, 2 ≤ k i ∧ (a i).Coprime (k i))
    (L : ℝ) (hL : Tendsto (fun i => Real.log (E G (a i) (k i))/(a i : ℝ)) l (𝓝 L)) :
    Real.log (256/27 : ℝ) ≤ L :=
  (central_lower_limit a k G W ha hk hprimitive).le_of_tendsto hL

theorem existing_limit_positive (G : Geometry) (W : Weist G) [l.NeBot]
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0))
    (hprimitive : ∀ᶠ i in l, 2 ≤ k i ∧ (a i).Coprime (k i))
    (L : ℝ) (hL : Tendsto (fun i => Real.log (E G (a i) (k i))/(a i : ℝ)) l (𝓝 L)) :
    0 < L :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 256/27)).trans_le
    (existing_limit_lower a k G W ha hk hprimitive L hL)

end KroneckerScopedWeistCentralLowerLimit
end
end
end

section

/-! Weist, Localization in quiver moduli spaces, Theorem 6.6, p.413.
Only the exact published finite formula is an input. The actual geometry
comparison remains explicit; limits and substitutions below are internal. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedPublishedAdjacent
open Filter KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerAllMPublishedDatum KroneckerAdjacentFormulaValue
open KroneckerScopedWeistCentralLowerLimit
open scoped Topology

structure Formula (G : Geometry) : Prop where
  finite : ∀ m a : ℕ, 3 ≤ m → 0 < a →
    (G.euler (datum m a (a+1)) : ℝ) =
      (m : ℝ)/(((a : ℝ)+1)*(((m-1 : ℕ) : ℝ)*a+m))*
        ((((m-1)^2*a+(m-1)*m).choose a : ℕ) : ℝ)

theorem adjacent_formula (G : Geometry) (F : Formula G) (m a : ℕ) (hm : 3 ≤ m) (ha : 0 < a) :
    (KroneckerManuscriptTarget.euler (family G) m a (a+1) : ℝ) = adjacentValue m a := by
  rw [euler_comparison, F.finite m a hm ha]
  rfl

theorem adjacent_positive (G : Geometry) (F : Formula G) (m a : ℕ) (hm : 3 ≤ m) (ha : 0 < a) :
    0 < KroneckerManuscriptTarget.euler (family G) m a (a+1) := by
  have h := adjacent_value_pos m a hm
  rw [← adjacent_formula G F m a hm ha] at h
  exact_mod_cast h

theorem adjacent_limit (G : Geometry) (F : Formula G) (m : ℕ) (hm : 3 ≤ m) :
    Tendsto (fun a : ℕ => Real.log
      (KroneckerManuscriptTarget.euler (family G) m a (a+1) : ℝ)/(a : ℝ))
      atTop (𝓝 (centralValue m)) := by
  apply (KroneckerAdjacentLogLimit.adjacent_log_limit m hm).congr'
  filter_upwards [eventually_gt_atTop 0] with a ha
  simp only [adjacent_formula G F m a hm ha]

theorem central_euler_eq (G : Geometry) (a k : ℕ) :
    E G a k = (KroneckerManuscriptTarget.euler (family G) 3 a (a+k) : ℝ) := rfl

theorem three_adjacent_limit {α : Type*} {l : Filter α} (G : Geometry) (F : Formula G)
    (a : α → ℕ) (ha : Tendsto (fun i => (a i : ℝ)) l atTop) :
    Tendsto (fun i => Real.log (E G (a i) 1)/(a i : ℝ)) l
      (𝓝 (Real.log (256/27 : ℝ))) := by
  have hnat : Tendsto a l atTop := tendsto_natCast_atTop_iff.mp ha
  have h := (adjacent_limit G F 3 (by decide)).comp hnat
  rw [KroneckerCentralValueThree.central_value_three] at h
  exact h

theorem three_adjacent_root {α : Type*} {l : Filter α} (G : Geometry) (F : Formula G)
    (a : α → ℕ) (ha : Tendsto (fun i => (a i : ℝ)) l atTop) :
    Tendsto (fun i => (E G (a i) 1)^(1/(a i : ℝ))) l (𝓝 (256/27 : ℝ)) := by
  apply (KroneckerEntropyRootTransfer.entropy_iff_root (by norm_num : (0:ℝ)<256/27)
    ?_).mp (three_adjacent_limit G F a ha)
  filter_upwards [KroneckerLowerEntropyKernel.eventually_positive a ha] with i hi
  rw [central_euler_eq]
  exact_mod_cast adjacent_positive G F 3 (a i) (by decide) hi

end KroneckerScopedPublishedAdjacent
end
end

