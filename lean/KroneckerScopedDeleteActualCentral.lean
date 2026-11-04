import KroneckerScopedActualFrameApplication
import KroneckerActualFrameApplication
import KroneckerDeleteBinaryCount
import KroneckerScopedPublishedAdjacent

section

/-! The literal primitive frame is binary throughout the central region. -/
set_option autoImplicit false
namespace KroneckerDeleteFrameAlphabet
open KroneckerFrameSlope KroneckerFrameWord KroneckerFrameBadDensity
open KroneckerDeleteBinaryProgram

theorem central_slope_lower (a r d : ℕ) (ha : 0<a) (hr : 1≤r) (hd : 0<d) :
    1 ≤ frameSlope a (a+r) d := by
  have ha' : (0:ℝ)<a := by exact_mod_cast ha
  have hr' : (1:ℝ)≤r := by exact_mod_cast hr
  have hd' : (1:ℝ)≤d := by exact_mod_cast hd
  have hi : 1/(d:ℝ) ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num) hd'
  have h := frameSlope_mul a (a+r) d ha hd
  push_cast at h
  nlinarith

theorem central_slope_upper (a r d : ℕ) (ha : 0<a) (hr : r≤a) :
    frameSlope a (a+r) d ≤ 2 := by
  apply (frameSlope_le_ratio a (a+r) d).trans
  have ha' : (0:ℝ)<a := by exact_mod_cast ha
  apply (div_le_iff₀ ha').mpr
  exact_mod_cast (show a+r≤2*a by omega)

theorem central_frame_binary (a r d : ℕ) (ha : 0<a) (hr : 1≤r) (hra : r≤a) (hd : 0<d) :
    ∀ t∈frameWord a (a+r) d,t=1 ∨ t=2 := by
  intro t ht
  have h := frameWord_legal a (a+r) d 2
    (central_slope_lower a r d ha hr hd) (central_slope_upper a r d ha hra) t ht
  omega

theorem central_frame_deletions (a r d : ℕ) (ha : 0<a) (hr : 1≤r) (hra : r≤a) (hd : 0<d) :
    (frameWord a (a+r) d).count 2=r-1 := by
  rw [binary_deletions _ (central_frame_binary a r d ha hr hra hd),
    frameWord_sum a (a+r) d ha (by omega) hd,frameWord_length]
  omega

theorem central_frame_target (a r : ℕ) (hr : 1≤r) :
    (a+1)+2+8*(r-1)=a+8*r-6+1 := by omega

end KroneckerDeleteFrameAlphabet
end

section

/-! The all-one target is literally the adjacent canonical frame. -/
set_option autoImplicit false
namespace KroneckerDeleteAdjacentFrame
open KroneckerFrameBadDensity KroneckerFrameWord KroneckerDeleteFrameAlphabet

theorem binary_all_ones (rs : List ℕ) (hr : ∀ r∈rs,r=1 ∨ r=2) (hD : rs.count 2=0) :
    rs=List.replicate rs.length 1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have ht : ∀ t∈rs,t=1 ∨ t=2 := fun t ht => hr t (by simp [ht])
    rcases hr r (by simp) with rfl | rfl
    · have hz : rs.count 2=0 := by simpa using hD
      simpa [List.replicate_succ] using congrArg (List.cons 1) (ih ht hz)
    · simp at hD

theorem adjacent_frame (a d : ℕ) (ha : 0<a) (hd : 0<d) :
    frameWord a (a+1) d=List.replicate (a+1) 1 := by
  have h := binary_all_ones _ (central_frame_binary a 1 d ha (by omega) (by omega) hd)
    (by simpa using central_frame_deletions a 1 d ha (by omega) (by omega) hd)
  simpa only [frameWord_length] using h

end KroneckerDeleteAdjacentFrame
end

section

/-! Identify the all-one output count with the ordinary adjacent Euler invariant. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedDeleteAdjacentEuler
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler KroneckerManuscriptTarget
open KroneckerFrameIdentity KroneckerScopedActualFrameApplication KroneckerWordCounts
open KroneckerFrameBadDensity KroneckerDeleteAdjacentFrame

theorem all_one_euler (G : Geometry) (A : Application G) (a : ℕ) (ha : 2≤a) :
    (runCount 3 (List.replicate (a+1) 1) 0 : ℝ)=
      3*(euler (family G) 3 a (a+1) : ℝ) := by
  have hc : a.Coprime (a+1) := by simp
  obtain ⟨p,hm,hpa,hpb,_⟩ := parameters_exist 3 a (a+1) (by decide) ha (by omega) hc
  have hd : 0<p.d₁ := by have := p.hd₁; omega
  have hi := literal_identity G A p
  rw [hm,hpa,hpb,adjacent_frame a p.d₁ (by omega) hd] at hi
  exact_mod_cast hi

end KroneckerScopedDeleteAdjacentEuler
end
end

section

/- Original module: KroneckerWeistApplication -/
section
/-! Application of the GENERAL published inputs. The full compatible-class
finsum is reduced to the actual finite stable index by proving omitted spaces
empty. Both Euler transport and positivity are then derived, not assumed in a
new family-specific wrapper. The external Geometry input remains explicit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistApplication
open KroneckerPublishedModuli KroneckerWeistApplicationGates
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
  localizationTerm G (base a b) (representativeSection a b q)

/-- A compatible class omitted from SourceIndex has EMPTY moduli. This uses
actual stable representations, not a presumed sign or a presumed Euler zero. -/
theorem omitted_empty (G : Geometry) (a b : ℕ) (ha : 0<a) (q : WordClass)
    (hn : ¬Active a b q)
    (hc : Compatible (base a b) (representativeSection a b q)) :
    IsEmpty (G.space (coverDatum (base a b) (representativeSection a b q))) := by
  apply not_nonempty_iff.mp
  intro h
  let d := representativeSection a b q
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
  apply ite_eq_left
  exact (compatible_dictionary a b _).mpr (representative_spec a b q).2.1

theorem finite_localization (G : Geometry) (W : Weist G) (a b : ℕ) (ha : 0<a)
    [Fintype (SourceIndex a b)] :
    G.euler (base a b)=∑ q : SourceIndex a b,
      G.euler (coverDatum (base a b) (representative a b q).1) := by
  have hW := W.localization (base a b) (base_acyclic a b) (base_connected a b) (base_nonzero a b ha)
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

end KroneckerWeistApplication
end
end

/- Original module: KroneckerWeistCountedLower -/
section
/-! Complete finite counted-family deduction, relative to the general explicit
analytic geometry input and Weist's general source statements. The manuscript
coprimality is gcd(a,n+2)=1, and is not dropped from the conclusion. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistCountedLower
open KroneckerPublishedModuli KroneckerWeistApplication
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

end KroneckerWeistCountedLower
end
end

/- Original module: KroneckerWeistFiniteLower -/
section
/-! The exact finite estimate displayed in the manuscript, with uniform
C0,q in (0,1]. Analytic Geometry and the general published Weist statements
remain visible. No entropy limit existence is assumed or concluded here. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistFiniteLower
open KroneckerPublishedModuli KroneckerOrdinarySingularEuler
open KroneckerWeistApplication KroneckerWeistUniformConstants

theorem finite_lower (G : Geometry) (W : Weist G) :
    ∃ C q : ℝ, 0 < C ∧ C ≤ 1 ∧ 0 < q ∧ q ≤ 1 ∧
      ∀ a k : ℕ, 2 ≤ k → 100000*k ≤ a → a.Coprime k →
        C * (256/27 : ℝ)^a * ((k : ℝ)/a)^(5/2 : ℝ) * q^(k-1) ≤
          (ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+k))
            (baseAdmissible G a (a+k)) : ℝ) := by
  obtain ⟨A, B, hA, hB, H⟩ := KroneckerWeistCountedLower.uniform_lower G W
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

end KroneckerWeistFiniteLower
end
end

/- Original module: KroneckerWeistCentralLowerLimit -/
section
/-! The manuscript's central joint lower-limit consequence for actual ordinary
Euler characteristics, retaining the explicit Geometry and general Weist inputs.
The theorem neither assumes nor supplies existence of the entropy limit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistCentralLowerLimit
open Filter KroneckerPublishedModuli KroneckerOrdinarySingularEuler
open KroneckerWeistApplication KroneckerLowerEntropyKernel KroneckerLowerEntropyTransfer
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
  exact_mod_cast KroneckerWeistFiniteLower.euler_positive_in_finite_region
    G W (a i) (k i) hp.1 hi hp.2

theorem central_lower_limit (G : Geometry) (W : Weist G)
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0))
    (hprimitive : ∀ᶠ i in l, 2 ≤ k i ∧ (a i).Coprime (k i)) :
    LowerLimit l (fun i => Real.log (E G (a i) (k i))/(a i : ℝ))
      (Real.log (256/27 : ℝ)) := by
  obtain ⟨C, q, hC, _, hq, _, H⟩ := KroneckerWeistFiniteLower.finite_lower G W
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

end KroneckerWeistCentralLowerLimit
end
end
end

section

/- Original module: KroneckerDeleteAdjacentEuler -/
section
/-! Identify the all-one output count with the ordinary adjacent Euler invariant. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDeleteAdjacentEuler
open KroneckerPublishedModuli KroneckerCanonicalPublishedEuler KroneckerManuscriptTarget
open KroneckerFrameIdentity KroneckerActualFrameApplication KroneckerWordCounts
open KroneckerFrameBadDensity KroneckerDeleteAdjacentFrame

theorem all_one_euler (G : Geometry) (A : Application G) (a : ℕ) (ha : 2≤a) :
    (runCount 3 (List.replicate (a+1) 1) 0 : ℝ)=
      3*(euler (family G) 3 a (a+1) : ℝ) := by
  have hc : a.Coprime (a+1) := by simp
  obtain ⟨p,hm,hpa,hpb,_⟩ := parameters_exist 3 a (a+1) (by decide) ha (by omega) hc
  have hd : 0<p.d₁ := by have := p.hd₁; omega
  have hi := literal_identity G A p
  rw [hm,hpa,hpb,adjacent_frame a p.d₁ (by omega) hd] at hi
  exact_mod_cast hi

end KroneckerDeleteAdjacentEuler
end
end

/- Original module: KroneckerDeleteFrameCount -/
section
/-! Concrete finite comparison for the canonical central frame. -/
set_option autoImplicit false
namespace KroneckerDeleteFrameCount
open KroneckerWordCounts KroneckerFrameBadDensity KroneckerFrameWord
open KroneckerDeleteFrameAlphabet KroneckerDeleteBinaryCount

theorem central_frame_count (a r d : ℕ) (ha : 0<a) (hr : 1≤r) (hra : r≤a) (hd : 0<d) :
    runCount 3 (frameWord a (a+r) d) 0 ≤ (a+r).choose (r-1)*64^(r-1) *
      runCount 3 (List.replicate (a+8*r-6+1) 1) 0 := by
  have h := binary_count (frameWord a (a+r) d) (central_frame_binary a r d ha hr hra hd)
  rw [central_frame_deletions a r d ha hr hra hd,frameWord_length,
    central_frame_target a r hr] at h
  have he : a+1+(r-1)=a+r := by omega
  simpa only [he] using h

theorem central_frame_count_real (a r d : ℕ) (ha : 0<a) (hr : 1≤r) (hra : r≤a) (hd : 0<d) :
    (runCount 3 (frameWord a (a+r) d) 0 : ℝ) ≤ ((a+r).choose (r-1):ℝ)*64^(r-1) *
      (runCount 3 (List.replicate (a+8*r-6+1) 1) 0 : ℝ) := by
  exact_mod_cast central_frame_count a r d ha hr hra hd

end KroneckerDeleteFrameCount
end

/- Original module: KroneckerDeleteActualFinite -/
section
/-! Apply the constructed comparison to actual Euler values through the finite-frame identity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDeleteActualFinite
open KroneckerPublishedModuli KroneckerCanonicalPublishedEuler KroneckerManuscriptTarget
open KroneckerFrameIdentity KroneckerActualFrameApplication KroneckerWordCounts
open KroneckerFrameBadDensity KroneckerDeleteFrameCount KroneckerDeleteAdjacentEuler
open KroneckerDeleteFrameAlphabet KroneckerWeistCentralLowerLimit

theorem finite_comparison (G : Geometry) (A : Application G) (a r : ℕ)
    (ha : 2≤a) (hr : 1≤r) (hra : r≤a) (hc : a.Coprime r) :
    E G a r ≤ ((a+r).choose (r-1):ℝ)*64^(r-1)*E G (a+8*r-6) 1 := by
  have hab : a.Coprime (a+r) := by simpa using hc
  obtain ⟨p,hm,hpa,hpb,_⟩ := parameters_exist 3 a (a+r) (by decide) ha (by omega) hab
  have hd : 0<p.d₁ := by have := p.hd₁; omega
  have hi : (runCount 3 (frameWord a (a+r) p.d₁) 0:ℝ)=3*E G a r := by
    have h := literal_identity G A p
    rw [hm,hpa,hpb] at h
    dsimp [E]
    exact_mod_cast h
  have h := central_frame_count_real a r p.d₁ (by omega) hr hra hd
  rw [hi,all_one_euler G A (a+8*r-6) (by omega)] at h
  change 3*E G a r ≤ _*(3*E G (a+8*r-6) 1) at h
  nlinarith

theorem central_positive (G : Geometry) (A : Application G) (a r : ℕ)
    (ha : 2≤a) (hr : 1≤r) (hra : r≤a) (hc : a.Coprime r) : 0<E G a r := by
  have hab : a.Coprime (a+r) := by simpa using hc
  obtain ⟨p,hm,hpa,hpb,_⟩ := parameters_exist 3 a (a+r) (by decide) ha (by omega) hab
  have hd : 0<p.d₁ := by have := p.hd₁; omega
  have h := euler_positive_of_legal G A p (by
    rw [hm,hpa,hpb]
    intro t ht
    have hb := central_frame_binary a r p.d₁ (by omega) hr hra hd t ht
    omega)
  rw [hm,hpa,hpb] at h
  dsimp [E]
  exact_mod_cast h

end KroneckerDeleteActualFinite
end
end

/- Original module: KroneckerDeleteAdjacentUpper -/
section
/-! An elementary exponential envelope for the exact adjacent formula. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDeleteAdjacentUpper
open KroneckerBinomialTermBound KroneckerAdjacentFormulaValue KroneckerAdjacentParameters

theorem adjacent_binomial_upper (a : ℕ) :
    ((4*a+6).choose a:ℝ) ≤ (4096/729:ℝ)*(256/27:ℝ)^a := by
  have h := binomial_term_bound (4*a+6) a (by omega) (1/3) (by norm_num)
  have he : (4096/729:ℝ)*(256/27:ℝ)^a*(1/3:ℝ)^a=(1+1/3:ℝ)^(4*a+6) := by
    rw [mul_assoc,← mul_pow,pow_add,pow_mul]
    norm_num
    ring
  rw [← he] at h
  exact (mul_le_mul_iff_left₀ (by positivity : (0:ℝ)<(1/3:ℝ)^a)).mp h

theorem adjacent_prefactor_le_one (a : ℕ) :
    (3:ℝ)/(((a:ℝ)+1)*(2*a+3)) ≤ 1 := by
  apply (div_le_one (by positivity)).mpr
  have h : (0:ℝ)≤a := Nat.cast_nonneg a
  nlinarith

theorem adjacent_upper (a : ℕ) :
    adjacentValue 3 a ≤ (4096/729:ℝ)*(256/27:ℝ)^a := by
  have hc : (0:ℝ)≤((4*a+6).choose a:ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_right (adjacent_prefactor_le_one a) hc
  norm_num [adjacentValue,binomialSlope,binomialOffset] at *
  exact h.trans (adjacent_binomial_upper a)

end KroneckerDeleteAdjacentUpper
end
end

/- Original module: KroneckerPublishedAdjacent -/
section
/-! Weist, Localization in quiver moduli spaces, Theorem 6.6, p.413.
Only the exact published finite formula is an input. The actual geometry
comparison remains explicit; limits and substitutions below are internal. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPublishedAdjacent
open Filter KroneckerPublishedModuli KroneckerCanonicalPublishedEuler
open KroneckerAllMPublishedDatum KroneckerAdjacentFormulaValue
open KroneckerWeistCentralLowerLimit
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

end KroneckerPublishedAdjacent
end
end

/- Original module: KroneckerDeleteActualUpper -/
section
/-! The selected finite Euler bound, with no DT/IH or global framing dictionary. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDeleteActualUpper
open KroneckerPublishedModuli KroneckerCanonicalPublishedEuler KroneckerManuscriptTarget
open KroneckerActualFrameApplication KroneckerPublishedAdjacent KroneckerWeistCentralLowerLimit
open KroneckerDeleteActualFinite KroneckerDeleteAdjacentUpper

def bound (a r : ℕ) : ℝ :=
  (4096/729:ℝ)*((a+r).choose (r-1):ℝ)*64^(r-1)*(256/27:ℝ)^(a+8*r-6)

theorem bound_positive (a r : ℕ) : 0<bound a r := by
  have h : 0<((a+r).choose (r-1):ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : r-1≤a+r)
  unfold bound
  positivity

theorem actual_adjacent_upper (G : Geometry) (F : Formula G) (a : ℕ) (ha : 0<a) :
    E G a 1 ≤ (4096/729:ℝ)*(256/27:ℝ)^a := by
  rw [central_euler_eq,adjacent_formula G F 3 a (by decide) ha]
  exact adjacent_upper a

theorem finite_upper (G : Geometry) (A : Application G) (F : Formula G) (a r : ℕ)
    (ha : 2≤a) (hr : 1≤r) (hra : r≤a) (hc : a.Coprime r) : E G a r ≤ bound a r := by
  have h := finite_comparison G A a r ha hr hra hc
  have ht := actual_adjacent_upper G F (a+8*r-6) (by omega)
  have hh := mul_le_mul_of_nonneg_left ht
    (by positivity : (0:ℝ)≤((a+r).choose (r-1):ℝ)*64^(r-1))
  apply h.trans
  convert hh using 1 <;> unfold bound <;> ring

end KroneckerDeleteActualUpper
end
end

/- Original module: KroneckerDeleteFiberFilter -/
section
/-! Sublinear recovery cost along arbitrary filters, including the joint-limit filter. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDeleteFiberFilter
open Filter KroneckerFiberBudget KroneckerNormalizedFiberBound
open KroneckerFiberEnvelopeLimit KroneckerSmallLogParameter KroneckerLowerEntropyKernel
open scoped Topology

variable {α : Type*} {l : Filter α}

theorem envelope_tendsto (m : ℕ) (t : ℝ) (x : α→ℝ) (hx : Tendsto x l (𝓝 0)) :
    Tendsto (fun i => fiberEnvelope m t (x i)) l (𝓝 (Real.log (1+t))) := by
  have h := ((hx.const_add 1).mul_const (Real.log (1+t))).add
    (hx.mul_const (2*(m:ℝ)*Real.log 2-Real.log t))
  simpa only [fiberEnvelope,add_zero,zero_mul,one_mul] using h

theorem normalized_tendsto (m : ℕ) (n D : α→ℕ)
    (hn : Tendsto (fun i => (n i:ℝ)) l atTop)
    (hD : Tendsto (fun i => (D i:ℝ)/(n i:ℝ)) l (𝓝 0)) :
    Tendsto (fun i => normalizedFiberLog m (n i) (D i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨t,ht,hlog⟩ := exists_small_log_parameter ε hε
  have hs := (envelope_tendsto m t _ hD).eventually (gt_mem_nhds (by linarith : Real.log (1+t)<ε))
  filter_upwards [eventually_positive n hn,hs] with i hni hi
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (normalizedFiberLog_nonneg m (n i) (D i))]
  exact (normalizedFiberLog_bound m (n i) (D i) hni t ht).trans_lt hi

theorem successor_ratio (a : α→ℕ) (ha : Tendsto (fun i => (a i:ℝ)) l atTop) :
    Tendsto (fun i => ((a i+1:ℕ):ℝ)/(a i:ℝ)) l (𝓝 1) := by
  have h := (constant_over_height a ha 1).const_add 1
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_positive a ha] with i hi
  have hne : (a i:ℝ)≠0 := by exact_mod_cast hi.ne'
  push_cast
  field_simp

theorem deletion_density (a r : α→ℕ)
    (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0)) :
    Tendsto (fun i => ((r i-1:ℕ):ℝ)/((a i+1:ℕ):ℝ)) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun i => by positivity)) ?_ hr
  filter_upwards [eventually_positive a ha] with i hi
  have hap : (0:ℝ)<a i := by exact_mod_cast hi
  gcongr
  · exact_mod_cast Nat.sub_le (r i) 1
  · exact_mod_cast Nat.le_succ (a i)

theorem recovery_cost (m : ℕ) (a r : α→ℕ)
    (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0)) :
    Tendsto (fun i => Real.log (fiberBudget m (a i+1) (r i-1):ℝ)/(a i:ℝ)) l (𝓝 0) := by
  have hn : Tendsto (fun i => ((a i+1:ℕ):ℝ)) l atTop := by
    exact tendsto_atTop_mono (fun i => by exact_mod_cast Nat.le_succ (a i)) ha
  have h := (normalized_tendsto m (fun i => a i+1) (fun i => r i-1)
    hn (deletion_density a r ha hr)).mul (successor_ratio a ha)
  simp only [zero_mul] at h
  apply h.congr'
  exact Eventually.of_forall fun i => by
    have hnz : ((a i+1:ℕ):ℝ)≠0 := by positivity
    unfold normalizedFiberLog
    field_simp

end KroneckerDeleteFiberFilter
end
end

/- Original module: KroneckerDeleteUpperLimit -/
section
/-! The complete logarithmic error of the deletion bound vanishes jointly. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDeleteUpperLimit
open Filter KroneckerFiberBudget KroneckerDeleteBinaryCount KroneckerDeleteActualUpper
open KroneckerDeleteFiberFilter KroneckerLowerEntropyKernel KroneckerUpperEntropyKernel
open scoped Topology

theorem bound_as_fiber (a r : ℕ) (hr : 1≤r) :
    bound a r=(4096/729:ℝ)*(fiberBudget 3 (a+1) (r-1):ℝ)*(256/27:ℝ)^(a+8*r-6) := by
  rw [fiberBudget_three]
  have he : a+1+(r-1)=a+r := by omega
  simp only [bound,he,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem log_bound (a r : ℕ) (hr : 1≤r) :
    Real.log (bound a r)/(a:ℝ)=Real.log (4096/729:ℝ)/(a:ℝ)+
      Real.log (fiberBudget 3 (a+1) (r-1):ℝ)/(a:ℝ)+
      ((a+8*r-6:ℕ):ℝ)/(a:ℝ)*Real.log (256/27:ℝ) := by
  have hb : (0:ℝ)<(fiberBudget 3 (a+1) (r-1):ℝ) := by
    exact_mod_cast fiberBudget_positive 3 (a+1) (r-1)
  rw [bound_as_fiber a r hr,Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) hb.ne',Real.log_pow]
  ring

variable {α : Type*} {l : Filter α} (a r : α→ℕ)

theorem target_height_ratio (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0))
    (hp : ∀ᶠ i in l,1≤r i) :
    Tendsto (fun i => ((a i+8*r i-6:ℕ):ℝ)/(a i:ℝ)) l (𝓝 1) := by
  have h := ((hr.const_mul 8).const_add 1).sub (constant_over_height a ha 6)
  simp only [mul_zero,add_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_positive a ha,hp] with i hai hri
  have hne : (a i:ℝ)≠0 := by exact_mod_cast hai.ne'
  rw [Nat.cast_sub (by omega : 6≤a i+8*r i)]
  push_cast
  field_simp <;> ring

theorem bound_entropy_limit (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0))
    (hp : ∀ᶠ i in l,1≤r i) :
    Tendsto (fun i => Real.log (bound (a i) (r i))/(a i:ℝ)) l (𝓝 (Real.log (256/27:ℝ))) := by
  have h := ((constant_over_height a ha (Real.log (4096/729:ℝ))).add
    (recovery_cost 3 a r ha hr)).add ((target_height_ratio a r ha hr hp).mul_const (Real.log (256/27:ℝ)))
  simp only [zero_add,one_mul] at h
  apply h.congr'
  exact hp.mono fun i hi => (log_bound (a i) (r i) hi).symm

theorem upper_limit (E : α→ℝ) (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0))
    (hp : ∀ᶠ i in l,1≤r i) (hE : ∀ᶠ i in l,0<E i)
    (hbound : ∀ᶠ i in l,E i≤bound (a i) (r i)) :
    UpperLimit l (fun i => Real.log (E i)/(a i:ℝ)) (Real.log (256/27:ℝ)) := by
  intro c hc
  have h := (bound_entropy_limit a r ha hr hp).eventually (gt_mem_nhds hc)
  filter_upwards [h,hE,hbound] with i hi hEi hbi
  exact (div_le_div_of_nonneg_right (Real.log_le_log hEi hbi) (Nat.cast_nonneg _)).trans hi.le

end KroneckerDeleteUpperLimit
end
end

/- Original module: KroneckerScopedDeleteActualFinite -/
section
/-! Apply the constructed comparison to actual Euler values through the finite-frame identity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedDeleteActualFinite
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler KroneckerManuscriptTarget
open KroneckerFrameIdentity KroneckerScopedActualFrameApplication KroneckerWordCounts
open KroneckerFrameBadDensity KroneckerDeleteFrameCount KroneckerScopedDeleteAdjacentEuler
open KroneckerDeleteFrameAlphabet KroneckerScopedWeistCentralLowerLimit

theorem finite_comparison (G : Geometry) (A : Application G) (a r : ℕ)
    (ha : 2≤a) (hr : 1≤r) (hra : r≤a) (hc : a.Coprime r) :
    E G a r ≤ ((a+r).choose (r-1):ℝ)*64^(r-1)*E G (a+8*r-6) 1 := by
  have hab : a.Coprime (a+r) := by simpa using hc
  obtain ⟨p,hm,hpa,hpb,_⟩ := parameters_exist 3 a (a+r) (by decide) ha (by omega) hab
  have hd : 0<p.d₁ := by have := p.hd₁; omega
  have hi : (runCount 3 (frameWord a (a+r) p.d₁) 0:ℝ)=3*E G a r := by
    have h := literal_identity G A p
    rw [hm,hpa,hpb] at h
    dsimp [E]
    exact_mod_cast h
  have h := central_frame_count_real a r p.d₁ (by omega) hr hra hd
  rw [hi,all_one_euler G A (a+8*r-6) (by omega)] at h
  change 3*E G a r ≤ _*(3*E G (a+8*r-6) 1) at h
  nlinarith

theorem central_positive (G : Geometry) (A : Application G) (a r : ℕ)
    (ha : 2≤a) (hr : 1≤r) (hra : r≤a) (hc : a.Coprime r) : 0<E G a r := by
  have hab : a.Coprime (a+r) := by simpa using hc
  obtain ⟨p,hm,hpa,hpb,_⟩ := parameters_exist 3 a (a+r) (by decide) ha (by omega) hab
  have hd : 0<p.d₁ := by have := p.hd₁; omega
  have h := euler_positive_of_legal G A p (by
    rw [hm,hpa,hpb]
    intro t ht
    have hb := central_frame_binary a r p.d₁ (by omega) hr hra hd t ht
    omega)
  rw [hm,hpa,hpb] at h
  dsimp [E]
  exact_mod_cast h

end KroneckerScopedDeleteActualFinite
end
end

/- Original module: KroneckerScopedDeleteActualUpper -/
section
/-! The selected finite Euler bound, with no DT/IH or global framing dictionary. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedDeleteActualUpper
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler KroneckerManuscriptTarget
open KroneckerScopedActualFrameApplication KroneckerScopedPublishedAdjacent KroneckerScopedWeistCentralLowerLimit
open KroneckerScopedDeleteActualFinite KroneckerDeleteAdjacentUpper

export KroneckerDeleteActualUpper (bound bound_positive)

theorem actual_adjacent_upper (G : Geometry) (F : Formula G) (a : ℕ) (ha : 0<a) :
    E G a 1 ≤ (4096/729:ℝ)*(256/27:ℝ)^a := by
  rw [central_euler_eq,adjacent_formula G F 3 a (by decide) ha]
  exact adjacent_upper a

theorem finite_upper (G : Geometry) (A : Application G) (F : Formula G) (a r : ℕ)
    (ha : 2≤a) (hr : 1≤r) (hra : r≤a) (hc : a.Coprime r) : E G a r ≤ bound a r := by
  have h := finite_comparison G A a r ha hr hra hc
  have ht := actual_adjacent_upper G F (a+8*r-6) (by omega)
  have hh := mul_le_mul_of_nonneg_left ht
    (by positivity : (0:ℝ)≤((a+r).choose (r-1):ℝ)*64^(r-1))
  apply h.trans
  convert hh using 1 <;> unfold bound <;> ring

end KroneckerScopedDeleteActualUpper
end
end

/- Original module: KroneckerScopedDeleteActualCentral -/
section
/-! Actual central upper and two-sided entropy limits from the deletion map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedDeleteActualCentral
open Filter KroneckerScopedModuli KroneckerScopedActualFrameApplication
open KroneckerScopedPublishedAdjacent KroneckerScopedWeistCentralLowerLimit
open KroneckerUpperEntropyKernel KroneckerScopedDeleteActualFinite KroneckerScopedDeleteActualUpper
open scoped Topology
variable {α : Type*} {l : Filter α} (a r : α→ℕ)

theorem eventually_region (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0)) :
    ∀ᶠ i in l,2≤a i ∧ r i≤a i := by
  filter_upwards [ha.eventually_ge_atTop 2,KroneckerLowerEntropyKernel.eventually_le a r ha hr]
    with i hai hri
  exact ⟨by exact_mod_cast hai,hri⟩

theorem eventually_positive (G : Geometry) (A : Application G)
    (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0))
    (hp : ∀ᶠ i in l,0<r i ∧ (a i).Coprime (r i)) :
    ∀ᶠ i in l,0<E G (a i) (r i) := by
  filter_upwards [eventually_region a r ha hr,hp] with i hi hpi
  exact central_positive G A (a i) (r i) hi.1 hpi.1 hi.2 hpi.2

theorem central_upper (G : Geometry) (A : Application G) (F : Formula G)
    (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0))
    (hp : ∀ᶠ i in l,0<r i ∧ (a i).Coprime (r i)) :
    UpperLimit l (fun i => Real.log (E G (a i) (r i))/(a i:ℝ)) (Real.log (256/27:ℝ)) := by
  apply KroneckerDeleteUpperLimit.upper_limit a r _ ha hr (hp.mono fun i hi => hi.1)
    (eventually_positive a r G A ha hr hp)
  filter_upwards [eventually_region a r ha hr,hp] with i hi hpi
  exact finite_upper G A F (a i) (r i) hi.1 hpi.1 hi.2 hpi.2

theorem central_limit (G : Geometry) (A : Application G) (F : Formula G) (W : Weist G)
    (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0))
    (hp : ∀ᶠ i in l,2≤r i ∧ (a i).Coprime (r i)) :
    Tendsto (fun i => Real.log (E G (a i) (r i))/(a i:ℝ)) l (𝓝 (Real.log (256/27:ℝ))) :=
  tendsto_of_bounds (central_lower_limit a r G W ha hr hp)
    (central_upper a r G A F ha hr (hp.mono fun i hi => ⟨by omega,hi.2⟩))

end KroneckerScopedDeleteActualCentral
end
end
end

