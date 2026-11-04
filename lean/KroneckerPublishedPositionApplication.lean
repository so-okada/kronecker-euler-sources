import KroneckerSourceParameterGates
import KroneckerSourceNaturalGradings

/- Original module: KroneckerSourcePrefixBounds -/
section
/-! Nonnegative source weights and finite-prefix edge counts. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourcePrefixBounds
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerSourceIntervalCounts
open scoped BigOperators

theorem horizontal_grade_nonnegative (e : Edge) : 0≤hGrade e := by cases e <;> simp [hGrade]

theorem vertical_grade_nonnegative (e : Edge) : 0≤vGrade e := by cases e <;> simp [vGrade]

theorem horizontal_weight_nonnegative (E : ℕ→Edge) (s t : ℕ) : 0≤hWeight E s t :=
  Finset.sum_nonneg fun i _ => horizontal_grade_nonnegative (E i)

theorem vertical_weight_nonnegative (E : ℕ→Edge) (s t : ℕ) : 0≤vWeight E s t :=
  Finset.sum_nonneg fun i _ => vertical_grade_nonnegative (E i)

theorem horizontal_weight_add (E : ℕ→Edge) (s u t : ℕ) (hsu : s≤u) (hut : u≤t) :
    hWeight E s u+hWeight E u t=hWeight E s t := interval_add hGrade E s u t hsu hut

theorem vertical_weight_add (E : ℕ→Edge) (s u t : ℕ) (hsu : s≤u) (hut : u≤t) :
    vWeight E s u+vWeight E u t=vWeight E s t := interval_add vGrade E s u t hsu hut

theorem horizontal_weight_mono (E : ℕ→Edge) (s u t : ℕ) (hsu : s≤u) (hut : u≤t) :
    hWeight E s u≤hWeight E s t := by
  have := horizontal_weight_add E s u t hsu hut
  have := horizontal_weight_nonnegative E u t
  omega

theorem vertical_weight_mono (E : ℕ→Edge) (s u t : ℕ) (hsu : s≤u) (hut : u≤t) :
    vWeight E s u≤vWeight E s t := by
  have := vertical_weight_add E s u t hsu hut
  have := vertical_weight_nonnegative E u t
  omega

theorem horizontal_grade_le_interval (E : ℕ→Edge) {s t i : ℕ} (hsi : s ≤ i) (hit : i < t) :
    hGrade (E i)≤hWeight E s t :=
  Finset.single_le_sum (fun j _ => horizontal_grade_nonnegative (E j)) (Finset.mem_Ico.mpr ⟨hsi,hit⟩)

theorem vertical_grade_le_interval (E : ℕ→Edge) {s t i : ℕ} (hsi : s ≤ i) (hit : i < t) :
    vGrade (E i)≤vWeight E s t :=
  Finset.single_le_sum (fun j _ => vertical_grade_nonnegative (E j)) (Finset.mem_Ico.mpr ⟨hsi,hit⟩)

theorem horizontal_zero_of_total (E : ℕ→Edge) {s t i : ℕ} (hsi : s ≤ i) (hit : i < t)
    (hz : hWeight E s t=0) : hGrade (E i)=0 := by
  have := horizontal_grade_le_interval E hsi hit
  have := horizontal_grade_nonnegative (E i)
  omega

theorem vertical_zero_of_total (E : ℕ→Edge) {s t i : ℕ} (hsi : s ≤ i) (hit : i < t)
    (hz : vWeight E s t=0) : vGrade (E i)=0 := by
  have := vertical_grade_le_interval E hsi hit
  have := vertical_grade_nonnegative (E i)
  omega

theorem trace_horizontal_prefix {m N n : ℕ} (shape : ℕ→Bool) (g : Coloring m N) (hn : n≤N) :
    KroneckerSourceIntervalCounts.hCount (trace shape g) 0 n=HEdges shape n := by
  rw [KroneckerSourceIntervalCounts.hCount,Nat.Ico_zero_eq_range,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_before shape g i (i.isLt.trans_le hn)]
  cases hs : shape i.val <;> simp [paint,hFlag]

theorem trace_vertical_prefix {m N n : ℕ} (shape : ℕ→Bool) (g : Coloring m N) (hn : n≤N) :
    KroneckerSourceIntervalCounts.vCount (trace shape g) 0 n=VEdges shape n := by
  rw [KroneckerSourceIntervalCounts.vCount,Nat.Ico_zero_eq_range,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_before shape g i (i.isLt.trans_le hn)]
  cases hs : shape i.val <;> simp [paint,vFlag]

end KroneckerSourcePrefixBounds
end
end

/- Original module: KroneckerSourceDominantShadow -/
section
/-! A literal maximum horizontal shadow controls positive vertical support.
Horizontal support is recovered separately from the exact nonnegative total. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceDominantShadow
open KroneckerStack KroneckerCompatibility KroneckerSourceIntervalCounts
open KroneckerSourceCompatibility KroneckerSourceHorizontalShadow KroneckerSourcePrefixBounds

/-- Inclusion of the source shadows of all supported horizontal edges.
The test edge is vertical, and every index lies in the actual finite period. -/
def Dominates (E : ℕ→Edge) (N u : ℕ) : Prop :=
  ∀w,w<N→PositiveH E w→∀j,j<N→Vertical E j→
    Shadow E w (lift N w j)→Shadow E u (lift N u j)

theorem positive_horizontal_is_horizontal {E : ℕ→Edge} {u : ℕ} (h : PositiveH E u) : Horizontal E u := by
  obtain ⟨g,_,hg⟩ := h
  exact ⟨g,hg⟩

theorem positive_vertical_is_vertical {E : ℕ→Edge} {v : ℕ} (h : PositiveV E v) : Vertical E v := by
  obtain ⟨g,_,hg⟩ := h
  exact ⟨g,hg⟩

theorem not_positive_horizontal_iff {E : ℕ→Edge} {u : ℕ} : ¬PositiveH E u ↔ hGrade (E u)=0 := by
  cases he : E u <;> simp [PositiveH,hGrade,he]

theorem not_positive_vertical_iff {E : ℕ→Edge} {v : ℕ} : ¬PositiveV E v ↔ vGrade (E v)=0 := by
  cases he : E v <;> simp [PositiveV,vGrade,he]

theorem zero_grade_iff (e : Edge) : e.grade=0 ↔ hGrade e=0 ∧ vGrade e=0 := by
  cases e <;> simp [Edge.grade,hGrade,vGrade]

theorem supported_vertical_in_dominant {E : ℕ→Edge} {N u : ℕ}
    (hs : Support E N) (hd : Dominates E N u) :
    ∀j,j<N→PositiveV E j→Shadow E u (lift N u j) := by
  intro j hj hjP
  obtain ⟨w,hw,hwP,hwj⟩ := hs j hj hjP
  exact hd w hw hwP j hj (positive_vertical_is_vertical hjP) hwj

theorem vertical_zero_after_first {E : ℕ→Edge} {N v j : ℕ}
    (hs : Support E N) (hd : Dominates E N 0) (hc : FirstClosure E 0 v)
    (hvj : v<j) (hj : j<N) : vGrade (E j)=0 := by
  apply not_positive_vertical_iff.mp
  intro hjP
  have hshadow := supported_vertical_in_dominant hs hd j hj hjP
  simp only [lift,Nat.zero_le,ite_true] at hshadow
  exact beyond_first_not_shadow hc hvj hshadow

theorem vertical_suffix_zero {E : ℕ→Edge} {N v : ℕ}
    (hs : Support E N) (hd : Dominates E N 0) (hc : FirstClosure E 0 v) :
    vWeight E (v+1) N=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hvj,hjN⟩ := Finset.mem_Ico.mp hj
  exact vertical_zero_after_first hs hd hc (by omega) hjN

theorem horizontal_suffix_zero {E : ℕ→Edge} {n N : ℕ} (hn : n≤N)
    (he : hWeight E 0 n=hWeight E 0 N) : hWeight E n N=0 := by
  have h := horizontal_weight_add E 0 n N (Nat.zero_le _) hn
  omega

theorem whole_grade_zero_outside {E : ℕ→Edge} {N v : ℕ}
    (hs : Support E N) (hd : Dominates E N 0) (hc : FirstClosure E 0 v)
    (hvN : v+1≤N) (he : hWeight E 0 (v+1)=hWeight E 0 N) :
    ∀j,v+1≤j→j<N→(E j).grade=0 := by
  intro j hvj hjN
  apply (zero_grade_iff _).mpr
  exact ⟨horizontal_zero_of_total E hvj hjN (horizontal_suffix_zero hvN he),
    vertical_zero_after_first hs hd hc (by omega) hjN⟩

theorem vertical_prefix_total {E : ℕ→Edge} {N v : ℕ}
    (hs : Support E N) (hd : Dominates E N 0) (hc : FirstClosure E 0 v) (hvN : v+1≤N) :
    vWeight E 0 (v+1)=vWeight E 0 N := by
  have h := vertical_weight_add E 0 (v+1) N (Nat.zero_le _) hvN
  rw [vertical_suffix_zero hs hd hc,add_zero] at h
  exact h

theorem dominant_shadow_prefix {E : ℕ→Edge} {N v : ℕ}
    (hs : Support E N) (hd : Dominates E N 0) (hc : FirstClosure E 0 v) :
    ∀j,j<N→PositiveV E j→j≤v := by
  intro j hj hjP
  by_contra h
  have hzero := vertical_zero_after_first hs hd hc (by omega) hj
  exact not_positive_vertical_iff.mpr hzero hjP

end KroneckerSourceDominantShadow
end
end

/- Original module: KroneckerSourcePositionBridge -/
section
/-! The source's maximum shadow and coordinate constraints give the manuscript
position. Zero outside is proved from support and nonnegative total weights. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourcePositionBridge
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerWeights KroneckerDyck
open KroneckerFrameIdentity KroneckerTight KroneckerSourceGradingDictionary
open KroneckerSourceIntervalCounts KroneckerSourceCompatibility KroneckerSourceHorizontalShadow
open KroneckerSourcePrefixBounds KroneckerSourceDominantShadow KroneckerSourceParameterGates
open KroneckerSourceMaximalPath

/-- Literal data from the negative-determinant branch of source Lemmas
4.12–4.13 (including the maximum supported shadow selected in 4.12's proof).
There is no internal first-return or zero-outside field. -/
structure PositionedShadow (N d₁ d₂ a b : ℕ) (shape : ℕ→Bool) (E : ℕ→Edge) where
  u : ℕ
  v : ℕ
  hu : u<N
  hv : v<N
  supported : PositiveH E u
  first : FirstClosure E u (lift N u v)
  dominant : Dominates E N u
  low : 0≤sourceCoordinate d₁ d₂ shape u ∧ sourceCoordinate d₁ d₂ shape u<(Nat.gcd a b:ℤ)
  high : sourceCoordinate d₁ d₂ shape v=sourceCoordinate d₁ d₂ shape u+(d₁:ℤ)+d₂-Nat.gcd a b

abbrev Block (p : Parameters) (g : Coloring p.m (ambientLength p)) :=
  PositionedShadow (ambientLength p) p.d₁ p.d₂ p.a p.b (frameShape p) (trace (frameShape p) g)

theorem block_origin (p : Parameters) {g : Coloring p.m (ambientLength p)} (B : Block p g) : B.u=0 := by
  have hlo := B.low.2
  rw [source_coordinate,p.coprime.gcd_eq_one] at hlo
  have hz : coord p.d₁ p.d₂ B.u=0 := by omega
  exact zero_coordinate_origin (ambient_coprime p) (by simpa [ambientLength,frameLength,p.length_eq] using B.hu) hz

theorem block_end (p : Parameters) {g : Coloring p.m (ambientLength p)} (B : Block p g) : B.v=p.a+p.b := by
  have hhigh := B.high
  rw [source_coordinate,source_coordinate,block_origin p B,p.coprime.gcd_eq_one] at hhigh
  rw [show coord p.d₁ p.d₂ 0=0 by simp [coord]] at hhigh
  simp only [Nat.cast_zero,zero_add,Nat.cast_one] at hhigh
  have hc : coord p.d₁ p.d₂ B.v=p.d₁+p.d₂-1 := by
    have := (source_hypotheses p).2.2.1
    omega
  apply coordinate_injective (ambient_coprime p)
    (by simpa [ambientLength,frameLength,p.length_eq] using B.hv)
    (by have := p.hd₁; have := p.hd₂; omega)
  rw [hc,frame_last_coordinate (source_hypotheses p).2.2.1
    (source_hypotheses p).2.2.2.1 p.determinant]

theorem block_first (p : Parameters) {g : Coloring p.m (ambientLength p)} (B : Block p g) :
    FirstClosure (trace (frameShape p) g) 0 (p.a+p.b) := by
  have h := B.first
  simpa only [block_origin p B,block_end p B,lift,Nat.zero_le,ite_true] using h

theorem block_dominant (p : Parameters) {g : Coloring p.m (ambientLength p)} (B : Block p g) :
    Dominates (trace (frameShape p) g) (ambientLength p) 0 := by
  simpa only [block_origin p B] using B.dominant

theorem frame_prefix_counts (p : Parameters) (g : Coloring p.m (ambientLength p)) :
    KroneckerSourceIntervalCounts.hCount (trace (frameShape p) g) 0 (frameLength p)=(p.a:ℤ)+1 ∧
    KroneckerSourceIntervalCounts.vCount (trace (frameShape p) g) 0 (frameLength p)=(p.b:ℤ) := by
  rw [trace_horizontal_prefix _ _ (Nat.le_add_right _ _),trace_vertical_prefix _ _ (Nat.le_add_right _ _)]
  exact frame_edge_counts (source_hypotheses p).2.2.1 (source_hypotheses p).2.2.2.1 p.determinant

theorem prefix_horizontal_total (p : Parameters) {g : Coloring p.m (ambientLength p)} (B : Block p g) :
    hWeight (trace (frameShape p) g) 0 (frameLength p)=(p.b:ℤ) := by
  have h := (block_first p B).2.2.1
  change KroneckerSourceIntervalCounts.vCount (trace (frameShape p) g) 0 (frameLength p)=
    hWeight (trace (frameShape p) g) 0 (frameLength p) at h
  rw [(frame_prefix_counts p g).2] at h
  exact h.symm

theorem prefix_vertical_total (p : Parameters) {g : Coloring p.m (ambientLength p)}
    (ht : Tight (frameShape p) p.a p.b g) (B : Block p g) :
    vWeight (trace (frameShape p) g) 0 (frameLength p)=(p.a:ℤ) := by
  have hs := (support_iff_internal (trace (frameShape p) g) (ambientLength p)).mpr ht.2.2.2
  have h := vertical_prefix_total hs (block_dominant p B) (block_first p B)
    (Nat.le_add_right (frameLength p) p.k)
  rw [vWeight_total,ht.2.2.1] at h
  exact h

theorem outside_zero (p : Parameters) {g : Coloring p.m (ambientLength p)}
    (ht : Tight (frameShape p) p.a p.b g) (B : Block p g) :
    ∀j,frameLength p≤j→j<ambientLength p→(trace (frameShape p) g j).grade=0 := by
  have hs := (support_iff_internal (trace (frameShape p) g) (ambientLength p)).mpr ht.2.2.2
  apply whole_grade_zero_outside hs (block_dominant p B) (block_first p B)
    (Nat.le_add_right (frameLength p) p.k)
  rw [prefix_horizontal_total p B,hWeight_total,ht.2.1]

theorem source_position (p : Parameters) {g : Coloring p.m (ambientLength p)}
    (ht : Tight (frameShape p) p.a p.b g) (B : Block p g) : SourcePosition p (trace (frameShape p) g) := by
  have hu : PositiveH (trace (frameShape p) g) 0 := by simpa only [block_origin p B] using B.supported
  have hfirst := first_return_debt hu (block_first p B)
  refine ⟨0,p.a+p.b,?_,?_,?_,?_,hu,?_,?_,?_⟩
  · have := p.ha
    dsimp [ambientLength,frameLength]
    omega
  · dsimp [ambientLength,frameLength]
    omega
  · simp [coord]
  · exact frame_last_coordinate (source_hypotheses p).2.2.1 (source_hypotheses p).2.2.2.1 p.determinant
  · simpa only [Nat.zero_le,ite_true] using hfirst.1
  · simpa only [Nat.zero_le,ite_true] using hfirst.2
  · intro j hj hout
    simp only [Nat.zero_le,ite_true,true_and,not_le] at hout
    exact outside_zero p ht B j (by dsimp [frameLength]; omega) hj

theorem located_tight (p : Parameters) {g : Coloring p.m (ambientLength p)}
    (ht : Tight (frameShape p) p.a p.b g) (B : Block p g) :
    LocatedTight (n:=frameLength p) (k:=p.k) (frameShape p) p.a p.b g :=
  source_position_localizes p ht (source_position p ht B)

end KroneckerSourcePositionBridge
end
end

/- Original module: KroneckerPublishedPositionApplication -/
section
/-! Apply the published maximum-shadow and coordinate result to the literal
finite frame. The internal first return and zero outside are proved, not inputs. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPublishedPositionApplication
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerWeights KroneckerTight
open KroneckerFrameIdentity KroneckerSourceGradingDictionary KroneckerSourceNaturalGradings
open KroneckerSourcePositionBridge KroneckerSourceParameterGates KroneckerSourceMaximalPath

/-- General negative-determinant source consequence of Lemma 4.12's proof
(maximum supported horizontal shadow) and Lemma 4.13 (coordinates), pp.14–15.
The strict b<d2 side condition rules out the whole-path fallback; it holds
for our Parameters. No RootComponent, ZeroOutside or SourcePosition premise. -/
def PublishedPosition : Prop :=
  ∀N d₁ d₂ a b (shape : ℕ→Bool) (g : Fin N→ℕ),
    N=d₁+d₂→0<a→0<b→a≤d₁→b<d₂→Maximal d₁ d₂ shape→
    (a:ℤ)*d₂-(b:ℤ)*d₁=-(Nat.gcd a b:ℕ)→NaturalTight shape a b g→
    Nonempty (PositionedShadow N d₁ d₂ a b shape (naturalTrace shape g))

theorem colored_natural_trace {m N : ℕ} (shape : ℕ→Bool) (g : Coloring m N) :
    naturalTrace shape (fun i => grade (g i))=trace shape g := by
  rw [trace_eq_raw_grades]
  rfl

theorem colored_natural_tight {m N a b : ℕ} (shape : ℕ→Bool) (g : Coloring m N)
    (ht : Tight shape a b g) : NaturalTight shape a b (fun i => grade (g i)) := by
  have h := (colored_tight_iff shape (a:ℤ) (b:ℤ) g).mp ht
  exact (natural_tight_bounded_iff shape (grades g)).mpr h

theorem has_literal_block (P : PublishedPosition) (p : Parameters)
    {g : Coloring p.m (ambientLength p)} (ht : Tight (frameShape p) p.a p.b g) : Nonempty (Block p g) := by
  have h := source_hypotheses p
  have hb := P (ambientLength p) p.d₁ p.d₂ p.a p.b (frameShape p) (fun i => grade (g i))
    p.length_eq h.1 h.2.1 p.hd₁.le p.hd₂ (ambient_path_maximal p) h.2.2.2.2.2.2.2.1
    (colored_natural_tight (frameShape p) g ht)
  simpa only [colored_natural_trace] using hb

def block (P : PublishedPosition) (p : Parameters)
    {g : Coloring p.m (ambientLength p)} (ht : Tight (frameShape p) p.a p.b g) : Block p g :=
  Classical.choice (has_literal_block P p ht)

theorem source_position (P : PublishedPosition) (p : Parameters)
    {g : Coloring p.m (ambientLength p)} (ht : Tight (frameShape p) p.a p.b g) :
    SourcePosition p (trace (frameShape p) g) :=
  KroneckerSourcePositionBridge.source_position p ht (block P p ht)

theorem located (P : PublishedPosition) (p : Parameters)
    {g : Coloring p.m (ambientLength p)} (ht : Tight (frameShape p) p.a p.b g) :
    LocatedTight (n:=frameLength p) (k:=p.k) (frameShape p) p.a p.b g :=
  KroneckerSourcePositionBridge.located_tight p ht (block P p ht)

theorem tight_iff_located (P : PublishedPosition) (p : Parameters) (g : Coloring p.m (ambientLength p)) :
    Tight (frameShape p) p.a p.b g ↔
    LocatedTight (n:=frameLength p) (k:=p.k) (frameShape p) p.a p.b g :=
  ⟨located P p,fun h => h.1⟩

theorem tight_count_frame (P : PublishedPosition) (p : Parameters) :
    Nat.card {g:Coloring p.m (ambientLength p) // Tight (frameShape p) p.a p.b g}=
    Nat.card {g:Coloring p.m (frameLength p) // Connected p.m (word (frameShape p) g) 0} := by
  have hcounts := KroneckerDyck.frame_edge_counts (source_hypotheses p).2.2.1
    (source_hypotheses p).2.2.2.1 p.determinant
  have hframe := frame_count (m:=p.m) (n:=frameLength p) (k:=p.k) (frameShape p) p.a p.b hcounts.1 hcounts.2
  have ht := Nat.card_congr (Equiv.subtypeEquivRight (tight_iff_located P p))
  exact ht.trans hframe.symm

theorem weighted_frame_count (P : PublishedPosition) (p : Parameters) :
    weightedCount (fun d:Grades p.m (ambientLength p) => Tight (frameShape p) p.a p.b (representative d))=
    Nat.card {g:Coloring p.m (frameLength p) // Connected p.m (word (frameShape p) g) 0} := by
  rw [← tight_count_weighted]
  exact tight_count_frame P p

end KroneckerPublishedPositionApplication
end
end
