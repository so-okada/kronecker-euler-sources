import KroneckerNaturalNodes

/-! H-precursors after deletion. The finite-index theorem keeps the original
indices on undeleted edges. Reindexing is handled by the transport theorem. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerPrecursorDeletion
variable {H V : Type*} [Fintype V] [DecidableEq V]

def beforeSet (index : V → ℕ) (p : V → H) (k : ℕ) (x : H) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => index w < k ∧ p w = x)

def beforeCount (index : V → ℕ) (p : V → H) (k : ℕ) (x : H) : ℕ :=
  (beforeSet index p k x).card

def Precursor (hindex : H → ℕ) (vindex : V → ℕ) (g : H → ℕ)
    (p : V → H) : Prop :=
  ∀ w, hindex (p w) < vindex w ∧
    beforeCount vindex p (vindex w) (p w) < g (p w) ∧
    ∀ x, hindex x < vindex w → beforeCount vindex p (vindex w) x < g x →
      hindex x ≤ hindex (p w)

def lower (g : H → ℕ) (x : H) (y : H) : ℕ := by
  classical
  exact if y = x then g y - 1 else g y

theorem erased_count (index : V → ℕ) (p : V → H) (v : V) (k : ℕ) (x : H) :
    beforeCount (fun w : {w : V // w ≠ v} => index w.val)
      (fun w => p w.val) k x = ((beforeSet index p k x).erase v).card := by
  classical
  unfold beforeCount
  refine Finset.card_bij (fun w _ => w.val) ?_ ?_ ?_
  · intro w hw
    have hw' : index w.val < k ∧ p w.val = x := by simpa [beforeSet] using hw
    simpa [beforeSet] using And.intro w.property hw'
  · intro w hw z hz h
    exact Subtype.ext h
  · intro w hw
    have h := Finset.mem_erase.mp hw
    refine ⟨⟨w,h.1⟩, ?_, rfl⟩
    simpa [beforeSet] using h.2

omit [DecidableEq V] in
theorem count_strict (index : V → ℕ) (p : V → H) (w v : V)
    (h : index w < index v) (x : H) (hw : p w = x) :
    beforeCount index p (index w) x < beforeCount index p (index v) x := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro z hz
    simp only [beforeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨lt_trans hz.1 h, hz.2⟩
  · intro he
    have hm : w ∈ beforeSet index p (index v) x := by simp [beforeSet, h, hw]
    rw [← he] at hm
    simp [beforeSet] at hm

theorem erase_precursor (hindex : H → ℕ) (vindex : V → ℕ)
    (hinj : Function.Injective vindex) (g : H → ℕ) (p : V → H)
    (hp : Precursor hindex vindex g p) (v : V) :
    Precursor hindex (fun w : {w : V // w ≠ v} => vindex w.val)
      (lower g (p v)) (fun w => p w.val) := by
  classical
  intro w
  have ho := hp w.val
  have hv := hp v
  have hne : vindex w.val ≠ vindex v := fun he => w.property (hinj he)
  refine ⟨ho.1, ?_, ?_⟩
  · rw [erased_count]
    by_cases hb : vindex w.val < vindex v
    · have hn : v ∉ beforeSet vindex p (vindex w.val) (p w.val) := by
        simp [beforeSet, Nat.not_lt.mpr (Nat.le_of_lt hb)]
      rw [Finset.erase_eq_of_notMem hn]
      by_cases he : p w.val = p v
      · have hs := count_strict vindex p w.val v hb (p v) he
        simp only [lower, ite_eq_left he]
        rw [he]
        dsimp [beforeCount] at hs hv
        omega
      · simpa [lower, he, beforeCount] using ho.2.1
    · have ha : vindex v < vindex w.val := by omega
      by_cases he : p w.val = p v
      · have hm : v ∈ beforeSet vindex p (vindex w.val) (p w.val) := by
          simp [beforeSet, ha, he]
        have hc := Finset.card_erase_add_one hm
        simp only [lower, ite_eq_left he]
        dsimp [beforeCount] at ho
        omega
      · have hn : v ∉ beforeSet vindex p (vindex w.val) (p w.val) := by
          simp [beforeSet, Ne.symm he]
        rw [Finset.erase_eq_of_notMem hn]
        simpa [lower, he, beforeCount] using ho.2.1
  · intro x hx hc
    apply ho.2.2 x hx
    rw [erased_count] at hc
    by_cases he : x = p v
    · subst x
      simp only [lower, ↓reduceIte] at hc
      have hle := Finset.pred_card_le_card_erase (s := beforeSet vindex p (vindex w.val) (p v)) (a := v)
      dsimp [beforeCount]
      omega
    · have hn : v ∉ beforeSet vindex p (vindex w.val) x := by
        simp [beforeSet, Ne.symm he]
      rw [Finset.erase_eq_of_notMem hn] at hc
      simpa [lower, he, beforeCount] using hc


def compress (r k : ℕ) : ℕ := if k < r then k else k-1

theorem compress_lt_iff (r a b : ℕ) (ha : a ≠ r) (hb : b ≠ r) :
    compress r a < compress r b ↔ a < b := by
  unfold compress
  split_ifs <;> omega

theorem compress_le_iff (r a b : ℕ) (ha : a ≠ r) (hb : b ≠ r) :
    compress r a ≤ compress r b ↔ a ≤ b := by
  unfold compress
  split_ifs <;> omega

theorem erase_precursor_compressed (hindex : H → ℕ) (vindex : V → ℕ)
    (hinj : Function.Injective vindex) (g : H → ℕ) (p : V → H)
    (hp : Precursor hindex vindex g p) (v : V)
    (hdisj : ∀ x, hindex x ≠ vindex v) :
    Precursor (fun x => compress (vindex v) (hindex x))
      (fun w : {w : V // w ≠ v} => compress (vindex v) (vindex w.val))
      (lower g (p v)) (fun w => p w.val) := by
  classical
  have hne (w : {w : V // w ≠ v}) : vindex w.val ≠ vindex v :=
    fun he => w.property (hinj he)
  have hcount (w : {w : V // w ≠ v}) (x : H) :
      beforeCount (fun z : {w : V // w ≠ v} => compress (vindex v) (vindex z.val))
        (fun z => p z.val) (compress (vindex v) (vindex w.val)) x =
      beforeCount (fun z : {w : V // w ≠ v} => vindex z.val)
        (fun z => p z.val) (vindex w.val) x := by
    unfold beforeCount
    congr 1
    ext z
    simp only [beforeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [compress_lt_iff _ _ _ (hne z) (hne w)]
  have h := erase_precursor hindex vindex hinj g p hp v
  intro w
  refine ⟨(compress_lt_iff _ _ _ (hdisj _) (hne w)).mpr (h w).1, ?_, ?_⟩
  · rw [hcount]
    exact (h w).2.1
  · intro x hx hc
    rw [hcount] at hc
    apply (compress_le_iff _ _ _ (hdisj _) (hdisj _)).mpr
    exact (h w).2.2 x ((compress_lt_iff _ _ _ (hdisj _) (hne w)).mp hx) hc

open KroneckerPaperPaths
open KroneckerPaperPathGradings (Horizontal Vertical edgeIndex assignmentCount)

theorem natural_precursor_iff (Z : TNEPath) [Fintype (Vertical Z)]
    (g : KroneckerNaturalPathGradings.Grading Z) (p : Vertical Z → Horizontal Z) :
    KroneckerNaturalPathGradings.IsHPrecursor g p ↔
      Precursor (fun x : Horizontal Z => edgeIndex x.val)
        (fun w : Vertical Z => edgeIndex w.val) (fun x => g x.val) p := by
  classical
  have hc (k : ℕ) (x : Horizontal Z) :
      beforeCount (fun w : Vertical Z => edgeIndex w.val) p k x = assignmentCount p k x := by
    simp only [beforeCount, beforeSet, assignmentCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hh := KroneckerPaperPathGradings.isHPrecursor_iff
    (KroneckerNaturalPathGradings.bounded g) p
  simpa only [KroneckerNaturalPathGradings.IsHPrecursor,
    KroneckerPaperPathGradings.IsHPrecursor, KroneckerPaperPathGradings.IsPredecessor,
    KroneckerNaturalPathGradings.bounded, Precursor, hc] using hh

/-- The manuscript deletion identity in geometric-edge coordinates: retain every
horizontal edge, remove v, lower the grade at p(v), and compress edge indices.
The output precursor is exactly the restriction of p. -/
theorem geometric_erasure (Z : TNEPath) [Fintype (Vertical Z)] [DecidableEq (Vertical Z)]
    (g : KroneckerNaturalPathGradings.Grading Z) (p : Vertical Z → Horizontal Z)
    (hp : KroneckerNaturalPathGradings.IsHPrecursor g p) (v : Vertical Z) :
    Precursor (fun x : Horizontal Z => compress (edgeIndex v.val) (edgeIndex x.val))
      (fun w : {w : Vertical Z // w ≠ v} => compress (edgeIndex v.val) (edgeIndex w.val.val))
      (lower (fun x : Horizontal Z => g x.val) (p v)) (fun w => p w.val) := by
  classical
  have hi : Function.Injective (fun w : Vertical Z => edgeIndex w.val) := by
    intro a b h
    apply Subtype.ext
    apply (edgeEquiv Z).symm.injective
    exact Fin.ext h
  have hd (x : Horizontal Z) : edgeIndex x.val ≠ edgeIndex v.val := by
    intro he
    have he' : x.val = v.val := (edgeEquiv Z).symm.injective (Fin.ext he)
    have hx := x.property
    rw [he'] at hx
    rw [v.property] at hx
    cases hx
  exact erase_precursor_compressed _ _ hi _ p ((natural_precursor_iff Z g p).mp hp) v hd

end KroneckerPrecursorDeletion
