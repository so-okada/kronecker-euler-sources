import KroneckerInsertionPrecursorHelpers

/-! The candidate insertion map satisfies the three precursor conditions.
The chain is computed from the actual assignment fibers crossing the cut. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerInsertionPrecursorAssembly
open KroneckerPrecursorDeletion KroneckerInsertionPrecursorHelpers

variable {H V : Type*} [DecidableEq H] [Fintype V] [LinearOrder V]

def fiber (p : V → H) (x : H) : Finset V :=
  Finset.univ.filter (fun v => p v = x)

def Last (vi : V → ℕ) (p : V → H) (v : V) : Prop :=
  ∀ w, p w = p v → vi w ≤ vi v

def crossingEnds (hi : H → ℕ) (vi : V → ℕ) (p : V → H)
    (root : H) (q : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v =>
    hi (p v) < q ∧ q ≤ vi v ∧ p v ≠ root ∧ Last vi p v)

def chain (hi : H → ℕ) (vi : V → ℕ) (p : V → H)
    (root : H) (q : ℕ) : List V := (crossingEnds hi vi p root q).sort (· ≤ ·)

@[simp] theorem mem_chain (hi : H → ℕ) (vi : V → ℕ) (p : V → H)
    (root : H) (q : ℕ) (v : V) :
    v ∈ chain hi vi p root q ↔
      hi (p v) < q ∧ q ≤ vi v ∧ p v ≠ root ∧ Last vi p v := by
  classical
  simp [chain, crossingEnds]

theorem chain_order (hi : H → ℕ) (vi : V → ℕ) (hvi : StrictMono vi)
    (p : V → H) (root : H) (q : ℕ) :
    (chain hi vi p root q).Pairwise (fun v w => vi v < vi w) := by
  exact (Finset.sortedLT_sort _).pairwise.imp (fun h => hvi h)

theorem count_mono (vi : V → ℕ) (p : V → H) (x : H) {k l : ℕ}
    (hkl : k ≤ l) : beforeCount vi p k x ≤ beforeCount vi p l x := by
  apply Finset.card_le_card
  intro v hv
  simp only [beforeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact ⟨lt_of_lt_of_le hv.1 hkl, hv.2⟩

theorem count_le_fiber (vi : V → ℕ) (p : V → H) (x : H) (k : ℕ) :
    beforeCount vi p k x ≤ (fiber p x).card := by
  apply Finset.card_le_card
  intro v hv
  simp only [beforeSet, fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact hv.2

theorem last_exists (vi : V → ℕ) (hvi : StrictMono vi) (p : V → H)
    (x : H) (k : ℕ) (h : beforeCount vi p k x < (fiber p x).card) :
    ∃ v, p v = x ∧ k ≤ vi v ∧ Last vi p v := by
  classical
  have hn : (fiber p x).Nonempty := Finset.card_pos.mp (by omega)
  let v := (fiber p x).max' hn
  have hv : p v = x := by simpa [v, fiber] using Finset.max'_mem (fiber p x) hn
  have hl (w : V) (hw : p w = x) : vi w ≤ vi v := by
    apply hvi.monotone
    exact Finset.le_max' _ _ (by simp [fiber, hw])
  refine ⟨v, hv, ?_, fun w hw => hl w (hw.trans hv)⟩
  by_contra hk
  have he : beforeSet vi p k x = fiber p x := by
    ext w
    simp only [beforeSet, fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hw => hw.2, fun hw => ⟨by have := hl w hw; omega, hw⟩⟩
  simp only [beforeCount, he] at h
  omega

theorem count_last (vi : V → ℕ) (hvi : StrictMono vi) (p : V → H)
    (v : V) (hl : Last vi p v) :
    beforeCount vi p (vi v) (p v) + 1 = (fiber p (p v)).card := by
  classical
  have he : beforeSet vi p (vi v) (p v) = (fiber p (p v)).erase v := by
    ext w
    simp only [beforeSet, fiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨hb, he⟩
      exact ⟨fun hv => by subst w; omega, he⟩
    · rintro ⟨hne, he⟩
      have hb := hl w he
      have hv : vi w ≠ vi v := fun h => hne (hvi.injective h)
      exact ⟨by omega, he⟩
  rw [beforeCount, he]
  exact Finset.card_erase_add_one (by simp [fiber])

theorem chain_owner_order (hi : H → ℕ) (vi : V → ℕ) (hhi : Function.Injective hi)
    (g : H → ℕ) (p : V → H) (hp : Precursor hi vi g p)
    (root : H) (q : ℕ) {v w : V}
    (hv : v ∈ chain hi vi p root q) (hw : w ∈ chain hi vi p root q)
    (hvw : vi v < vi w) : hi (p w) < hi (p v) := by
  have hv' := (mem_chain hi vi p root q v).mp hv
  have hw' := (mem_chain hi vi p root q w).mp hw
  have hb : beforeCount vi p (vi v) (p w) < g (p w) :=
    lt_of_le_of_lt (count_mono vi p (p w) (Nat.le_of_lt hvw)) (hp w).2.1
  have hh := (hp v).2.2 (p w) (by omega) hb
  have hne : p w ≠ p v := by
    intro he
    have := hv'.2.2.2 w he
    omega
  have hne' : hi (p w) ≠ hi (p v) := fun he => hne (hhi he)
  omega

/-- The first chain endpoint at or after k, or the root after all endpoints. -/
theorem next_spec (vi : V → ℕ) (p : V → H) (root : H) (k : ℕ) (ts : List V) :
    nextOwner vi p root k ts = root ∨
      ∃ v ∈ ts, k ≤ vi v ∧ nextOwner vi p root k ts = p v := by
  induction ts with
  | nil => exact Or.inl rfl
  | cons t ts ih =>
    by_cases ht : vi t < k
    · simp only [nextOwner, ite_eq_left ht]
      rcases ih with h | ⟨v, hv, hk, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, hk, he⟩
    · exact Or.inr ⟨t, List.mem_cons_self, by omega, by simp [nextOwner, ht]⟩

theorem next_greatest (hi : H → ℕ) (vi : V → ℕ) (p : V → H) (root : H)
    (k : ℕ) (ts : List V)
    (ho : ts.Pairwise (fun v w => vi v < vi w))
    (ha : ∀ v ∈ ts, ∀ w ∈ ts, vi v < vi w → hi (p w) < hi (p v))
    (v : V) (hv : v ∈ ts) (hk : k ≤ vi v) :
    hi (p v) ≤ hi (nextOwner vi p root k ts) := by
  induction ts with
  | nil => simp at hv
  | cons t ts ih =>
    have ho' := List.pairwise_cons.mp ho
    by_cases ht : vi t < k
    · have hv' : v ∈ ts := by
        rcases List.mem_cons.mp hv with rfl | hv'
        · omega
        · exact hv'
      simp only [nextOwner, ite_eq_left ht]
      exact ih ho'.2 (fun a ha' b hb' => ha a (List.mem_cons_of_mem _ ha')
        b (List.mem_cons_of_mem _ hb')) hv'
    · simp only [nextOwner, ite_eq_right ht]
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact le_rfl
      · exact (ha t List.mem_cons_self v hv (ho'.1 v hv')).le

theorem inserted_none_next (vi : V → ℕ) (p : V → H) (root : H)
    (k : ℕ) (ts : List V) (hn : ts.Nodup) (hk : ∀ v ∈ ts, k ≤ vi v) :
    inserted p root ts none = nextOwner vi p root k ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    rw [inserted_new p root t ts (List.nodup_cons.mp hn).1]
    simp [nextOwner, Nat.not_lt.mpr (hk t List.mem_cons_self)]

theorem inserted_mem_next (vi : V → ℕ) (p : V → H) (root : H)
    (ts : List V) (ho : ts.Pairwise (fun v w => vi v < vi w))
    (v : V) (hv : v ∈ ts) :
    inserted p root ts (some v) = nextOwner vi p root (vi v + 1) ts := by
  induction ts with
  | nil => simp at hv
  | cons t ts ih =>
    have ho' := List.pairwise_cons.mp ho
    have hn : ts.Nodup := ho'.2.imp (fun h he => by subst_vars; omega)
    by_cases he : v = t
    · subst v
      change inserted p root ts ((Equiv.swap none (some t)) (some t)) = _
      rw [Equiv.swap_apply_right, inserted_none_next vi p root (vi t+1) ts hn
        (fun w hw => by have := ho'.1 w hw; omega)]
      simp [nextOwner]
    · have hv' : v ∈ ts := (List.mem_cons.mp hv).resolve_left he
      change inserted p root ts ((Equiv.swap none (some t)) (some v)) = _
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using he)]
      rw [ih ho'.2 hv']
      have ht : vi t < vi v+1 := by have := ho'.1 v hv'; omega
      simp only [nextOwner, ite_eq_left ht]

def shift (q k : ℕ) : ℕ := if k < q then k else k+1

def verticalIndex (q : ℕ) (vi : V → ℕ) : Option V → ℕ
  | none => q
  | some v => shift q (vi v)

def raised (g : H → ℕ) (root x : H) : ℕ := g x + if x = root then 1 else 0

theorem shift_strict (q : ℕ) : StrictMono (shift q) := by
  intro a b hab
  unfold shift
  split_ifs <;> omega

@[simp] theorem shift_lt_shift (q a b : ℕ) : shift q a < shift q b ↔ a < b :=
  (shift_strict q).lt_iff_lt

@[simp] theorem shift_le_shift (q a b : ℕ) : shift q a ≤ shift q b ↔ a ≤ b :=
  (shift_strict q).le_iff_le

@[simp] theorem shift_lt_cut (q a : ℕ) : shift q a < q ↔ a < q := by
  unfold shift
  split_ifs <;> omega

@[simp] theorem cut_lt_shift (q a : ℕ) : q < shift q a ↔ q ≤ a := by
  unfold shift
  split_ifs <;> omega

theorem next_at (vi : V → ℕ) (p : V → H) (root : H) (ts : List V)
    (ho : ts.Pairwise (fun v w => vi v < vi w)) (v : V) (hv : v ∈ ts) :
    nextOwner vi p root (vi v) ts = p v := by
  induction ts with
  | nil => simp at hv
  | cons t ts ih =>
    have ho' := List.pairwise_cons.mp ho
    rcases List.mem_cons.mp hv with rfl | hv'
    · simp [nextOwner]
    · simp only [nextOwner, ite_eq_left (ho'.1 v hv')]
      exact ih ho'.2 hv'

theorem shift_lt_small (q k a : ℕ) (hk : k ≤ q) : shift q a < k ↔ a < k := by
  unfold shift
  split_ifs <;> omega

theorem shift_lt_after (q k a : ℕ) (hk : q ≤ k) : shift q a < k+1 ↔ a < k := by
  unfold shift
  split_ifs <;> omega

theorem count_before_cut (hi : H → ℕ) (vi : V → ℕ) (p : V → H)
    (root x : H) (q k : ℕ) (hk : k ≤ q) :
    beforeCount (verticalIndex q vi) (inserted p root (chain hi vi p root q)) k x =
      beforeCount vi p k x := by
  classical
  have hfix (v : V) (hv : vi v < k) :
      inserted p root (chain hi vi p root q) (some v) = p v := by
    apply inserted_unchanged
    intro hm
    have := (mem_chain hi vi p root q v).mp hm
    omega
  simp only [beforeCount, beforeSet, Finset.card_filter]
  rw [Fintype.sum_option]
  simp only [verticalIndex, Nat.not_lt.mpr hk, false_and, ↓reduceIte, zero_add]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [shift_lt_small q k (vi v) hk]
  by_cases h : vi v < k
  · simp [hfix v h, h]
  · simp [h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem count_after_cut (vi : V → ℕ) (Q : Option V → H)
    (q k : ℕ) (hk : q ≤ k) (x : H) :
    beforeCount (verticalIndex q vi) Q (k+1) x = prefixCount vi k Q x := by
  classical
  simp only [beforeCount, beforeSet, Finset.card_filter, prefixCount]
  apply Finset.sum_congr rfl
  intro v hv
  cases v with
  | none => simp [verticalIndex, prefixTest, show q < k+1 by omega]
  | some v => simp [verticalIndex, prefixTest, shift_lt_after q k (vi v) hk]

/-- The hypotheses are the old precursor, exhaustion of its fibers, and a
minimal root owning a globally last vertical edge. All chain, parent and
positive-debt conditions are derived in the proof. -/
theorem inserted_precursor (hi : H → ℕ) (vi : V → ℕ)
    (hhi : Function.Injective hi) (hvi : StrictMono vi)
    (g : H → ℕ) (p : V → H) (hp : Precursor hi vi g p)
    (hs : ∀ x, (fiber p x).card = g x)
    (root : H) (r : V) (hr : p r = root)
    (hmin : ∀ x, hi root ≤ hi x) (hmax : ∀ v, vi v ≤ vi r)
    (q : ℕ) (hroot : hi root < q) (hcut : q ≤ vi r) :
    Precursor (fun x => shift q (hi x)) (verticalIndex q vi) (raised g root)
      (inserted p root (chain hi vi p root q)) := by
  classical
  let ts := chain hi vi p root q
  let Q := inserted p root ts
  let a := fun k => nextOwner vi p root k ts
  have ho : ts.Pairwise (fun v w => vi v < vi w) := chain_order hi vi hvi p root q
  have hn : ts.Nodup := ho.imp (fun h he => by subst_vars; omega)
  have ha : ∀ v ∈ ts, ∀ w ∈ ts, vi v < vi w → hi (p w) < hi (p v) :=
    fun v hv w hw hvw => chain_owner_order hi vi hhi g p hp root q hv hw hvw
  have hm (v : V) (hv : v ∈ ts) :
      hi (p v) < q ∧ q ≤ vi v ∧ p v ≠ root ∧ Last vi p v :=
    (mem_chain hi vi p root q v).mp hv
  have hab (k : ℕ) : hi (a k) < q := by
    rcases next_spec vi p root k ts with he | ⟨t, ht, _, he⟩
    · change hi (nextOwner vi p root k ts) < q
      rw [he]
      exact hroot
    · change hi (nextOwner vi p root k ts) < q
      rw [he]
      exact (hm t ht).1
  have har (k : ℕ) (hk : k ≤ vi r) : beforeCount vi p k root < g root := by
    have hh := (hp r).2.1
    rw [hr] at hh
    exact lt_of_le_of_lt (count_mono vi p root hk) hh
  have hap (k : ℕ) (hk : k ≤ vi r) : beforeCount vi p k (a k) < g (a k) := by
    rcases next_spec vi p root k ts with he | ⟨t, ht, hkt, he⟩
    · change beforeCount vi p k (nextOwner vi p root k ts) < g (nextOwner vi p root k ts)
      rw [he]
      exact har k hk
    · change beforeCount vi p k (nextOwner vi p root k ts) < g (nextOwner vi p root k ts)
      rw [he]
      exact lt_of_le_of_lt (count_mono vi p (p t) hkt) (hp t).2.1
  have hcount (k : ℕ) (hk : q ≤ k) (x : H) :
      beforeCount (verticalIndex q vi) Q (k+1) x =
        beforeCount vi p k x + if a k = x then 1 else 0 := by
    rw [count_after_cut vi Q q k hk]
    exact prefix_count_formula vi k p root x ts ho
  have hcover (x : H) (k : ℕ) (hx : hi x < q) (hxr : x ≠ root)
      (hqk : q ≤ k) (hc : beforeCount vi p k x < g x) :
      ∃ v ∈ ts, k ≤ vi v ∧ p v = x := by
    obtain ⟨v, hv, hkv, hl⟩ := last_exists vi hvi p x k (by rw [hs]; exact hc)
    refine ⟨v, ?_, hkv, hv⟩
    exact (mem_chain hi vi p root q v).mpr ⟨by simpa [hv] using hx,
      by omega, by simpa [hv] using hxr, hl⟩
  intro v
  change shift q (hi (Q v)) < verticalIndex q vi v ∧
    beforeCount (verticalIndex q vi) Q (verticalIndex q vi v) (Q v) < raised g root (Q v) ∧
    ∀ x, shift q (hi x) < verticalIndex q vi v →
      beforeCount (verticalIndex q vi) Q (verticalIndex q vi v) x < raised g root x →
        shift q (hi x) ≤ shift q (hi (Q v))
  cases v with
  | none =>
    simp only [verticalIndex]
    have hQ : Q none = a q := inserted_none_next vi p root q ts hn
      (fun v hv => (hm v hv).2.1)
    rw [hQ]
    refine ⟨(shift_lt_cut q _).mpr (hab q), ?_, ?_⟩
    · rw [count_before_cut hi vi p root (a q) q q le_rfl]
      have hh := hap q hcut
      unfold raised
      omega
    · intro x hx hc
      rw [count_before_cut hi vi p root x q q le_rfl] at hc
      apply (shift_le_shift q _ _).mpr
      by_cases he : x = root
      · subst x
        exact hmin (a q)
      · simp only [raised, ite_eq_right he, add_zero] at hc
        obtain ⟨w, hw, hqw, hpw⟩ := hcover x q
          ((shift_lt_cut q _).mp hx) he le_rfl hc
        rw [← hpw]
        exact next_greatest hi vi p root q ts ho ha w hw hqw
  | some v =>
    by_cases hbefore : vi v < q
    · have hnot : v ∉ ts := by intro hv; have := (hm v hv).2.1; omega
      have hQ : Q (some v) = p v := inserted_unchanged p root ts v hnot
      have hindex : verticalIndex q vi (some v) = vi v := by simp [verticalIndex, shift, hbefore]
      rw [hQ, hindex]
      refine ⟨?_, ?_, ?_⟩
      · have hprior := (hp v).1
        simpa [shift, show hi (p v) < q by omega] using hprior
      · rw [count_before_cut hi vi p root (p v) q (vi v) (by omega)]
        have hh := (hp v).2.1
        unfold raised
        omega
      · intro x hx hc
        rw [count_before_cut hi vi p root x q (vi v) (by omega)] at hc
        apply (shift_le_shift q _ _).mpr
        by_cases he : x = root
        · subst x
          exact hmin (p v)
        · simp only [raised, ite_eq_right he, add_zero] at hc
          exact (hp v).2.2 x ((shift_lt_small q (vi v) (hi x) (by omega)).mp hx) hc
    · have hqv : q ≤ vi v := by omega
      have hindex : verticalIndex q vi (some v) = vi v+1 := by simp [verticalIndex, shift, hbefore]
      rw [hindex]
      by_cases hv : v ∈ ts
      · have hQ : Q (some v) = a (vi v+1) := inserted_mem_next vi p root ts ho v hv
        have hav : a (vi v) = p v := next_at vi p root ts ho v hv
        have hvr : v ≠ r := by intro he; subst v; exact (hm r hv).2.2.1 hr
        have hvr' : vi v < vi r := by
          have := hmax v
          have hn' : vi v ≠ vi r := fun he => hvr (hvi.injective he)
          omega
        have hne : a (vi v+1) ≠ p v := by
          rcases next_spec vi p root (vi v+1) ts with he | ⟨w, hw, hkw, he⟩
          · change nextOwner vi p root (vi v+1) ts ≠ p v
            rw [he]
            exact Ne.symm (hm v hv).2.2.1
          · change nextOwner vi p root (vi v+1) ts ≠ p v
            rw [he]
            intro h
            have := (hm v hv).2.2.2 w h
            omega
        rw [hQ]
        refine ⟨?_, ?_, ?_⟩
        · have hh := hab (vi v+1)
          have hs' : shift q (hi (a (vi v+1))) = hi (a (vi v+1)) := by simp [shift, hh]
          rw [hs']
          omega
        · rw [hcount (vi v) hqv, hav, ite_eq_right (Ne.symm hne), add_zero]
          have hh := hap (vi v+1) (by omega)
          have hb := count_mono vi p (a (vi v+1)) (show vi v ≤ vi v+1 by omega)
          unfold raised
          omega
        · intro x hx hc
          rw [hcount (vi v) hqv x, hav] at hc
          apply (shift_le_shift q _ _).mpr
          by_cases hxr : x = root
          · subst x
            exact hmin _
          · simp only [raised, ite_eq_right hxr, add_zero] at hc
            have hxold : beforeCount vi p (vi v) x < g x := by omega
            have hxprior : hi x < vi v := by
              simpa only [← hindex, verticalIndex, shift_lt_shift] using hx
            have hxle := (hp v).2.2 x hxprior hxold
            have hxn : x ≠ p v := by
              intro he
              subst x
              have hh := count_last vi hvi p v (hm v hv).2.2.2
              rw [hs] at hh
              have hbad : beforeCount vi p (vi v) (p v) + 1 < g (p v) := by
                simpa only [ite_true] using hc
              omega
            obtain ⟨w, hw, hkw, hpw⟩ := hcover x (vi v)
              (lt_of_le_of_lt hxle (hm v hv).1) hxr hqv hxold
            have hwv : w ≠ v := by intro he; subst w; exact hxn hpw.symm
            have hk' : vi v+1 ≤ vi w := by
              have hne' : vi w ≠ vi v := fun he => hwv (hvi.injective he)
              omega
            rw [← hpw]
            exact next_greatest hi vi p root (vi v+1) ts ho ha w hw hk'
      · have hQ : Q (some v) = p v := inserted_unchanged p root ts v hv
        rw [hQ]
        refine ⟨?_, ?_, ?_⟩
        · have hh := (shift_lt_shift q (hi (p v)) (vi v)).mpr (hp v).1
          simpa [shift, hbefore] using hh
        · rw [hcount (vi v) hqv]
          by_cases hrp : p v = root
          · subst root
            have hh := (hp v).2.1
            simp only [raised]
            split_ifs <;> omega
          · by_cases he : a (vi v) = p v
            · have hh : beforeCount vi p (vi v) (p v)+1 < g (p v) := by
                rcases next_spec vi p root (vi v) ts with har' | ⟨w, hw, hkw, haw⟩
                · exact (hrp (he.symm.trans har')).elim
                · have hpw : p w = p v := haw.symm.trans he
                  have hwv : w ≠ v := by intro h; subst w; exact hv hw
                  have hkw' : vi v < vi w := by
                    have hn' : vi w ≠ vi v := fun h => hwv (hvi.injective h)
                    omega
                  have hc := count_strict vi p v w hkw' (p v) rfl
                  have hb := (hp w).2.1
                  rw [hpw] at hb
                  omega
              simp only [raised, ite_eq_right hrp, ite_eq_left he, add_zero]
              exact hh
            · simp only [raised, ite_eq_right hrp, ite_eq_right he, add_zero]
              exact (hp v).2.1
        · intro x hx hc
          rw [hcount (vi v) hqv x] at hc
          apply (shift_le_shift q _ _).mpr
          by_cases hxr : x = root
          · subst x
            exact hmin _
          · simp only [raised, ite_eq_right hxr, add_zero] at hc
            have hxprior : hi x < vi v := by
              simpa only [← hindex, verticalIndex, shift_lt_shift] using hx
            exact (hp v).2.2 x hxprior (by omega)

#print axioms inserted_precursor
end KroneckerInsertionPrecursorAssembly
