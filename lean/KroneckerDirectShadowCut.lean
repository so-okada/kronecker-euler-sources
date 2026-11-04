import KroneckerDirectShadowBudget

/-! Cyclic support transported to a cut at a minimum of the debt walk. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace KroneckerDirectShadowBudget
open KroneckerStack KroneckerCompatibility KroneckerTight
open KroneckerSourceIntervalCounts KroneckerSourcePeriodicSums

theorem walk_shift (f : Edge → ℤ) (E : ℕ → Edge) (c i : ℕ) :
    walk f (fun k => E (c+k)) i = walk f E (c+i) - walk f E c :=
  walk_subpath (fun _ _ => rfl) f i (le_refl i)

theorem hwitness_interval_congr {E F : ℕ → Edge} {p q l : ℕ}
    (h : ∀ k, k < l+1 → E (p+k) = F (q+k)) :
    HWitness E p (p+l) ↔ HWitness F q (q+l) := by
  let A := fun k => E (p+k)
  have hE := hwitness_subpath (Nat.succ_pos l) (show ∀ k, k < l+1 → A k = E (p+k) from fun _ _ => rfl)
  have hF := hwitness_subpath (Nat.succ_pos l) (show ∀ k, k < l+1 → A k = F (q+k) from h)
  have hp : p + l.succ - 1 = p + l := by omega
  have hq : q + l.succ - 1 = q + l := by omega
  simpa only [hp, hq] using hE.symm.trans hF

theorem support_shift {E : ℕ → Edge} {N c : ℕ}
    (hE : Function.Periodic E N) (hc : c < N) (hs : ShadowSupport E N) :
    ShadowSupport (fun k => E (c+k)) N := by
  intro v hv hvP
  have hN : 0 < N := by omega
  let q := (c+v)%N
  have hq : q < N := Nat.mod_lt _ hN
  have heq : E q = E (c+v) := hE.map_mod_nat _
  obtain ⟨p,hp,hpP,hps⟩ := hs q hq (by simpa only [PositiveV,heq] using hvP)
  let u := if c ≤ p then p-c else p+N-c
  have hu : u < N := by dsimp [u]; split_ifs <;> omega
  have hup : (c+u)%N = p := by
    dsimp [u]
    split_ifs with h
    · rw [show c+(p-c)=p by omega, Nat.mod_eq_of_lt hp]
    · rw [show c+(p+N-c)=p+N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hp]
  have hepu : E p = E (c+u) := by
    rw [← hup]
    exact hE.map_mod_nat _
  refine ⟨u,hu,by simpa only [PositiveH,hepu] using hpP,?_⟩
  let l := (if u ≤ v then v else v+N)-u
  have hlu : u+l = if u ≤ v then v else v+N := by dsimp [l]; split_ifs <;> omega
  have hlp : p+l = if p ≤ q then q else q+N := by
    have hspan := cyclic_span_shift hc hu hv
    rw [hup] at hspan
    change (if p ≤ q then q else q+N)-p=l at hspan
    split_ifs at hspan ⊢ <;> omega
  have he : ∀ k, k < l+1 → E (p+k) = E (c+(u+k)) := by
    intro k _
    calc
      E (p+k) = E ((p+k)%N) := (hE.map_mod_nat _).symm
      _ = E ((c+(u+k))%N) := by rw [← hup, Nat.mod_add_mod, Nat.add_assoc]
      _ = E (c+(u+k)) := hE.map_mod_nat _
  have hw := hwitness_interval_congr (F := fun k => E (c+k)) he
  rw [hlp,hlu] at hw
  exact fun h => hps (hw.mpr h)

theorem support_linear_of_last_min {E : ℕ → Edge} {N : ℕ}
    (hs : ShadowSupport E N)
    (hmin : ∀ i, i ≤ N → debt E N ≤ debt E i) : LinearSupport E N := by
  intro v hv hvP
  obtain ⟨u,hu,huP,hshadow⟩ := hs v hv hvP
  have ha := (KroneckerTight.shadow_iff_active huP).mp hshadow
  by_cases huv : u ≤ v
  · have hne : u ≠ v := by
      intro heq
      subst u
      obtain ⟨g,_,hg⟩ := huP
      obtain ⟨k,_,hk⟩ := hvP
      rw [hg] at hk
      contradiction
    exact ⟨u,lt_of_le_of_ne huv hne,huP,by simpa [huv] using ha⟩
  · simp only [ite_eq_right huv] at ha
    have hh := ha N hu (by omega)
    have hl := hmin u hu.le
    omega

theorem exists_min_cut {E : ℕ → Edge} {N : ℕ}
    (hE : Function.Periodic E N) (hN : 0 < N) (hneg : debt E N ≤ 0) :
    ∃ c, c < N ∧ ∀ i, i ≤ N →
      debt (fun k => E (c+k)) N ≤ debt (fun k => E (c+k)) i := by
  obtain ⟨c,hc,hcm⟩ := Finset.exists_min_image (Finset.range N) (debt E)
    ⟨0, Finset.mem_range.mpr hN⟩
  have hcN : c < N := Finset.mem_range.mp hc
  refine ⟨c,hcN,?_⟩
  intro i hi
  change walk Edge.debtChange (fun k => E (c+k)) N ≤
    walk Edge.debtChange (fun k => E (c+k)) i
  rw [walk_shift, walk_shift, walk_add_period hE]
  change debt E c + debt E N - debt E c ≤ debt E (c+i) - debt E c
  by_cases hci : c+i < N
  · have hm := hcm (c+i) (Finset.mem_range.mpr hci)
    omega
  · have hciN : c+i-N < N := by omega
    have hm := hcm (c+i-N) (Finset.mem_range.mpr hciN)
    have hper := walk_add_period hE Edge.debtChange (c+i-N)
    rw [show c+i-N+N=c+i by omega] at hper
    change debt E (c+i)=debt E (c+i-N)+debt E N at hper
    omega

theorem cost_shift_period {E : ℕ → Edge} {N : ℕ} (hE : Function.Periodic E N)
    (d₁ d₂ : ℤ) (c : ℕ) :
    cost (fun k => E (c+k)) d₁ d₂ 0 N = cost E d₁ d₂ 0 N := by
  have h (f : Edge → ℤ) :
      (∑ i ∈ Finset.Ico 0 N, f (E (c+i))) = ∑ i ∈ Finset.Ico 0 N, f (E i) := by
    rw [interval_walk f (fun k => E (c+k)) 0 N (Nat.zero_le _),
      interval_walk f E 0 N (Nat.zero_le _), walk_shift, walk_add_period hE]
    simp [walk]
  simp only [cost, hWeight, vWeight, h]

/-- A cyclic compatible grading of total cost one has a single complete
supported shadow. The coordinate bounds determine both endpoints. -/
theorem one_cyclic_block {E : ℕ → Edge} {N : ℕ} {d₁ d₂ : ℤ} {φ : ℕ → ℤ}
    (hN : 0 < N) (hE : Function.Periodic E N) (hd₂ : 0 < d₂)
    (hstep : ∀ i, φ (i+1) = φ i + d₂ * hFlag (E i) - d₁ * vFlag (E i))
    (hbound : ∀ i, 0 ≤ φ i ∧ φ i < d₁+d₂)
    (hc : CyclicCompatible E N) (hs : ShadowSupport E N)
    (hneg : debt E N ≤ 0) (htotal : cost E d₁ d₂ 0 N = 1) :
    ∃ c u e, c < N ∧ e < N ∧
      PositiveH (fun k => E (c+k)) u ∧
      KroneckerSourceHorizontalShadow.FirstClosure (fun k => E (c+k)) u e ∧
      φ (c+u) = 0 ∧ φ (c+e) = d₁+d₂-1 ∧
      ZeroOn (fun k => E (c+k)) 0 u ∧ ZeroOn (fun k => E (c+k)) (e+1) N := by
  obtain ⟨c,hcN,hmin⟩ := exists_min_cut hE hN hneg
  let F := fun k => E (c+k)
  have hcF := cyclicCompatible_shift_forward hE hcN hc
  have hlinear : LinearCompatible F N := by
    intro u v huv hv huP hvP
    simpa only [ite_eq_left huv.le] using hcF u v (huv.trans hv) hv huP hvP
  have hsF := support_linear_of_last_min (support_shift hE hcN hs) hmin
  have hstepF : ∀ i, φ (c+(i+1)) = φ (c+i) +
      d₂ * hFlag (F i) - d₁ * vFlag (F i) := by
    intro i
    simpa only [Nat.add_assoc] using hstep (c+i)
  have hboundF : ∀ i, 0 ≤ φ (c+i) ∧ φ (c+i) < d₁+d₂ := fun i => hbound (c+i)
  have hb := budget_decomposition hsF hmin
    (fun s e he hp hf => shadow_cost_positive hd₂ hstepF hboundF hlinear he hp hf)
    0 (Nat.zero_le _) (by
      intro i hi
      have hi0 : i=0 := by omega
      subst i
      exact le_rfl)
  have hcost : cost F d₁ d₂ 0 N = 1 := (cost_shift_period hE d₁ d₂ c).trans htotal
  obtain ⟨u,e,_,he,hu,hf,hce,hpre,hpost⟩ := hb.2.2 hcost
  have hlo := shadow_cost_bound (d₁ := d₁) (φ := fun i => φ (c+i)) hd₂ hstepF hlinear he hu hf
  have hlu := (hboundF u).1
  have hhe := (hboundF e).2
  change φ (c+u) + d₁ + d₂ - φ (c+e) ≤ cost F d₁ d₂ u (e+1) at hlo
  change cost F d₁ d₂ u (e+1) = 1 at hce
  refine ⟨c,u,e,hcN,he,hu,hf,by omega,by omega,hpre,hpost⟩

end KroneckerDirectShadowBudget
