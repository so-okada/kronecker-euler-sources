import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Finite
import KroneckerLogic

set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerAsymptotics

/-- Superadditivity is needed only on the tail n ≥ 3. -/
def TailSuperadditive (u : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, 3 ≤ i → ∀ j : ℕ, 3 ≤ j → u i + u j ≤ u (i+j)

theorem block_lower_bound {u : ℕ → ℝ} (h : TailSuperadditive u)
    {t r : ℕ} (ht : 3≤t) (hr : 3≤r) (k : ℕ) :
    (k : ℝ)*u t+u r ≤ u (k*t+r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkr : 3≤k*t+r := by omega
    calc
      ((k+1 : ℕ) : ℝ)*u t+u r = u t+((k : ℝ)*u t+u r) := by push_cast; ring
      _ ≤ u t+u (k*t+r) := add_le_add le_rfl ih
      _ ≤ u (t+(k*t+r)) := h t ht (k*t+r) hkr
      _ = u ((k+1)*t+r) := by congr 1; ring

theorem tail_eventually_gt {u : ℕ → ℝ} (h : TailSuperadditive u)
    (hpos : ∀ n, 3≤n → 0≤u n) {t : ℕ} (ht : 3≤t) {L : ℝ}
    (hL : L<u t/(t : ℝ)) : ∀ᶠ n in atTop, L<u n/(n : ℝ) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t≠0)
  refine Eventually.atTop_of_arithmetic (by omega : t≠0) (fun r _ => ?_)
  have hbase : 3≤3*t+r := by omega
  have A : Tendsto (fun x : ℝ => u t / ((t : ℝ) + ((3*t+r : ℕ) : ℝ)/x))
      atTop (𝓝 (u t/(t : ℝ))) := by
    have hden : Tendsto (fun x : ℝ => (t : ℝ) + ((3*t+r : ℕ) : ℝ)/x)
        atTop (𝓝 ((t : ℝ) + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    have hdiv := (tendsto_const_nhds : Tendsto (fun _ : ℝ => u t) atTop (𝓝 (u t))).div hden
      (by simpa using ht0)
    change Tendsto (fun x : ℝ => u t / ((t : ℝ) + ((3*t+r : ℕ) : ℝ)/x))
      atTop (𝓝 (u t / ((t : ℝ) + 0))) at hdiv
    simpa only [add_zero] using hdiv
  have B : Tendsto (fun x : ℝ => x*u t/((t : ℝ)*x+((3*t+r : ℕ) : ℝ)))
      atTop (𝓝 (u t/(t : ℝ))) := by
    apply A.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp
  have hevent : ∀ᶠ k : ℕ in atTop,
      L<u (t*(k+3)+r)/((t*(k+3)+r : ℕ) : ℝ) := by
    filter_upwards [(B.comp tendsto_natCast_atTop_atTop).eventually (lt_mem_nhds hL)] with k hk
    have hlo : (k : ℝ)*u t ≤ u (k*t+(3*t+r)) :=
      le_trans (le_add_of_nonneg_right (hpos _ hbase)) (block_lower_bound h ht hbase k)
    have heq : k*t+(3*t+r)=t*(k+3)+r := by ring
    rw [heq] at hlo
    have hn : 0≤((t*(k+3)+r : ℕ) : ℝ) := by positivity
    apply lt_of_lt_of_le _ (div_le_div_of_nonneg_right hlo hn)
    simpa [Function.comp_apply, Nat.cast_add, Nat.cast_mul, mul_add, add_assoc, mul_comm] using hk
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  refine eventually_atTop.mpr ⟨N+3,fun k hk => ?_⟩
  have hkn : N≤k-3 := by omega
  have hk3 : k-3+3=k := by omega
  simpa only [hk3] using hN (k-3) hkn

/-- Tail version of Fekete's lemma used by the periodic-growth proof.
There is no assumption that the first two indices satisfy superadditivity. -/
theorem tail_fekete {u : ℕ → ℝ} (h : TailSuperadditive u)
    (hpos : ∀ n, 3≤n → 0≤u n) (C : ℝ)
    (hbound : ∀ n, 3≤n → u n≤C*n) :
    Tendsto (fun n => u n/(n : ℝ)) atTop
      (𝓝 (sSup ((fun n : ℕ => u n/(n : ℝ)) '' Set.Ici 3))) := by
  let S := (fun n : ℕ => u n/(n : ℝ)) '' Set.Ici 3
  have hne : S.Nonempty := ⟨u 3/3,3,by simp,by norm_num⟩
  have hb : BddAbove S := by
    refine ⟨C,?_⟩
    rintro z ⟨n,hn,rfl⟩
    change 3≤n at hn
    exact (div_le_iff₀ (by exact_mod_cast (by omega : 0<n))).mpr (hbound n hn)
  apply tendsto_order.2
  constructor
  · intro L hL
    obtain ⟨z,hz,hLz⟩ := exists_lt_of_lt_csSup hne hL
    obtain ⟨t,ht,rfl⟩ := hz
    exact tail_eventually_gt h hpos ht hLz
  · intro L hL
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact lt_of_le_of_lt (le_csSup hb ⟨n,hn,rfl⟩) hL

/-- Passing from liminf/limsup bounds to eventual intervals, with the
boundedness hypotheses made explicit. -/
theorem eventual_enlarged_interval {u : ℕ → ℝ} {a b ε : ℝ}
    (hbelow : atTop.IsBoundedUnder (· ≥ ·) u)
    (habove : atTop.IsBoundedUnder (· ≤ ·) u)
    (hlo : a≤liminf u atTop) (hhi : limsup u atTop≤b) (hε : 0<ε) :
    ∀ᶠ n in atTop, a-ε≤u n ∧ u n≤b+ε := by
  filter_upwards [eventually_lt_of_lt_liminf (by linarith : a-ε<liminf u atTop) hbelow,
    eventually_lt_of_limsup_lt (by linarith : limsup u atTop<b+ε) habove] with n hn₁ hn₂
  exact ⟨hn₁.le,hn₂.le⟩

/-- Completes the conversion omitted from the earlier formalization:
common liminf/limsup intervals of arbitrarily small width give a common
limit. The starting bounds on each sequence are explicit. -/
theorem common_limits_from_liminf_limsup {I : Type*} [Nonempty I]
    (u : I → ℕ → ℝ)
    (hbelow : ∀ i, atTop.IsBoundedUnder (· ≥ ·) (u i))
    (habove : ∀ i, atTop.IsBoundedUnder (· ≤ ·) (u i))
    (hinterval : ∀ ε>0, ∃ a b : ℝ, b-a<ε ∧
      ∀ i, a≤liminf (u i) atTop ∧ limsup (u i) atTop≤b) :
    ∃ L : ℝ, ∀ i, Tendsto (u i) atTop (𝓝 L) := by
  apply KroneckerLogic.common_intervals_limit u
  intro ε hε
  obtain ⟨a,b,hw,hbounds⟩ := hinterval (ε/2) (by linarith)
  refine ⟨a-ε/8,b+ε/8,by linarith,?_⟩
  intro i
  exact eventual_enlarged_interval (hbelow i) (habove i)
    (hbounds i).1 (hbounds i).2 (by linarith)

#print axioms tail_fekete
#print axioms eventual_enlarged_interval
#print axioms common_limits_from_liminf_limsup

end KroneckerAsymptotics
