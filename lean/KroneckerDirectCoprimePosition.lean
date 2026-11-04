import KroneckerDirectShadowCut

/-! Direct positioning at determinant minus one, without the published
position axiom or either of the BLMMR structural lemmas. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerDirectCoprimePosition
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerTight
open KroneckerDyck KroneckerSourceIntervalCounts KroneckerSourceCompatibility
open KroneckerSourceGradingDictionary KroneckerSourcePeriodicSums
open KroneckerSourceHorizontalShadow KroneckerDirectShadowBudget

theorem coord_mod (d₁ d₂ i : ℕ) :
    coord d₁ d₂ (i%(d₁+d₂)) = coord d₁ d₂ i := by
  simp [coord, Nat.mod_mul_mod]

theorem trace_coordinate_step {m N d₁ d₂ : ℕ}
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (hN : N=d₁+d₂)
    (g : Coloring m N) (i : ℕ) :
    (coord d₁ d₂ (i+1) : ℤ) = (coord d₁ d₂ i : ℤ) +
      (d₂ : ℤ) * hFlag (trace (pathShape d₁ d₂) g i) -
      (d₁ : ℤ) * vFlag (trace (pathShape d₁ d₂) g i) := by
  have hpos : 0 < N := by omega
  have ht : trace (pathShape d₁ d₂) g i =
      paint (pathShape d₁ d₂ i) (g ⟨i%N,Nat.mod_lt _ hpos⟩) := by
    simp only [trace, dite_eq_right (Nat.ne_of_gt hpos)]
    congr 1
    simp only [pathShape, hN, coord_mod]
  rw [ht,coord_step h₁ h₂]
  by_cases hi : coord d₁ d₂ i < d₁
  · simp [pathShape,hi,paint,hFlag,vFlag]
  · rw [ite_eq_right hi,Nat.cast_sub (by omega : d₁ ≤ coord d₁ d₂ i)]
    simp [pathShape,hi,paint,hFlag,vFlag]

theorem shifted_block_indices {N c u e r : ℕ}
    (_hN : 0 < N) (hc : c < N) (he : e < N) (hue : u ≤ e) (_hr : r < N)
    (hu0 : (c+u)%N = 0) (her : (c+e)%N = r) :
    (c+u=0 ∨ c+u=N) ∧ e=u+r := by
  have hcub : c+u < 2*N := by omega
  have hceb : c+e < 2*N := by omega
  have hu : c+u=0 ∨ c+u=N := by
    by_cases h : c+u<N
    · rw [Nat.mod_eq_of_lt h] at hu0
      exact Or.inl hu0
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hu0
      exact Or.inr (by omega)
  refine ⟨hu,?_⟩
  rcases hu with hu | hu
  · have hz : c=0 := by omega
    rw [hz,Nat.zero_add,Nat.mod_eq_of_lt he] at her
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : N ≤ c+e),
      Nat.mod_eq_of_lt (by omega : c+e-N<N)] at her
    omega

theorem unshift_root {E : ℕ → Edge} {N c u e r : ℕ}
    (hE : Function.Periodic E N) (hu : c+u=0 ∨ c+u=N) (he : e=u+r)
    (hp : PositiveH (fun k => E (c+k)) u)
    (hf : FirstClosure (fun k => E (c+k)) u e) : RootComponent E (r+1) := by
  let F := fun k => E (c+k)
  change PositiveH F u at hp
  change FirstClosure F u e at hf
  have htrace : (fun k => F (u+k)) = E := by
    funext k
    dsimp [F]
    rw [← Nat.add_assoc]
    rcases hu with hu | hu
    · simp [hu]
    · rw [hu,Nat.add_comm]
      exact hE k
  have hwalk (k : ℕ) : debt E k = debt F (u+k) - debt F u := by
    have h := walk_shift Edge.debtChange F u k
    rw [htrace] at h
    exact h
  have hreturn := first_return_debt hp hf
  apply (root_iff_first_return E (r+1)).mpr
  refine ⟨Nat.succ_pos r,?_,?_,?_⟩
  · have h0 : F u=E 0 := by simpa using congrFun htrace 0
    simpa only [PositiveH,h0] using hp
  · rw [hwalk,show u+(r+1)=e+1 by omega,hreturn.1]
    omega
  · intro j hj hjr
    rw [hwalk]
    have h := hreturn.2 (u+j) (by omega) (by omega)
    omega

theorem unshift_zero {E : ℕ → Edge} {N c u e r : ℕ}
    (hE : Function.Periodic E N) (_hc : c < N) (_heN : e < N)
    (hu : c+u=0 ∨ c+u=N) (he : e=u+r)
    (hpre : ZeroOn (fun k => E (c+k)) 0 u)
    (hpost : ZeroOn (fun k => E (c+k)) (e+1) N) :
    ZeroOn E (r+1) N := by
  intro j hj hjN
  rcases hu with hu | hu
  · have hc0 : c=0 := by omega
    have hu0 : u=0 := by omega
    simpa [hc0] using hpost j (by omega) hjN
  · by_cases hjc : j < c
    · have ht : c+(j+N-c)=j+N := by omega
      have hz := hpost (j+N-c) (by omega) (by omega)
      simpa only [ht,hE j] using hz
    · have ht : c+(j-c)=j := by omega
      have hz := hpre (j-c) (Nat.zero_le _) (by omega)
      simpa only [ht] using hz

/-- The full frame position needed in the manuscript, proved from tightness
and the determinant-one arithmetic. There is no published position premise. -/
theorem tight_position {m N a b d₁ d₂ : ℕ}
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (hN : N=d₁+d₂)
    (ha : a < d₁) (hb : b < d₂)
    (hdet : (b : ℤ)*d₁-(a : ℤ)*d₂=1)
    (g : Coloring m N) (ht : Tight (pathShape d₁ d₂) a b g) :
    RootComponent (trace (pathShape d₁ d₂) g) (a+b+1) ∧
      ZeroOn (trace (pathShape d₁ d₂) g) (a+b+1) N := by
  let E := trace (pathShape d₁ d₂) g
  let φ := fun i => (coord d₁ d₂ i : ℤ)
  have hpos : 0 < N := by omega
  have hp : Function.Periodic E N := trace_periodic _ g
  have hbounds : ∀ i, 0 ≤ φ i ∧ φ i < (d₁ : ℤ)+d₂ := by
    intro i
    dsimp only [φ]
    refine ⟨Int.natCast_nonneg _,?_⟩
    exact_mod_cast coord_bound (show 0 < d₁+d₂ by omega) i
  have hcoord := trace_coordinate_step h₁ h₂ hN g
  have hneg : debt E N ≤ 0 := by
    have hd := KroneckerSourceIntervalCounts.debt_interval E 0 N (Nat.zero_le _)
    have hh : hWeight E 0 N=(b : ℤ) := (hWeight_total _ g).trans ht.2.1
    have hv : KroneckerSourceIntervalCounts.vCount E 0 N=(d₂ : ℤ) := by
      rw [vCount_edges,hN,(path_dimensions h₁ h₂).2]
    have hz : debt E 0=0 := rfl
    omega
  have hcost : cost E d₁ d₂ 0 N=1 := by
    dsimp [cost,E]
    rw [hWeight_total,vWeight_total,ht.2.1,ht.2.2.1]
    nlinarith [hdet]
  obtain ⟨c,u,e,hc,he,hu,hf,hcu,hce,hpre,hpost⟩ :=
    one_cyclic_block hpos hp (show (0 : ℤ)<d₂ by exact_mod_cast h₂)
      hcoord hbounds ht.1 ht.2.2.2 hneg hcost
  have hcop : d₁.Coprime d₂ := by
    exact_mod_cast KroneckerFrame.defect_one_coprime hdet
  have hstart : (c+u)%N=0 := by
    apply coordinate_injective hcop (by rw [← hN]; exact Nat.mod_lt _ hpos) (by omega)
    rw [hN,coord_mod]
    change (coord d₁ d₂ (c+u) : ℤ)=0 at hcu
    have hzero : coord d₁ d₂ (c+u)=0 := by exact_mod_cast hcu
    simpa [coord] using hzero
  have hend : (c+e)%N=a+b := by
    apply coordinate_injective hcop (by rw [← hN]; exact Nat.mod_lt _ hpos) (by omega)
    rw [hN,coord_mod,frame_last_coordinate h₁ h₂ hdet]
    have hlast : (coord d₁ d₂ (c+e) : ℤ)=(d₁ : ℤ)+d₂-1 := hce
    omega
  obtain ⟨hcut,hlen⟩ := shifted_block_indices hpos hc he hf.1
    (show a+b<N by omega) hstart hend
  exact ⟨unshift_root hp hcut hlen hu hf, unshift_zero hp hc he hcut hlen hpre hpost⟩

theorem natural_tight_position {N a b d₁ d₂ : ℕ}
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (hN : N=d₁+d₂)
    (ha : a < d₁) (hb : b < d₂)
    (hdet : (b : ℤ)*d₁-(a : ℤ)*d₂=1)
    (g : Fin N → ℕ)
    (ht : KroneckerSourceNaturalGradings.NaturalTight (pathShape d₁ d₂) a b g) :
    RootComponent (KroneckerSourceNaturalGradings.naturalTrace (pathShape d₁ d₂) g) (a+b+1) ∧
      ZeroOn (KroneckerSourceNaturalGradings.naturalTrace (pathShape d₁ d₂) g) (a+b+1) N := by
  let d := KroneckerSourceNaturalGradings.cap ht
  have hd := KroneckerSourceNaturalGradings.cap_tight ht
  have hcolored := (source_tight_iff_representative (pathShape d₁ d₂) a b d).mp hd
  have h := tight_position h₁ h₂ hN ha hb hdet (KroneckerWeights.representative d) hcolored
  rw [← raw_eq_representative] at h
  exact h

open KroneckerFrameIdentity KroneckerWeights KroneckerSourceParameterGates

theorem located (p : Parameters) {g : Coloring p.m (ambientLength p)}
    (ht : Tight (frameShape p) p.a p.b g) :
    LocatedTight (n := frameLength p) (k := p.k) (frameShape p) p.a p.b g := by
  have h := tight_position (source_hypotheses p).2.2.1
    (source_hypotheses p).2.2.2.1 p.length_eq p.hd₁ p.hd₂ p.determinant g ht
  refine ⟨ht,h.1,?_⟩
  intro j
  have hz := h.2 (Fin.natAdd (frameLength p) j).val (by simp [frameLength])
    (Fin.natAdd (frameLength p) j).isLt
  rw [trace_before _ _ _ (Fin.natAdd _ j).isLt,paint_grade] at hz
  exact hz

theorem source_position (p : Parameters) {g : Coloring p.m (ambientLength p)}
    (ht : Tight (frameShape p) p.a p.b g) : SourcePosition p (trace (frameShape p) g) := by
  have h := tight_position (source_hypotheses p).2.2.1
    (source_hypotheses p).2.2.2.1 p.length_eq p.hd₁ p.hd₂ p.determinant g ht
  have hr := (root_iff_first_return _ _).mp h.1
  refine ⟨0,p.a+p.b,by have := p.ha; dsimp [ambientLength,frameLength]; omega,
    by dsimp [ambientLength,frameLength]; omega,by simp [coord],
    frame_last_coordinate (source_hypotheses p).2.2.1 (source_hypotheses p).2.2.2.1 p.determinant,
    hr.2.1,?_,?_,?_⟩
  · simpa only [Nat.zero_le,ite_true,debt,walk] using hr.2.2.1
  · simpa only [Nat.zero_le,ite_true,debt,walk] using hr.2.2.2
  · intro j hj hout
    simp only [Nat.zero_le,ite_true,true_and,not_le] at hout
    exact h.2 j (by omega) hj

theorem tight_count_frame (p : Parameters) :
    Nat.card {g : Coloring p.m (ambientLength p) // Tight (frameShape p) p.a p.b g} =
      Nat.card {g : Coloring p.m (frameLength p) // Connected p.m (word (frameShape p) g) 0} := by
  have hcounts := frame_edge_counts (source_hypotheses p).2.2.1
    (source_hypotheses p).2.2.2.1 p.determinant
  have hframe := frame_count (m := p.m) (n := frameLength p) (k := p.k)
    (frameShape p) p.a p.b hcounts.1 hcounts.2
  have heq : ∀ g : Coloring p.m (ambientLength p),
      Tight (frameShape p) p.a p.b g ↔
        LocatedTight (n := frameLength p) (k := p.k) (frameShape p) p.a p.b g :=
    fun _ => ⟨located p,fun h => h.1⟩
  exact (Nat.card_congr (Equiv.subtypeEquivRight heq)).trans hframe.symm

theorem weighted_frame_count (p : Parameters) :
    weightedCount (fun d : Grades p.m (ambientLength p) =>
      Tight (frameShape p) p.a p.b (representative d)) =
      Nat.card {g : Coloring p.m (frameLength p) // Connected p.m (word (frameShape p) g) 0} := by
  rw [← tight_count_weighted]
  exact tight_count_frame p

end KroneckerDirectCoprimePosition
