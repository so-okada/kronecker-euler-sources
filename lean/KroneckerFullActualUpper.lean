import KroneckerSampledPeriodicLimit
import KroneckerSparseGoodPartition
import KroneckerPeriodicGrowth
import KroneckerRationalFrameLower
import KroneckerEventualFramePhase

section

/- Original module: KroneckerCompletionDensity -/
section
/-! A sublinear bad-window budget gives a sublinear completion deficit and the correct period density. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerCompletionDensity

theorem completion_deficit_density (q : ℕ) (a B t : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hB : Tendsto (fun n => (B n : ℝ)/(a n : ℝ)) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, a n ≤ t n*q ∧ t n*q ≤ a n+2*q*(B n+1)) :
    Tendsto (fun n => ((t n*q-a n : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 0) := by
  have hone : Tendsto (fun n => (1 : ℝ)/(a n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  have hup : Tendsto (fun n => ((2*q*(B n+1) : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 0) := by
    have h := (hB.add hone).const_mul (2*(q : ℝ))
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_add,
      add_div,mul_div_assoc,add_zero,mul_zero] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall (fun n => by positivity)
  · filter_upwards [hbound] with n hn
    have h : t n*q-a n ≤ 2*q*(B n+1) := by omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem completion_period_density (q : ℕ) (hq : 0 < q) (a B t : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hB : Tendsto (fun n => (B n : ℝ)/(a n : ℝ)) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, a n ≤ t n*q ∧ t n*q ≤ a n+2*q*(B n+1)) :
    Tendsto (fun n => (t n : ℝ)/(a n : ℝ)) atTop (𝓝 (1/(q : ℝ))) := by
  have hK := completion_deficit_density q a B t ha hB hbound
  have hself : Tendsto (fun n => (a n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Nat.sub_zero] using KroneckerShiftedBlockDensity.sub_height_ratio a ha 0
  have h := (hself.add hK).div_const (q : ℝ)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [hbound,ha.eventually (eventually_ge_atTop 1)] with n hn han
  have ha0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (show a n ≠ 0 by omega)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have he : (a n : ℝ)+((t n*q-a n : ℕ) : ℝ)=(t n : ℝ)*(q : ℝ) := by
    exact_mod_cast (show a n+(t n*q-a n)=t n*q by omega)
  field_simp
  nlinarith

end KroneckerCompletionDensity
end

/- Original module: KroneckerPaddedPeriodDensity -/
section
/-! All prescribed collars and the fixed terminal repair have zero normalized cost. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPaddedPeriodDensity
open KroneckerCompletionPadding KroneckerCompletionDensity

theorem completion_index_density (m q : ℕ) (hq : 0 < q) (a B t : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hB : Tendsto (fun n => (B n : ℝ)/(a n : ℝ)) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, a n ≤ t n*q ∧ t n*q ≤ a n+2*q*(B n+1)) :
    Tendsto (fun n => (completionIndex m q (a n) (t n) : ℝ)/(a n : ℝ))
      atTop (𝓝 (1/(q : ℝ))) := by
  have ht := completion_period_density q hq a B t ha hB hbound
  have hK := completion_deficit_density q a B t ha hB hbound
  have hconst : Tendsto (fun n => ((2+2*(2*q+m) : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  have h := (ht.add (hK.const_mul 2)).add hconst
  simp only [mul_zero,add_zero] at h
  convert h using 1
  ext n
  simp only [completionIndex,completionPadding,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem completion_index_shift_density (m q : ℕ) (hq : 0 < q) (a B t : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hB : Tendsto (fun n => (B n : ℝ)/(a n : ℝ)) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, a n ≤ t n*q ∧ t n*q ≤ a n+2*q*(B n+1)) :
    Tendsto (fun n => ((completionIndex m q (a n) (t n) : ℝ)+2)/(a n : ℝ))
      atTop (𝓝 (1/(q : ℝ))) := by
  have hc : Tendsto (fun n => (2 : ℝ)/(a n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  simpa only [add_div,add_zero] using (completion_index_density m q hq a B t ha hB hbound).add hc

end KroneckerPaddedPeriodDensity
end
end

section

/-! Strictly interior rational slopes have an insertion-admissible first run. -/
set_option autoImplicit false
namespace KroneckerRationalHeadBound
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerRationalWordRotation

theorem initial_run_floor (s : ℝ) : natRun s 0 0=⌊s⌋₊ := by
  simp [natRun,mechanicalRun,mechanicalPrefix,Int.floor_toNat]

theorem rational_head_bound (m p q : ℕ) (hq : 0 < q)
    (hlo : 1 ≤ (p : ℝ)/(q : ℝ)) (hhi : (p : ℝ)/(q : ℝ) < (m-1 : ℕ)) :
    ∃ u V, rationalPeriod p q=u::V ∧ u+2 ≤ m := by
  have hs : 0 ≤ (p : ℝ)/(q : ℝ) := le_trans (by norm_num) hlo
  have hb : ⌊(p : ℝ)/(q : ℝ)⌋₊ < m-1 := (Nat.floor_lt hs).mpr hhi
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  simp only [rationalPeriod,mechanicalWord,List.ofFn_succ,Nat.zero_add,Fin.val_zero]
  rw [initial_run_floor]
  exact ⟨_,_,rfl,by omega⟩

end KroneckerRationalHeadBound
end

section

/- Original module: KroneckerAsymmetricInsertion -/
section
/-! The literal insertion map needs a stronger bound only on the left shell. -/
set_option autoImplicit false
namespace KroneckerAsymmetricInsertion
open KroneckerStack KroneckerWordCounts KroneckerInsertionPalette
open KroneckerInsertionColorConnected KroneckerInsertionColorRecovery

def asymmetricInsertion {m : ℕ} (u v i c : ℕ) (hu : u+2 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool)
    (hi : 1 ≤ i ∧ i ≤ U.length) :
    ConnectedColorings m U c → ConnectedColorings m (insertedPath u v i U) c :=
  fun g => ⟨insertionColoring u v i hu hv hm hpos U g.val,
    insertionColoring_connected u v i c hu hv hm hpos U hi g.val g.property⟩

theorem asymmetric_injective {m : ℕ} (u v i c : ℕ) (hu : u+2 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool)
    (hi : 1 ≤ i ∧ i ≤ U.length) :
    Function.Injective (asymmetricInsertion u v i c hu hv hm hpos U hi) := by
  intro x y hxy
  apply Subtype.ext
  exact insertionColoring_injective u v i hu hv hm hpos U hi.2 (congrArg Subtype.val hxy)

theorem asymmetric_path_count {m : ℕ} (u v i c : ℕ) (hu : u+2 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool)
    (hi : 1 ≤ i ∧ i ≤ U.length) :
    pathCount m U c ≤ pathCount m (insertedPath u v i U) c := by
  classical
  simp only [pathCount,Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective (asymmetricInsertion u v i c hu hv hm hpos U hi)
    (asymmetric_injective u v i c hu hv hm hpos U hi)

end KroneckerAsymmetricInsertion
end

/- Original module: KroneckerAsymmetricRunRise -/
section
/-! Increase any selected run using the exact asymmetric shell hypotheses. -/
set_option autoImplicit false
namespace KroneckerAsymmetricRunRise
open KroneckerStack KroneckerWordCounts KroneckerInsertionPalette
open KroneckerAsymmetricInsertion KroneckerVerticalInsertionRuns

theorem asymmetric_run_rise {m : ℕ} (u v c r : ℕ) (hu : u+2 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (pre post : List ℕ) :
    runCount m (pre++r::post) c ≤ runCount m (u::(pre++(r+1)::post)++[v]) c := by
  have hi : 1 ≤ (runWord pre).length+1 ∧
      (runWord pre).length+1 ≤ (runWord (pre++r::post)).length := by
    constructor
    · omega
    · simp [runWord,runShape]
  have h := asymmetric_path_count u v ((runWord pre).length+1) c hu hv hm hpos
    (runWord (pre++r::post)) hi
  unfold insertedPath at h
  rw [insert_runWord] at h
  simpa [runCount,runWord,List.append_assoc] using h

end KroneckerAsymmetricRunRise
end

/- Original module: KroneckerPeriodCollarIdentity -/
section
/-! Exact order of the left and right period collars under iteration. -/
set_option autoImplicit false
namespace KroneckerPeriodCollarIdentity
open KroneckerPeriodicWords

theorem collar_succ (W X : List ℕ) (k : ℕ) :
    W++(repeatRuns W k++X++repeatRuns W k)++W =
      repeatRuns W (k+1)++X++repeatRuns W (k+1) := by
  calc
    _ = (W++repeatRuns W k)++X++(repeatRuns W k++W) := by simp only [List.append_assoc]
    _ = _ := by rw [←repeatRuns_succ_left]; rfl


end KroneckerPeriodCollarIdentity
end

/- Original module: KroneckerPeriodInnerCollars -/
section
/-! Removing opposite endpoints of one period leaves equal legal inner collars. -/
set_option autoImplicit false
namespace KroneckerPeriodInnerCollars

theorem inner_collar_lengths (u v : ℕ) (T : List ℕ) : (T++[v]).length=(u::T).length := by simp

theorem inner_collars_legal {m u v : ℕ} (T : List ℕ)
    (hW : ∀ r ∈ u::(T++[v]), 1 ≤ r ∧ r ≤ m-1) :
    (∀ r ∈ T++[v], 1 ≤ r ∧ r ≤ m-1) ∧
      (∀ r ∈ u::T, 1 ≤ r ∧ r ≤ m-1) := by
  constructor
  · intro r hr
    exact hW r (by simp [hr])
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hW r (by simp)
    · exact hW r (by simp [hr])

end KroneckerPeriodInnerCollars
end

/- Original module: KroneckerPeriodRunRise -/
section
/-! One vertical insertion can consume whole periods as its two collars. -/
set_option autoImplicit false
namespace KroneckerPeriodRunRise
open KroneckerWordCounts KroneckerPreservingCollars KroneckerAsymmetricRunRise
open KroneckerPeriodInnerCollars

theorem period_run_rise {m u v : ℕ} (hm : 3 ≤ m) (T : List ℕ)
    (hW : ∀ r ∈ u::(T++[v]), 1 ≤ r ∧ r ≤ m-1) (hu : u+2 ≤ m)
    (pre post : List ℕ) (r c : ℕ) :
    runCount m (pre++r::post) c ≤
      runCount m ((u::(T++[v]))++(pre++(r+1)::post)++(u::(T++[v]))) c := by
  have hlegal := inner_collars_legal T hW
  have hv := hW v (by simp)
  have h₁ := preserving_collars m hm (T++[v]) (u::T) (inner_collar_lengths u v T)
    hlegal.1 hlegal.2 (pre++r::post) c
  have h₂ := asymmetric_run_rise u v c r hu (by omega) (by omega) hv.1
    ((T++[v])++pre) (post++(u::T))
  have h₁' : runCount m (pre++r::post) c ≤
      runCount m (((T++[v])++pre)++r::(post++(u::T))) c := by
    simpa only [List.append_assoc,List.cons_append] using h₁
  simpa only [List.append_assoc,List.cons_append] using h₁'.trans h₂

end KroneckerPeriodRunRise
end

/- Original module: KroneckerRepeatedPeriodRise -/
section
/-! Raise a selected run by A using A whole-period collar layers. -/
set_option autoImplicit false
namespace KroneckerRepeatedPeriodRise
open KroneckerWordCounts KroneckerPeriodicWords KroneckerPeriodRunRise
open KroneckerPeriodCollarIdentity

theorem repeated_period_rise {m u v : ℕ} (hm : 3 ≤ m) (T : List ℕ)
    (hW : ∀ r ∈ u::(T++[v]), 1 ≤ r ∧ r ≤ m-1) (hu : u+2 ≤ m)
    (pre post : List ℕ) (r c A : ℕ) :
    runCount m (pre++r::post) c ≤
      runCount m (repeatRuns (u::(T++[v])) A++(pre++(r+A)::post)++
        repeatRuns (u::(T++[v])) A) c := by
  let W := u::(T++[v])
  induction A with
  | zero => simp [repeatRuns]
  | succ A ih =>
    have h := period_run_rise hm T hW hu (repeatRuns W A++pre)
      (post++repeatRuns W A) (r+A) c
    have h' : runCount m (repeatRuns W A++(pre++(r+A)::post)++repeatRuns W A) c ≤
        runCount m (W++(repeatRuns W A++(pre++(r+(A+1))::post)++repeatRuns W A)++W) c := by
      simpa only [W,List.append_assoc,List.cons_append,Nat.add_assoc] using h
    rw [collar_succ] at h'
    exact ih.trans h'

end KroneckerRepeatedPeriodRise
end
end

section

/-! Reserve A whole periods for marker repair and drain the surplus with the rest. -/
set_option autoImplicit false
namespace KroneckerWholePeriodBudget
open KroneckerCompletionPadding

theorem marker_padding_le (m q K A : ℕ) (hA : A ≤ m) :
    A ≤ completionPadding m q K := by unfold completionPadding; omega

theorem remaining_period_budget (m q K L A : ℕ) (hq : 1 ≤ q)
    (hL : L ≤ 2*q) (hA : A ≤ m) :
    K+L ≤ (completionPadding m q K-A)*q := by
  have h : K+L ≤ completionPadding m q K-A := by unfold completionPadding; omega
  exact h.trans (Nat.le_mul_of_pos_right _ hq)

theorem padded_index_recombines (t j A : ℕ) (hA : A ≤ j) :
    (j-A)+(t+2+2*A)+(j-A)=t+2+2*j := by omega

end KroneckerWholePeriodBudget
end

section

/- Original module: KroneckerDrainingCollars -/
section
/-! Arbitrary prescribed equal-length collars remove up to one surplus unit
per layer; all remaining layers preserve surplus zero. -/
set_option autoImplicit false
namespace KroneckerDrainingCollars
open KroneckerWordCounts KroneckerColoredShell KroneckerDrainingShell

theorem draining_collars (m : ℕ) (hm : 3 ≤ m) (A : List ℕ) :
    ∀ (B : List ℕ), A.length = B.length →
      (∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) → (∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) →
      ∀ (rs : List ℕ) (c : ℕ),
      runCount m rs c ≤ runCount m (A ++ rs ++ B) (c-A.length) := by
  induction A with
  | nil =>
    intro B hlen _ _ rs c
    have hB : B = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    simp [hB]
  | cons u A ih =>
    intro B hlen hA hB rs c
    have hu := hA u (by simp)
    have hBne : B ≠ [] := by intro h; subst B; simp at hlen
    obtain ⟨Bs, v, htail⟩ : ∃ Bs v, B = Bs ++ [v] :=
      ⟨B.dropLast, B.getLast hBne, (List.dropLast_append_getLast hBne).symm⟩
    subst B
    have hv := hB v (by simp)
    have hsize : A.length = Bs.length := by simp at hlen; omega
    have hinner := ih Bs hsize (fun r h => hA r (by simp [h]))
      (fun r h => hB r (by simp [h])) rs c
    by_cases hc : c ≤ A.length
    · have hz : c-A.length = 0 := by omega
      have hz' : c-(A.length+1) = 0 := by omega
      have houter := unary_runCount_le u v 0 hm hu hv (A ++ rs ++ Bs)
      have hinner0 : runCount m rs c ≤ runCount m (A ++ rs ++ Bs) 0 := by
        simpa [hz] using hinner
      simpa [List.append_assoc, hz'] using hinner0.trans houter
    · have hpos : 1 ≤ c-A.length := by omega
      have houter := draining_runCount_le u v (c-A.length) hm hu hv hpos (A ++ rs ++ Bs)
      have hsub : c-A.length-1 = c-(u::A).length := by simp; omega
      simpa [List.append_assoc, hsub] using hinner.trans houter

theorem zero_surplus_collars (m : ℕ) (hm : 3 ≤ m) (A B rs : List ℕ) (c : ℕ)
    (hlen : A.length = B.length) (hc : c ≤ A.length)
    (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) (hB : ∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) :
    runCount m rs c ≤ runCount m (A ++ rs ++ B) 0 := by
  simpa [Nat.sub_eq_zero_of_le hc] using draining_collars m hm A B hlen hA hB rs c

end KroneckerDrainingCollars
end

/- Original module: KroneckerFullPalettePrograms -/
section
/-! Complete-run programs retain the full range justified by the local map. -/
set_option autoImplicit false
namespace KroneckerFullPalettePrograms
open KroneckerCompleteRunPalette

inductive CompleteProgram (m : ℕ) (U : List Bool) : List Bool → ℕ → Type
  | nil : CompleteProgram m U U 0
  | step {V : List Bool} {K : ℕ} (p : CompleteProgram m U V K)
      (r i : ℕ) (hr : r ≤ m) (hi : i ≤ V.length) :
      CompleteProgram m U (completePath r i V) (K+1)

noncomputable def appendComplete {m : ℕ} {U V Z : List Bool} {K L : ℕ}
    (p : CompleteProgram m U V K) (q : CompleteProgram m V Z L) :
    CompleteProgram m U Z (K+L) := by
  induction q with
  | nil => simpa using p
  | step q r i hr hi ih => simpa [Nat.add_assoc] using CompleteProgram.step ih r i hr hi


end KroneckerFullPalettePrograms
end

/- Original module: KroneckerFullPaletteRunSteps -/
section
/-! Complete-run edits at run boundaries, including types m-1 and m. -/
set_option autoImplicit false
namespace KroneckerFullPaletteRunSteps
open KroneckerWordCounts KroneckerFullPalettePrograms KroneckerRunWordSplice

def insertComplete (m : ℕ) (pre post : List ℕ) (r : ℕ) (hr : r ≤ m) :
    CompleteProgram m (runWord (pre++post)) (runWord (pre++r::post)) 1 := by
  have hi : (runWord pre).length ≤ (runWord (pre++post)).length := by
    simp [runWord]
  simpa only [complete_runWord] using CompleteProgram.step CompleteProgram.nil r
    (runWord pre).length hr hi


end KroneckerFullPaletteRunSteps
end

/- Original module: KroneckerFullPaletteSublist -/
section
/-! Subsequence completion without the narrower vertical-edit alphabet. -/
set_option autoImplicit false
namespace KroneckerFullPaletteSublist
open KroneckerWordCounts KroneckerFullPalettePrograms KroneckerFullPaletteRunSteps

theorem sublist_complete {m : ℕ} {X Y : List ℕ} (h : X.Sublist Y)
    (hY : ∀ r ∈ Y, r ≤ m) (pre post : List ℕ) :
    Nonempty (CompleteProgram m (runWord (pre++X++post)) (runWord (pre++Y++post))
      (Y.length-X.length)) := by
  induction h generalizing pre with
  | slnil => exact ⟨CompleteProgram.nil⟩
  | @cons X Y r h ih =>
    have hr := hY r (by simp)
    have htail : ∀ s ∈ Y, s ≤ m := fun s hs => hY s (by simp [hs])
    obtain ⟨p⟩ := ih htail pre
    simp only [List.append_assoc] at p
    let q := insertComplete m pre (Y++post) r hr
    have hlen := h.length_le
    have he : Y.length-X.length+1=(r::Y).length-X.length := by simp only [List.length_cons]; omega
    exact ⟨by simpa only [List.append_assoc,List.cons_append,he] using appendComplete p q⟩
  | @cons_cons X Y r h ih =>
    have htail : ∀ s ∈ Y, s ≤ m := fun s hs => hY s (by simp [hs])
    obtain ⟨p⟩ := ih htail (pre++[r])
    exact ⟨by simpa only [List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_sub_add_right] using p⟩

end KroneckerFullPaletteSublist
end

/- Original module: KroneckerFullPaletteSurround -/
section
/-! Prescribed prefix and suffix completion with exact added-run cost. -/
set_option autoImplicit false
namespace KroneckerFullPaletteSurround
open KroneckerWordCounts KroneckerFullPalettePrograms KroneckerFullPaletteSublist

theorem surround_complete {m : ℕ} (X L R : List ℕ)
    (hL : ∀ r ∈ L, r ≤ m) (hR : ∀ r ∈ R, r ≤ m) :
    Nonempty (CompleteProgram m (runWord X) (runWord (L++X++R)) (L.length+R.length)) := by
  obtain ⟨p⟩ := sublist_complete (m:=m) (List.nil_sublist L) hL [] X
  obtain ⟨q⟩ := sublist_complete (m:=m) (List.nil_sublist R) hR (L++X) []
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.sub_zero] at p q
  exact ⟨appendComplete p q⟩

end KroneckerFullPaletteSurround
end

/- Original module: KroneckerFullCapProgram -/
section
/-! Complete the interior while retaining the terminal unit marker for a later repair. -/
set_option autoImplicit false
namespace KroneckerFullCapProgram
open KroneckerWordCounts KroneckerFullPalettePrograms KroneckerFullPaletteSublist
open KroneckerFullPaletteSurround KroneckerPeriodicWords

theorem full_cap_program {m u v : ℕ} (T X : List ℕ) (t : ℕ)
    (hW : ∀ r ∈ u::(T++[v]), r ≤ m)
    (hX : X.Sublist (repeatRuns (u::(T++[v])) t)) :
    Nonempty (CompleteProgram m (runWord (X++[1]))
      (runWord ((T++[v])++repeatRuns (u::(T++[v])) t++[1]++T))
      ((repeatRuns (u::(T++[v])) t).length-X.length+(2*T.length+1))) := by
  let W := u::(T++[v])
  have hrep : ∀ r ∈ repeatRuns W t, r ≤ m := fun r hr => hW r (mem_repeatRuns W t hr)
  have hL : ∀ r ∈ T++[v], r ≤ m := fun r hr => hW r (by simp [hr])
  have hT : ∀ r ∈ T, r ≤ m := fun r hr => hL r (by simp [hr])
  obtain ⟨p⟩ := sublist_complete hX hrep [] [1]
  obtain ⟨q⟩ := surround_complete (repeatRuns W t++[1]) (T++[v]) T hL hT
  exact ⟨by simpa [W,List.append_assoc,two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    using appendComplete p q⟩

end KroneckerFullCapProgram
end

/- Original module: KroneckerFullPaletteBufferCount -/
section
/-! Fixed nonempty buffers make every raw complete-run insertion internal. -/
set_option autoImplicit false
namespace KroneckerFullPaletteBufferCount
open KroneckerWordCounts KroneckerFullPalettePrograms KroneckerColoredShell
open KroneckerCollarColoring KroneckerMiddleContext KroneckerBufferedGaps
open KroneckerMiddleCompleteLift KroneckerCompleteRunInjection

theorem buffered_program_count {m : ℕ} {U V : List Bool} {K : ℕ}
    (p : CompleteProgram m U V K) (u v c : ℕ) :
    pathCount m (shellPath u v U) c ≤ pathCount m (shellPath u v V) (c+K) := by
  induction p with
  | nil => simp
  | @step V K p r i hr hi ih =>
    have hs := completeRun_count r ((leftContext [] u).length+i) (c+K) hr
      (collarPath [] (shellPath u v V)) (middle_complete_bounds [] u v V i hi)
    rw [complete_middle_path [] u v r i V hi] at hs
    simp only [collarPath] at hs
    simpa only [Nat.add_assoc] using ih.trans hs

end KroneckerFullPaletteBufferCount
end

/- Original module: KroneckerPeriodMarkerRaise -/
section
/-! Exact repair of the frame's unit marker to an arbitrary legal period head. -/
set_option autoImplicit false
namespace KroneckerPeriodMarkerRaise
open KroneckerWordCounts KroneckerPeriodicWords KroneckerRepeatedPeriodRise

theorem period_marker_raise {m u v : ℕ} (hm : 3 ≤ m) (T : List ℕ)
    (hW : ∀ r ∈ u::(T++[v]), 1 ≤ r ∧ r ≤ m-1) (hu : u+2 ≤ m)
    (pre post : List ℕ) (c : ℕ) :
    runCount m (pre++1::post) c ≤
      runCount m (repeatRuns (u::(T++[v])) (u-1)++(pre++u::post)++
        repeatRuns (u::(T++[v])) (u-1)) c := by
  have hp := (hW u (by simp)).1
  have he : 1+(u-1)=u := by omega
  simpa only [he] using repeated_period_rise hm T hW hu pre post 1 c (u-1)

end KroneckerPeriodMarkerRaise
end

/- Original module: KroneckerFullCapCount -/
section
/-! Repair the terminal marker with whole periods, retaining the exact surplus. -/
set_option autoImplicit false
namespace KroneckerFullCapCount
open KroneckerWordCounts KroneckerPeriodicWords KroneckerColoredShell
open KroneckerFullCapProgram KroneckerFullPaletteBufferCount KroneckerPeriodMarkerRaise
open KroneckerPeriodicCapIdentity

theorem full_cap_count {m u v : ℕ} (hm : 3 ≤ m) (T X : List ℕ) (t : ℕ)
    (hW : ∀ r ∈ u::(T++[v]), 1 ≤ r ∧ r ≤ m-1) (hu : u+2 ≤ m)
    (hX : X.Sublist (repeatRuns (u::(T++[v])) t)) :
    runCount m (X++[1]) 0 ≤ runCount m
      (repeatRuns (u::(T++[v])) (t+2+2*(u-1)))
      (t*(u::(T++[v])).length-X.length+(2*T.length+1)) := by
  let W := u::(T++[v])
  have hulegal := hW u (by simp)
  have hvlegal := hW v (by simp)
  obtain ⟨p⟩ := full_cap_program (m:=m) T X t
    (fun r hr => (hW r hr).2.trans (by omega)) hX
  have hbuffer := unary_runCount_le u v 0 hm hulegal hvlegal (X++[1])
  have hmiddle := buffered_program_count p u v 0
  simp only [shellPath_runWord,Nat.zero_add,repeatRuns_length] at hmiddle
  have hraise := period_marker_raise hm T hW hu
    (u::((T++[v])++repeatRuns W t)) (T++[v])
    (t*W.length-X.length+(2*T.length+1))
  have hraise' : runCount m (u::((T++[v])++repeatRuns W t++[1]++T)++[v])
      (t*W.length-X.length+(2*T.length+1)) ≤
      runCount m (repeatRuns W (u-1)++
        (u::((T++[v])++repeatRuns W t++[u]++T)++[v])++repeatRuns W (u-1))
        (t*W.length-X.length+(2*T.length+1)) := by
    simpa only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using hraise
  rw [cap_identity] at hraise'
  exact hbuffer.trans (hmiddle.trans hraise')

end KroneckerFullCapCount
end

/- Original module: KroneckerFullSplitUpper -/
section
/-! Actual periodic upper comparison for the full legal alphabet. -/
set_option autoImplicit false
namespace KroneckerFullSplitUpper
open KroneckerWordCounts KroneckerPeriodicWords KroneckerFullCapCount
open KroneckerCompletionPadding KroneckerWholePeriodBudget KroneckerDrainingCollars

theorem full_split_upper {m u v : ℕ} (hm : 3 ≤ m) (T X : List ℕ) (t : ℕ)
    (hW : ∀ r ∈ u::(T++[v]), 1 ≤ r ∧ r ≤ m-1) (hu : u+2 ≤ m)
    (hX : X.Sublist (repeatRuns (u::(T++[v])) t)) :
    runCount m (X++[1]) 0 ≤ periodicCount m (u::(T++[v]))
      (completionIndex m (u::(T++[v])).length X.length t) := by
  let W := u::(T++[v])
  let K := t*W.length-X.length
  let A := u-1
  let j := completionPadding m W.length K
  have hq : 1 ≤ W.length := by simp [W]
  have hL : 2*T.length+1 ≤ 2*W.length := by simp [W]
  have hA : A ≤ m := by dsimp [A]; omega
  have hAj : A ≤ j := marker_padding_le m W.length K A hA
  have hbudget := remaining_period_budget m W.length K (2*T.length+1) A hq hL hA
  have hrep : ∀ r ∈ repeatRuns W (j-A), 1 ≤ r ∧ r ≤ m-1 :=
    fun r hr => hW r (mem_repeatRuns W (j-A) hr)
  have hsource := full_cap_count hm T X t hW hu hX
  have hfinal := zero_surplus_collars m hm (repeatRuns W (j-A)) (repeatRuns W (j-A))
    (repeatRuns W (t+2+2*A)) (K+(2*T.length+1)) rfl
    (by simpa only [repeatRuns_length] using hbudget) hrep hrep
  rw [←repeatRuns_add,←repeatRuns_add,padded_index_recombines t j A hAj] at hfinal
  exact hsource.trans hfinal

end KroneckerFullSplitUpper
end

/- Original module: KroneckerFullPeriodicUpper -/
section
/-! Endpoint-free finite comparison for the full legal alphabet and an admissible head. -/
set_option autoImplicit false
namespace KroneckerFullPeriodicUpper
open KroneckerWordCounts KroneckerPeriodicWords KroneckerCompletionPadding
open KroneckerFullSplitUpper KroneckerPeriodEndpoints

theorem full_periodic_upper {m : ℕ} (hm : 3 ≤ m) (W X : List ℕ) (t : ℕ)
    (hq : 2 ≤ W.length) (hhead : ∃ u V, W=u::V ∧ u+2 ≤ m)
    (hW : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1)
    (hX : X.Sublist (repeatRuns W t)) :
    runCount m (X++[1]) 0 ≤ periodicCount m W (completionIndex m W.length X.length t) := by
  obtain ⟨a,V,rfl,ha⟩ := hhead
  obtain ⟨u,v,T,h⟩ := period_endpoints (a::V) hq
  have hu : u=a := (List.cons.inj h).1.symm
  subst u
  rw [h] at hW hX ⊢
  exact full_split_upper hm T X t hW ha hX

end KroneckerFullPeriodicUpper
end

/- Original module: KroneckerFullPiecesUpper -/
section
/-! The number of periodic pieces explicitly bounds the finite count comparison length. -/
set_option autoImplicit false
namespace KroneckerFullPiecesUpper
open KroneckerWordCounts KroneckerPeriodicWords KroneckerPhasePieces
open KroneckerPiecesCompletion KroneckerFullPeriodicUpper KroneckerCompletionPadding

theorem full_pieces_upper {m : ℕ} (hm : 3 ≤ m) (W : List ℕ) (pieces : List (List ℕ))
    (hq : 2 ≤ W.length) (hhead : ∃ u V, W=u::V ∧ u+2 ≤ m) (hW : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1)
    (hpieces : ∀ X ∈ pieces, PhasePiece W X) :
    ∃ t, pieces.flatten.length ≤ t*W.length ∧
      t*W.length ≤ pieces.flatten.length+2*W.length*pieces.length ∧
      runCount m (pieces.flatten++[1]) 0 ≤
        periodicCount m W (completionIndex m W.length pieces.flatten.length t) := by
  obtain ⟨t,ht,hbound⟩ := pieces_completion W pieces hpieces
  have hlen := ht.length_le
  rw [repeatRuns_length] at hlen
  exact ⟨t,hlen,hbound,full_periodic_upper hm W pieces.flatten t hq hhead hW ht⟩

end KroneckerFullPiecesUpper
end

/- Original module: KroneckerFullGoodPartition -/
section
/-! A literal partition into good intervals yields a count bound with explicit overhead. -/
set_option autoImplicit false
namespace KroneckerFullGoodPartition
open KroneckerMechanicalWords KroneckerGoodIntervals KroneckerGoodIntervalPhasePiece
open KroneckerFullPiecesUpper KroneckerRationalHeadBound KroneckerGoodPartitionUpper KroneckerRationalWordRotation KroneckerRationalPeriodAlphabet
open KroneckerWordCounts KroneckerPeriodicWords KroneckerCompletionPadding

theorem full_good_partition_upper {m : ℕ} (hm : 3 ≤ m) (p q : ℕ)
    (hq : 1 < q) (hc : p.Coprime q) (s u : ℝ) (start n : ℕ) (parts : List (ℕ×ℕ))
    (hlo : 1 ≤ (p : ℝ)/(q : ℝ)) (hhi : (p : ℝ)/(q : ℝ) < (m-1 : ℕ))
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2)
    (hparts : GoodPartition s u (p : ℤ) q start n parts) :
    ∃ t, n ≤ t*q ∧ t*q ≤ n+2*q*parts.length ∧
      runCount m (mechanicalWord s u start n++[1]) 0 ≤
        periodicCount m (rationalPeriod p q) (completionIndex m q n t) := by
  let words := parts.map (fun z => mechanicalWord s u z.1 z.2)
  have hflat : words.flatten=mechanicalWord s u start n := by
    simpa only [words,List.flatMap] using hparts.1
  have hp : ∀ X ∈ words, KroneckerPhasePieces.PhasePiece (rationalPeriod p q) X := by
    intro X hX
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hX
    exact good_interval_phase_piece p q hq hc s u z.1 z.2 hs (hparts.2 z hz)
  have h := full_pieces_upper hm (rationalPeriod p q) words
    (by rw [rationalPeriod_length]; omega) (rational_head_bound m p q (by omega) hlo hhi)
      (rationalPeriod_legal p q (m-1) hlo hhi.le) hp
  simpa only [hflat,mechanicalWord_length,rationalPeriod_length,words,List.length_map] using h

end KroneckerFullGoodPartition
end

/- Original module: KroneckerFullMechanicalUpper -/
section
/-! Actual rational finite upper comparison: sparse partition and all insertions are proved. -/
set_option autoImplicit false
namespace KroneckerFullMechanicalUpper
open KroneckerMechanicalWords KroneckerWordCounts KroneckerPeriodicWords
open KroneckerRationalWordRotation KroneckerCompletionPadding KroneckerFullGoodPartition
open KroneckerIntervalBadStarts KroneckerSparseGoodPartition KroneckerBadWindowBounds

theorem full_mechanical_upper {m : ℕ} (hm : 3 ≤ m) (p q : ℕ)
    (hq : 1 < q) (hc : p.Coprime q) (s u : ℝ) (n : ℕ)
    (hlo : 1 ≤ (p : ℝ)/(q : ℝ)) (hhi : (p : ℝ)/(q : ℝ) < (m-1 : ℕ))
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    ∃ t, n ≤ t*q ∧ t*q ≤ n+2*q*(badWindows s u (p : ℤ) q (n+1-q)+1) ∧
      runCount m (mechanicalWord s u 0 n++[1]) 0 ≤
        periodicCount m (rationalPeriod p q) (completionIndex m q n t) := by
  obtain ⟨parts,hparts,hcount⟩ := sparse_good_partition s u (p : ℤ) q 0 n hq
  obtain ⟨t,htlo,hthi,htcount⟩ := full_good_partition_upper hm p q hq hc s u 0 n parts hlo hhi hs hparts
  rw [interval_bad_origin] at hcount
  refine ⟨t,htlo,?_,htcount⟩
  exact hthi.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (2*q) hcount) n)

end KroneckerFullMechanicalUpper
end

/- Original module: KroneckerPeriodicUpperAsymptotic -/
section
/-! Actual periodic domination gives upper logarithmic limits, including a zero source count. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPeriodicUpperAsymptotic
open KroneckerPeriodicWords KroneckerPeriodicTail KroneckerPeriodicGrowth KroneckerPeriodicLog

theorem log_periodic_domination (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hW : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (C j : ℕ) (hj : 1 ≤ j)
    (hC : C ≤ periodicCount m W j) :
    Real.log (C : ℝ) ≤ periodicGrowth m W*((j : ℝ)+2) := by
  by_cases hzero : C=0
  · subst C
    simp only [Nat.cast_zero,Real.log_zero]
    exact mul_nonneg (periodicGrowth_pos m hm W hne hW).le (by positivity)
  · have hp : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
    have hlog := Real.log_le_log hp (show (C : ℝ) ≤ (periodicCount m W j : ℝ) by exact_mod_cast hC)
    have hbound := (div_le_iff₀ (show (0 : ℝ) < (j : ℝ)+2 by positivity)).mp
      (periodicRatio_le_growth m hm W hne hW j hj)
    exact hlog.trans hbound

theorem eventual_periodic_upper (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hW : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (q : ℕ) (a C j : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hdensity : Tendsto (fun n => ((j n : ℝ)+2)/(a n : ℝ)) atTop (𝓝 (1/(q : ℝ))))
    (hcompare : ∀ᶠ n in atTop, 1 ≤ j n ∧ C n ≤ periodicCount m W (j n)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      Real.log (C n : ℝ)/(a n : ℝ) ≤ periodicGrowth m W/(q : ℝ)+ε := by
  have hlim := hdensity.const_mul (periodicGrowth m W)
  simp only [mul_one_div] at hlim
  intro ε hε
  filter_upwards [(tendsto_order.1 hlim).2 (periodicGrowth m W/(q : ℝ)+ε) (by linarith),
    hcompare,ha.eventually (eventually_ge_atTop 1)] with n hn hcomp han
  have h := div_le_div_of_nonneg_right (log_periodic_domination m hm W hne hW (C n) (j n) hcomp.1 hcomp.2)
    (show (0 : ℝ) ≤ a n by positivity)
  rw [mul_div_assoc] at h
  exact h.trans hn.le

end KroneckerPeriodicUpperAsymptotic
end

/- Original module: KroneckerFullActualUpper -/
section
/-! The rational upper bound uses the actual sparse partition and actual coloring maps. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFullActualUpper
open KroneckerFullMechanicalUpper KroneckerCompletionPadding KroneckerPaddedPeriodDensity
open KroneckerPeriodicUpperAsymptotic KroneckerRationalWordRotation KroneckerRationalPeriodAlphabet
open KroneckerWordCounts KroneckerPeriodicWords KroneckerPeriodicTail KroneckerBadWindowBounds
open KroneckerFrameSlope KroneckerFrameSlopeLimit KroneckerFrameBadDensity
open KroneckerRationalFrameLower KroneckerEventualPhaseNeighborhood

theorem full_frame_dominated_upper (m p q : ℕ) (hm : 3 ≤ m) (hq : 1 < q)
    (hc : p.Coprime q) (hlo : 1 ≤ (p : ℝ)/(q : ℝ))
    (hhi : (p : ℝ)/(q : ℝ) < (m-1 : ℕ)) (a b d C : ℕ → ℕ)
    (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 ((p : ℝ)/(q : ℝ))))
    (hC : ∀ᶠ n in atTop, C n ≤ runCount m (frameWord (a n) (b n) (d n)) 0) :
    ∀ ε > 0, ∀ᶠ n in atTop, Real.log (C n : ℝ)/(a n : ℝ) ≤
      periodicGrowth m (rationalPeriod p q)/(q : ℝ)+ε := by
  classical
  let B := fun n => badWindows (frameSlope (a n) (b n) (d n)) 0 (p : ℤ) q (a n+1-q)
  let Q := fun n t => a n ≤ t*q ∧ t*q ≤ a n+2*q*(B n+1) ∧
    C n ≤ periodicCount m (rationalPeriod p q) (completionIndex m q (a n) t)
  have hnear := eventually_phase_neighborhood (fun n => frameSlope (a n) (b n) (d n)) p q
    (by omega) (frame_slope_limit a b d _ ha hd hr)
  have hex : ∀ᶠ n in atTop, ∃ t, Q n t := by
    filter_upwards [hnear,hC] with n hn hcn
    obtain ⟨t,htlo,hthi,htcount⟩ := full_mechanical_upper hm p q hq hc
      (frameSlope (a n) (b n) (d n)) 0 (a n) hlo hhi hn
    exact ⟨t,htlo,hthi,hcn.trans htcount⟩
  let t := fun n => if h : ∃ t, Q n t then Classical.choose h else 0
  have ht : ∀ᶠ n in atTop, Q n (t n) := by
    filter_upwards [hex] with n hn
    simpa only [t,dite_eq_left hn] using Classical.choose_spec hn
  have hbound : ∀ᶠ n in atTop, a n ≤ t n*q ∧ t n*q ≤ a n+2*q*(B n+1) :=
    ht.mono (fun n hn => ⟨hn.1,hn.2.1⟩)
  have hB : Tendsto (fun n => (B n : ℝ)/(a n : ℝ)) atTop (𝓝 0) :=
    frame_internal_bad_density a b d (p : ℤ) q (by omega) ha hd
      (by simpa only [Int.cast_natCast] using hr)
  have hW : ∀ r ∈ rationalPeriod p q, 1 ≤ r ∧ r ≤ m-1 := by
    intro r hmem
    have h := rationalPeriod_legal p q (m-1) hlo hhi.le r hmem
    exact ⟨h.1,by omega⟩
  apply eventual_periodic_upper m (by omega) (rationalPeriod p q)
    (rationalPeriod_nonempty p q (by omega)) hW q a C
    (fun n => completionIndex m q (a n) (t n)) ha
    (completion_index_shift_density m q (by omega) a B t ha hB hbound)
  exact ht.mono (fun n hn => ⟨completion_index_positive m q (a n) (t n),hn.2.2⟩)

theorem full_actual_frame_upper (m p q : ℕ) (hm : 3 ≤ m) (hq : 1 < q)
    (hc : p.Coprime q) (hlo : 1 ≤ (p : ℝ)/(q : ℝ))
    (hhi : (p : ℝ)/(q : ℝ) < (m-1 : ℕ)) (a b d : ℕ → ℕ)
    (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 ((p : ℝ)/(q : ℝ)))) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      Real.log (runCount m (frameWord (a n) (b n) (d n)) 0 : ℝ)/(a n : ℝ) ≤
        periodicGrowth m (rationalPeriod p q)/(q : ℝ)+ε :=
  full_frame_dominated_upper m p q hm hq hc hlo hhi a b d _ ha hd hr
    (Eventually.of_forall (fun _ => le_rfl))

end KroneckerFullActualUpper
end
end

