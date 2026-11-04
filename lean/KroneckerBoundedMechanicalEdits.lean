import KroneckerGeometricPrograms
import KroneckerCurrentMechanicalNotation
import InsertionConventionCheck

/-! Lemma 6.5 with its quantifier order, source run lengths, explicit final path,
and bounds on every intermediate run. The core estimates are reused through
an explicit bounded run-edit list. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerBoundedRunEdits
open KroneckerRunEditPrograms KroneckerPairedRunCosts

def append {m : ℕ} {X Y Z : List ℕ} {K A D L B E : ℕ}
    (p : RunEdits m X Y K A D) (q : RunEdits m Y Z L B E) :
    RunEdits m X Z (K+L) (A+B) (D+E) := by
  induction q with
  | nil => exact p
  | complete q r hr ih =>
    simpa only [Nat.add_assoc] using RunEdits.complete ih r hr
  | rise q hr ih =>
    simpa only [Nat.add_assoc] using RunEdits.rise ih hr
  | fall q hr ih =>
    simpa only [Nat.add_assoc] using RunEdits.fall ih hr

theorem target_legal {m : ℕ} {X Y : List ℕ} {K A D : ℕ}
    (p : RunEdits m X Y K A D) (hX : ∀ r ∈ X, 1 ≤ r ∧ r ≤ m-2) :
    ∀ r ∈ Y, 1 ≤ r ∧ r ≤ m-2 := by
  induction p with
  | nil => exact hX
  | @complete pre post K A D p r hr ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih s (List.mem_append_left post hs)
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact hr
      · exact ih s (List.mem_append_right pre hs)
  | @rise pre post r K A D p hr ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih s (by simp only [List.mem_append, List.mem_cons]; exact Or.inl hs)
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨by omega, hr.2⟩
      · exact ih s (by simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hs))
  | @fall pre post r K A D p hr ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih s (by simp only [List.mem_append, List.mem_cons]; exact Or.inl hs)
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨hr.1, by omega⟩
      · exact ih s (by simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hs))

def states {m : ℕ} {X Y : List ℕ} {K A D : ℕ}
    (p : RunEdits m X Y K A D) : List (List ℕ) := by
  induction p with
  | nil => exact [X]
  | @complete pre post K A D p r hr ih => exact ih ++ [pre++r::post]
  | @rise pre post r K A D p hr ih => exact ih ++ [pre++(r+1)::post]
  | @fall pre post r K A D p hr ih => exact ih ++ [pre++r::post]

theorem states_length {m : ℕ} {X Y : List ℕ} {K A D : ℕ}
    (p : RunEdits m X Y K A D) : (states p).length=K+A+D+1 := by
  induction p with
  | nil => rfl
  | complete p r hr ih => simp only [states, List.length_append, List.length_singleton] at ih ⊢; omega
  | rise p hr ih => simp only [states, List.length_append, List.length_singleton] at ih ⊢; omega
  | fall p hr ih => simp only [states, List.length_append, List.length_singleton] at ih ⊢; omega

theorem states_legal {m : ℕ} {X Y : List ℕ} {K A D : ℕ}
    (p : RunEdits m X Y K A D) (hX : ∀ r ∈ X, 1 ≤ r ∧ r ≤ m-2) :
    ∀ Z ∈ states p, ∀ r ∈ Z, 1 ≤ r ∧ r ≤ m-2 := by
  induction p with
  | nil => simpa only [states, List.mem_singleton, forall_eq] using hX
  | complete p r hr ih =>
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact ih Z hZ
    · obtain rfl := List.mem_singleton.mp hZ
      exact target_legal (.complete p r hr) hX
  | rise p hr ih =>
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact ih Z hZ
    · obtain rfl := List.mem_singleton.mp hZ
      exact target_legal (.rise p hr) hX
  | fall p hr ih =>
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact ih Z hZ
    · obtain rfl := List.mem_singleton.mp hZ
      exact target_legal (.fall p hr) hX

theorem increase (m : ℕ) (pre post : List ℕ) (r t : ℕ) :
    1 ≤ r → r+t ≤ m-2 →
    Nonempty (RunEdits m (pre++r::post) (pre++(r+t)::post) 0 t 0) := by
  induction t with
  | zero => intro _ _; exact ⟨.nil⟩
  | succ t ih =>
    intro hr ht
    obtain ⟨p⟩ := ih hr (by omega)
    exact ⟨by simpa only [Nat.add_assoc] using RunEdits.rise p ⟨by omega, by omega⟩⟩

theorem decrease (m : ℕ) (pre post : List ℕ) (r t : ℕ) :
    1 ≤ r → r+t ≤ m-2 →
    Nonempty (RunEdits m (pre++(r+t)::post) (pre++r::post) 0 0 t) := by
  induction t with
  | zero => intro _ _; exact ⟨.nil⟩
  | succ t ih =>
    intro hr ht
    obtain ⟨p⟩ := ih hr (by omega)
    let q : RunEdits m (pre++(r+t+1)::post) (pre++(r+t)::post) 0 0 1 :=
      .fall .nil ⟨by omega, by omega⟩
    exact ⟨by simpa only [Nat.zero_add, Nat.add_comm 1 t, Nat.add_assoc] using append q p⟩

theorem adjust (m : ℕ) (pre post : List ℕ) (r s : ℕ)
    (hr : 1 ≤ r ∧ r ≤ m-2) (hs : 1 ≤ s ∧ s ≤ m-2) :
    Nonempty (RunEdits m (pre++r::post) (pre++s::post) 0 (s-r) (r-s)) := by
  rcases le_total r s with h | h
  · have he : r+(s-r)=s := by omega
    simpa only [he, Nat.sub_eq_zero_of_le h] using
      increase m pre post r (s-r) hr.1 (by omega)
  · have he : s+(r-s)=r := by omega
    simpa only [he, Nat.sub_eq_zero_of_le h] using
      decrease m pre post s (r-s) hs.1 (by omega)

theorem paired (m : ℕ) (X Y pre : List ℕ) (hlen : X.length=Y.length)
    (hX : ∀ r ∈ X, 1 ≤ r ∧ r ≤ m-2) (hY : ∀ r ∈ Y, 1 ≤ r ∧ r ≤ m-2) :
    Nonempty (RunEdits m (pre++X) (pre++Y) 0 (rises X Y) (falls X Y)) := by
  induction X generalizing Y pre with
  | nil =>
    have hy : Y=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst Y
    exact ⟨.nil⟩
  | cons r X ih =>
    cases Y with
    | nil => simp at hlen
    | cons s Y =>
      obtain ⟨p⟩ := ih Y (pre++[s]) (by simpa using hlen)
        (fun t ht => hX t (by simp [ht])) (fun t ht => hY t (by simp [ht]))
      simp only [List.append_assoc, List.singleton_append] at p
      obtain ⟨q⟩ := adjust m pre X r s (hX r (by simp)) (hY s (by simp))
      exact ⟨by simpa [rises, falls] using append q p⟩

theorem sublist {m : ℕ} {X Y : List ℕ} (h : X.Sublist Y)
    (hY : ∀ r ∈ Y, 1 ≤ r ∧ r ≤ m-2) (pre post : List ℕ) :
    Nonempty (RunEdits m (pre++X++post) (pre++Y++post) (Y.length-X.length) 0 0) := by
  induction h generalizing pre with
  | slnil => exact ⟨.nil⟩
  | @cons X Y r h ih =>
    obtain ⟨p⟩ := ih (fun s hs => hY s (by simp [hs])) pre
    simp only [List.append_assoc] at p
    have hr := hY r (by simp)
    have he : Y.length-X.length+1=(r::Y).length-X.length := by
      have := h.length_le
      simp only [List.length_cons]
      omega
    exact ⟨by simpa only [List.append_assoc, List.cons_append, he] using
      RunEdits.complete (pre := pre) (post := Y++post) p r hr⟩
  | @cons_cons X Y r h ih =>
    obtain ⟨p⟩ := ih (fun s hs => hY s (by simp [hs])) (pre++[r])
    exact ⟨by simpa only [List.append_assoc, List.singleton_append, List.length_cons,
      Nat.add_sub_add_right] using p⟩

theorem paired_sublist (m : ℕ) (X Y Z : List ℕ) (hlen : X.length=Y.length)
    (hsub : Y.Sublist Z) (hX : ∀ r ∈ X, 1 ≤ r ∧ r ≤ m-2)
    (hZ : ∀ r ∈ Z, 1 ≤ r ∧ r ≤ m-2) :
    Nonempty (RunEdits m X Z (Z.length-X.length) (rises X Y) (falls X Y)) := by
  obtain ⟨p⟩ := paired m X Y [] hlen hX (fun r hr => hZ r (hsub.subset hr))
  obtain ⟨q⟩ := sublist hsub hZ [] []
  simp only [List.nil_append, List.append_nil] at p q
  exact ⟨by simpa only [Nat.zero_add, Nat.add_zero, hlen] using append p q⟩

/-- Vertical run-edits preserve the prescribed origin. -/
theorem vertical_program {m K A D : ℕ} {X Y : List ℕ}
    (p : RunEdits m X Y K A D) (hK : K = 0)
    (o : KroneckerPaperPaths.LatticePoint) :
    Nonempty (KroneckerPaperPaths.EditProgram m
      (KroneckerPaperPaths.runPath X o) (KroneckerPaperPaths.runPath Y o) 0 A D) := by
  open KroneckerPaperPaths KroneckerWordCounts KroneckerStack in
  induction p with
  | nil => exact ⟨.nil⟩
  | complete p r hr ih => omega
  | @rise pre post r K A D p hr ih =>
    obtain ⟨q⟩ := ih hK
    let i := (runWord pre).length+1
    have hi : i ≤ (runPath (pre++r::post) o).steps.length := by
      simp [i,runWord,runShape]
    have hs : insert (runPath (pre++r::post) o) i (ofSteps [false] 0) =
        runPath (pre++(r+1)::post) o := by
      apply TNEPath.ext
      · simpa only [insert_steps,runPath_steps,ofSteps_steps,
          KroneckerListInsertion.insertAt,List.append_assoc,List.singleton_append] using
          KroneckerVerticalInsertionRuns.insert_runWord pre post r
      · rw [insert_positive_origin _ _ _ (by simp [runWord,runShape]) (by omega),
          runPath_origin _ o (by simp),runPath_origin _ o (by simp)]
    exact ⟨hs ▸ EditProgram.north q i hi⟩
  | @fall pre post r K A D p hr ih =>
    obtain ⟨q⟩ := ih hK
    obtain ⟨hi,hv,hs⟩ := KroneckerRunDeletionPosition.runDeletion_data pre post r
    let k : Edge (runPath (pre++(r+1)::post) o) :=
      ⟨KroneckerRunDeletionPosition.runDeletionIndex pre r,hi⟩
    have hk : (runPath (pre++(r+1)::post) o).steps.get k = false := hv
    have he : deleteVertical (runPath (pre++(r+1)::post) o) k hk =
        runPath (pre++r::post) o := by
      apply TNEPath.ext
      · rw [deleteVertical_steps]
        exact hs
      · have hpos : 0 < k.val := by
          simp [k,KroneckerRunDeletionPosition.runDeletionIndex]
        have hp : (subpath (runPath (pre++(r+1)::post) o) 0 k.val).steps ≠ [] := by
          intro hempty
          have hl := congrArg List.length hempty
          simp only [subpath_steps,List.length_take,List.length_drop,List.length_nil] at hl
          have hklt := k.isLt
          omega
        rw [deleteVertical,concat_origin _ _ hp,
          subpath_origin _ 0 k.val hpos (Nat.le_of_lt k.isLt)]
        simp only [vertex,List.take_zero,displacement,add_zero]
        rw [runPath_origin _ o (by simp),runPath_origin _ o (by simp)]
    exact ⟨he ▸ EditProgram.delete q k hk⟩

/-- Lemma 6.1: changing the vertical lengths of two equally long runs. -/
theorem vertical_length_comparison (M : ℕ) (X Y : List ℕ)
    (hlen : X.length=Y.length) (hX : ∀ a ∈ X, 1 ≤ a ∧ a ≤ M)
    (hY : ∀ a ∈ Y, 1 ≤ a ∧ a ≤ M)
    (o q : KroneckerPaperPaths.LatticePoint) :
    ∃ I D : ℕ, ((I+D : ℕ) : ℝ)=
        (List.zipWith (fun a b : ℕ => |(a : ℝ)-(b : ℝ)|) X Y).sum ∧
      ∃ p : RunEdits (M+2) X Y 0 I D,
        (∀ Z ∈ states p, ∀ a ∈ Z, 1 ≤ a ∧ a ≤ M) ∧
        Nonempty (KroneckerPaperPaths.EditProgram (M+2)
          (KroneckerPaperPaths.runPath X o)
          (KroneckerPaperPaths.translate (KroneckerPaperPaths.runPath Y q) (o-q)) 0 I D) := by
  obtain ⟨p⟩ := paired (M+2) X Y [] hlen (by simpa using hX) (by simpa using hY)
  simp only [List.nil_append] at p
  have htarget : KroneckerPaperPaths.translate (KroneckerPaperPaths.runPath Y q) (o-q) =
      KroneckerPaperPaths.runPath Y o := by
    rw [KroneckerPaperPaths.runPath_translate]
    congr 1
    abel
  refine ⟨rises X Y,falls X Y,paired_cost_real X Y,p,?_,?_⟩
  · simpa using states_legal p (by simpa using hX)
  · rw [htarget]
    exact vertical_program p rfl o

end KroneckerBoundedRunEdits

namespace KroneckerBoundedMechanicalEdits
open KroneckerMechanicalWords KroneckerPairedRunCosts KroneckerPaperPaths
open KroneckerCurrentMechanicalNotation KroneckerRunEditPrograms

theorem uniform_exceptional_subsequence (r : ℝ) (hr : Irrational r)
    (η : ℝ) (hη : 0 < η) (M : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B₀ : ℕ, ∀ s t : ℝ,
      0 ≤ s → 1 ≤ t → t ≤ M → |s-r| < δ → |t-r| < δ →
      ∀ u v : ℝ, ∀ n T z : ℕ, (1 ≤ z ∧ z ≤ M) →
      (1+η)*((n : ℝ)+1)+(B₀ : ℝ) ≤ T →
      ∃ Y : List ℕ, Y.length=n+1 ∧ Y.Sublist (mechanicalWord t v 0 T) ∧
        (cost (mechanicalWord s u 0 n ++ [z]) Y : ℝ) ≤ η*((n : ℝ)+1)+(B₀ : ℝ) := by
  obtain ⟨q,hq,hcoeff⟩ := KroneckerSmallBlockCoefficients.small_block_coefficients η hη
  obtain ⟨Q,_,hL⟩ := KroneckerGlobalExceptionalSubsequence.global_exceptional_subsequence r hr q hq
  obtain ⟨L,hLpos,hQsmall,hBsmall⟩ := hcoeff Q
  obtain ⟨δ,hδ,h⟩ := hL L hLpos
  let B := 2*(L/q+1)
  let B₀ := (L+Q+1)+B+(M-1)
  have hQη : (Q : ℝ)/L ≤ η := by linarith
  have hBη : (B : ℝ)/L ≤ η := by dsimp [B]; linarith
  have hbaseL : (L : ℝ)+(Q : ℝ)+1 ≤ B₀ := by
    exact_mod_cast (show L+Q+1 ≤ B₀ by dsimp [B₀]; omega)
  have hbaseB : (B : ℝ)+(M-1 : ℕ) ≤ B₀ := by
    exact_mod_cast (show B+(M-1) ≤ B₀ by dsimp [B₀]; omega)
  refine ⟨δ,hδ,B₀,?_⟩
  intro s t hs ht htM hsr htr u v n T z hz hT
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlen := KroneckerRoundedAffineBudget.rounded_length_budget n L Q hLpos
  have hmulQ := mul_le_mul_of_nonneg_right hQη hnR
  have hneeded : (n/L+1)*(L+Q)+1 ≤ T := by
    have hreal : (((n/L+1)*(L+Q)+1 : ℕ) : ℝ) ≤ T := by
      push_cast at hlen ⊢
      nlinarith
    exact_mod_cast hreal
  obtain ⟨Y,hlenY,hsub,hcost⟩ := h s t hs ht hsr htr u v n T M z htM hz hneeded
  refine ⟨Y,hlenY,hsub,?_⟩
  have hb := KroneckerRoundedAffineBudget.rounded_affine_budget n L B hLpos
  have hmulB := mul_le_mul_of_nonneg_right hBη hnR
  have hcR : (cost (mechanicalWord s u 0 n ++ [z]) Y : ℝ) ≤
      (((n/L+1)*B : ℕ) : ℝ)+(M-1 : ℕ) := by exact_mod_cast hcost
  nlinarith

/-- The source has l=n+1 simple runs. The last run may be exceptional.
This auxiliary theorem accepts the path identity as a hypothesis.
The manuscript-facing theorem defines that path in its conclusion.
`RunEdits` uses individual run insertions and individual vertical-edge edits. -/
theorem mechanical_edits (m : ℕ) (r η : ℝ) (_hm : 4 ≤ m)
    (hr : Irrational r) (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B₀ : ℕ, 0 < B₀ ∧
      ∀ l T : ℕ, 0 < l → ∀ σ₁ σ₂ u₁ u₂ : ℝ,
      ∀ z : ℕ, 1 ≤ z ∧ z ≤ m-2 →
      |σ₁-r| < δ → |σ₂-r| < δ → (1+η)*(l : ℝ)+(B₀ : ℝ) ≤ T →
      ∀ U V : TNEPath,
      U = runPath (mechanicalWord σ₁ u₁ 0 (l-1) ++ [z]) U.origin →
      V = MechRunFactor σ₂ u₂ 1 T →
      ∃ A D : ℕ, ((A+D : ℕ) : ℝ) ≤ 12*η*(l : ℝ)+(B₀ : ℝ) ∧
      ∃ p : RunEdits m (mechanicalWord σ₁ u₁ 0 (l-1) ++ [z])
          (mechanicalWord σ₂ u₂ 0 T) (T-l) A D,
        (∀ X ∈ KroneckerBoundedRunEdits.states p, ∀ a ∈ X, 1 ≤ a ∧ a ≤ m-2) ∧
        ∃ w : LatticePoint, Nonempty (EditProgram m U (translate V w) (T-l) A D) := by
  obtain ⟨d,hd,B,h⟩ := uniform_exceptional_subsequence r hr η hη (m-2)
  let δ := min d (min (r-1) ((m-2 : ℕ)-r))
  have hδ : 0 < δ := lt_min hd (lt_min (by linarith) (by linarith))
  refine ⟨δ,hδ,B+1,by omega,?_⟩
  intro l T hl σ₁ σ₂ u₁ u₂ z hz hs ht hT U V hU hV
  have hs' := abs_lt.mp hs
  have ht' := abs_lt.mp ht
  have hd1 : δ ≤ r-1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdM : δ ≤ (m-2 : ℕ)-r := (min_le_right _ _).trans (min_le_right _ _)
  have hs1 : 1 ≤ σ₁ := by linarith [hs'.1]
  have hsM : σ₁ ≤ (m-2 : ℕ) := by linarith [hs'.2]
  have ht1 : 1 ≤ σ₂ := by linarith [ht'.1]
  have htM : σ₂ ≤ (m-2 : ℕ) := by linarith [ht'.2]
  have he : l-1+1=l := by omega
  have heR : ((l-1 : ℕ) : ℝ)+1=(l : ℝ) := by exact_mod_cast he
  have hT' : (1+η)*(((l-1 : ℕ) : ℝ)+1)+(B : ℝ) ≤ T := by
    rw [heR]
    push_cast at hT
    linarith
  obtain ⟨Y,hlen,hsub,hcost⟩ := h σ₁ σ₂ (by linarith) ht1 htM
    (lt_of_lt_of_le hs (min_le_left _ _)) (lt_of_lt_of_le ht (min_le_left _ _))
    u₁ u₂ (l-1) T z hz hT'
  let X := mechanicalWord σ₁ u₁ 0 (l-1) ++ [z]
  have hX : ∀ a ∈ X, 1 ≤ a ∧ a ≤ m-2 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact mechanicalWord_legal σ₁ u₁ 0 (l-1) (m-2) hs1 hsM a ha
    · obtain rfl := List.mem_singleton.mp ha
      exact hz
  obtain ⟨p⟩ := KroneckerBoundedRunEdits.paired_sublist m X Y
    (mechanicalWord σ₂ u₂ 0 T) (by simp [X, mechanicalWord_length, hlen]) hsub hX
    (mechanicalWord_legal σ₂ u₂ 0 T (m-2) ht1 htM)
  have hXL : X.length=l := by simp [X, mechanicalWord_length, he]
  rw [mechanicalWord_length, hXL] at p
  refine ⟨rises X Y,falls X Y,?_,p,KroneckerBoundedRunEdits.states_legal p hX,?_⟩
  · change (cost X Y : ℝ) ≤ _
    rw [heR] at hcost
    push_cast
    nlinarith [show (0 : ℝ) ≤ l by positivity]
  · have hp := toRaw p
    have hsU : U.steps=KroneckerWordCounts.runWord X := by rw [hU]; rfl
    have hsV : V.steps=KroneckerWordCounts.runWord (mechanicalWord σ₂ u₂ 0 T) := by
      rw [hV, MechRunFactor_one]; rfl
    exact rawProgram_translated_target U V (by simpa only [hsU, hsV] using hp)

end KroneckerBoundedMechanicalEdits

#print axioms KroneckerBoundedRunEdits.vertical_program
#print axioms KroneckerBoundedRunEdits.vertical_length_comparison
