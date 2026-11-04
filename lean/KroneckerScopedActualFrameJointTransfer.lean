import KroneckerLegalIntegerJoint
import Mathlib.Topology.UniformSpace.HeineCantor
import KroneckerLiteralEulerLimitTransfer
import KroneckerUpperIntegerLimit
import KroneckerScopedActualFrameChoice
import KroneckerThreeEntropyPositive

/- Original module: KroneckerIntegerFrameApproximants -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerIntegerFrameApproximants
open KroneckerFrameObservables KroneckerFrameSlope

def integerFrame (k n : ℕ) : FramePoint := ⟨n+1,k*(n+1)+1,1,by omega⟩

theorem integerFrame_frameSlope (k n : ℕ) :
    frameSlope (integerFrame k n).a (integerFrame k n).b (integerFrame k n).d = (k : ℝ) := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  dsimp [integerFrame,frameSlope]
  push_cast
  field_simp
  ring

theorem integerFrame_height (k : ℕ) : Tendsto (fun n => height (integerFrame k n)) atTop atTop := by
  exact tendsto_atTop_mono (fun n => show n ≤ n+1 by omega) tendsto_id

theorem integerFrame_slope (k : ℕ) : Tendsto (fun n => slope (integerFrame k n)) atTop (𝓝 (k : ℝ)) := by
  have he : (fun n => slope (integerFrame k n)) = (fun n : ℕ => (k : ℝ)+1/((n : ℝ)+1)) := by
    funext n
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    dsimp [KroneckerFrameObservables.slope,integerFrame]
    push_cast
    field_simp
  rw [he]
  simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (k : ℝ)

end KroneckerIntegerFrameApproximants
end

/- Original module: KroneckerLegalFrameApproximable -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerLegalFrameApproximable
open KroneckerLegalFrameDomain KroneckerIntegerFrameApproximants KroneckerLogic

theorem legal_integer_approximable (m k : ℕ) (hk : 1 ≤ k ∧ k ≤ m-2) :
    Approximable (height (m:=m)) slope (k : ℝ) := by
  intro δ hδ N
  obtain ⟨n,hn,hs⟩ := ((integerFrame_height k).eventually (eventually_ge_atTop N)).and
    ((Metric.tendsto_nhds.mp (integerFrame_slope k)) δ hδ) |>.exists
  have hl : ∀ r ∈ KroneckerFrameBadDensity.frameWord
      (integerFrame k n).a (integerFrame k n).b (integerFrame k n).d, 1 ≤ r ∧ r ≤ m-2 := by
    apply KroneckerFrameWord.frameWord_legal
    · rw [integerFrame_frameSlope]; exact_mod_cast hk.1
    · rw [integerFrame_frameSlope]; exact_mod_cast hk.2
  exact ⟨⟨integerFrame k n,hl⟩,hn,hs⟩

theorem legal_frame_approximable (m : ℕ) (hm : 4 ≤ m) (r : ℝ)
    (hr : r ∈ Set.Icc 1 ((m-2 : ℕ) : ℝ)) : Approximable (height (m:=m)) slope r := by
  by_cases hlo : 1 < r
  · by_cases hhi : r < (m-2 : ℕ)
    · obtain ⟨x⟩ := approaching_nonempty KroneckerFrameObservables.height KroneckerFrameObservables.slope
        (KroneckerFrameObservables.frame_approximable r hlo)
      have hl := KroneckerEventualFrameAlphabet.eventual_frame_alphabet
        (fun n => (x.val n).a) (fun n => (x.val n).b) (fun n => (x.val n).d) (m-2) r
        x.property.1 (fun n => (x.val n).hd) x.property.2 hlo hhi
      intro δ hδ N
      obtain ⟨n,hn,hs,hnl⟩ := ((x.property.1.eventually (eventually_ge_atTop N)).and
        (((Metric.tendsto_nhds.mp x.property.2) δ hδ).and hl)).exists
      exact ⟨⟨x.val n,hnl⟩,hn,hs⟩
    · have he : r = (m-2 : ℕ) := le_antisymm hr.2 (le_of_not_gt hhi)
      rw [he]
      exact legal_integer_approximable m (m-2) ⟨by omega,le_rfl⟩
  · have he : r = 1 := le_antisymm (le_of_not_gt hlo) hr.1
    rw [he]
    exact_mod_cast legal_integer_approximable m 1 ⟨le_rfl,by omega⟩

end KroneckerLegalFrameApproximable
end

/- Original module: KroneckerClosedAlphabetExistence -/
section
set_option autoImplicit false
namespace KroneckerClosedAlphabetExistence
open KroneckerLegalFrameDomain KroneckerLogic

theorem closed_alphabet_limit_exists (m : ℕ) (hm : 4 ≤ m) (r : ℝ)
    (hr : r ∈ Set.Icc 1 ((m-2 : ℕ) : ℝ)) :
    ∃ L : ℝ, JointLimit (height (m:=m)) slope value r L := by
  by_cases hlo : 1 < r
  · by_cases hhi : r < (m-2 : ℕ)
    · exact ⟨_,interior_legal_frame_joint m hm r ⟨hlo,hhi⟩⟩
    · have he : r = (m-2 : ℕ) := le_antisymm hr.2 (le_of_not_gt hhi)
      rw [he]
      exact ⟨_,KroneckerLegalIntegerJoint.legal_integer_joint m (m-2) hm ⟨by omega,le_rfl⟩⟩
  · have he : r = 1 := le_antisymm (le_of_not_gt hlo) hr.1
    rw [he]
    exact ⟨_,by simpa only [Nat.cast_one] using
      KroneckerLegalIntegerJoint.legal_integer_joint m 1 hm ⟨le_rfl,by omega⟩⟩

end KroneckerClosedAlphabetExistence
end

/- Original module: KroneckerClosedAlphabetEntropy -/
section
set_option autoImplicit false
namespace KroneckerClosedAlphabetEntropy
open KroneckerLogic KroneckerLegalFrameDomain

def interval (m : ℕ) : Set ℝ := Set.Icc 1 ((m-2 : ℕ) : ℝ)

noncomputable def entropy (m : ℕ) (r : ℝ) : ℝ := by
  classical
  exact if h : 4 ≤ m ∧ r ∈ interval m then
    Classical.choose (KroneckerClosedAlphabetExistence.closed_alphabet_limit_exists m h.1 r h.2)
  else 0

theorem closed_entropy_joint (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interval m) :
    JointLimit (height (m:=m)) slope value r (entropy m r) := by
  rw [entropy,dite_eq_left ⟨hm,hr⟩]
  exact Classical.choose_spec (KroneckerClosedAlphabetExistence.closed_alphabet_limit_exists m hm r hr)



end KroneckerClosedAlphabetEntropy
end

/- Original module: KroneckerClosedAlphabetIntegers -/
section
set_option autoImplicit false
namespace KroneckerClosedAlphabetIntegers
open KroneckerClosedAlphabetEntropy KroneckerPeriodicTail



end KroneckerClosedAlphabetIntegers
end

/- Original module: KroneckerClosedAlphabetContinuity -/
section
set_option autoImplicit false
namespace KroneckerClosedAlphabetContinuity
open KroneckerClosedAlphabetEntropy KroneckerLegalFrameDomain


end KroneckerClosedAlphabetContinuity
end

/- Original module: KroneckerClosedAlphabetBounds -/
section
set_option autoImplicit false
namespace KroneckerClosedAlphabetBounds
open KroneckerLogic KroneckerLegalFrameDomain KroneckerClosedAlphabetEntropy

theorem closed_entropy_bounds (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interval m) :
    Real.log (m : ℝ)/2 ≤ entropy m r ∧ entropy m r ≤ (m : ℝ)*m*Real.log 2 := by
  obtain ⟨x⟩ := approaching_nonempty (height (m:=m)) slope
    (KroneckerLegalFrameApproximable.legal_frame_approximable m hm r hr)
  have hl := jointLimit_sequence (height (m:=m)) slope value (closed_entropy_joint m hm r hr)
    x.val x.property.1 x.property.2
  exact KroneckerFrameLimitBounds.frame_limit_bounds m (by omega) (fun n => (x.val n).val) _ x.property.1
    (Filter.Eventually.of_forall (fun n r hr' =>
      ⟨((x.val n).property r hr').1,by have := ((x.val n).property r hr').2; omega⟩)) hl

theorem closed_entropy_positive (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interval m) :
    0 < entropy m r := by
  have h := (closed_entropy_bounds m hm r hr).1
  have hp : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  linarith

end KroneckerClosedAlphabetBounds
end

/- Original module: KroneckerClosedAlphabetUniformity -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerClosedAlphabetUniformity
open KroneckerClosedAlphabetEntropy



end KroneckerClosedAlphabetUniformity
end

/- Original module: KroneckerInteriorEulerJoint -/
section
set_option autoImplicit false
namespace KroneckerInteriorEulerJoint
open KroneckerEulerObservables KroneckerEulerFramePositivity KroneckerInteriorEntropy


end KroneckerInteriorEulerJoint
end

/- Original module: KroneckerInteriorEulerUnique -/
section
set_option autoImplicit false
namespace KroneckerInteriorEulerUnique
open KroneckerLogic KroneckerEulerObservables KroneckerInteriorEntropy


end KroneckerInteriorEulerUnique
end

/- Original module: KroneckerInteriorLiteratureSequence -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerInteriorLiteratureSequence
open KroneckerFrameIdentity KroneckerInteriorEntropy


end KroneckerInteriorLiteratureSequence
end

/- Original module: KroneckerBelowEulerDomain -/
section
set_option autoImplicit false
namespace KroneckerBelowEulerDomain

def BelowEulerPoint (m : ℕ) :=
  {x : KroneckerEulerObservables.EulerPoint m // KroneckerEulerObservables.slope x ≤ (m-2 : ℕ)}

def height {m : ℕ} (x : BelowEulerPoint m) : ℕ := x.val.P.a
noncomputable def slope {m : ℕ} (x : BelowEulerPoint m) : ℝ := KroneckerEulerObservables.slope x.val
noncomputable def value {m : ℕ} (x : BelowEulerPoint m) : ℝ := KroneckerEulerObservables.value x.val

theorem below_euler_frame_legal (m : ℕ) (x : BelowEulerPoint m) :
    ∀ r ∈ KroneckerFrameBadDensity.frameWord x.val.P.a x.val.P.b x.val.P.d₁,
      1 ≤ r ∧ r ≤ m-2 :=
  KroneckerUpperIntegerLimit.parameter_below_alphabet x.val.P (m-2) x.property

def toLegalFrame {m : ℕ} (x : BelowEulerPoint m) : KroneckerLegalFrameDomain.LegalFramePoint m :=
  ⟨KroneckerEulerFramePositivity.toFrame x.val,below_euler_frame_legal m x⟩

end KroneckerBelowEulerDomain
end

/- Original module: KroneckerBelowEulerJoint -/
section
set_option autoImplicit false
namespace KroneckerBelowEulerJoint
open KroneckerBelowEulerDomain KroneckerClosedAlphabetEntropy

theorem below_euler_joint (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interval m) :
    KroneckerLogic.JointLimit (height (m:=m)) slope value r (entropy m r) := by
  apply KroneckerLogic.jointLimit_of_sequences (height (m:=m)) slope value
  intro x ha hs
  apply KroneckerLiteralEulerLimitTransfer.literal_euler_limit_transfer m (by omega)
    (fun n => (x n).val) _ ha
  · exact Filter.Eventually.of_forall (fun n s hs' =>
      ⟨(below_euler_frame_legal m (x n) s hs').1,
        by have := (below_euler_frame_legal m (x n) s hs').2; omega⟩)
  · exact KroneckerLogic.jointLimit_sequence _ _ _ (closed_entropy_joint m hm r hr)
      (fun n => toLegalFrame (x n)) ha hs

end KroneckerBelowEulerJoint
end

/- Original module: KroneckerEulerAlphabetNeighborhood -/
section
/-! Below-alphabet Euler limits are unrestricted locally at every strictly lower slope. -/
set_option autoImplicit false
namespace KroneckerEulerAlphabetNeighborhood
open KroneckerLogic KroneckerEulerObservables

theorem below_to_full_joint (m : ℕ) (r L : ℝ) (hr : r < ((m-2 : ℕ) : ℝ))
    (h : JointLimit (KroneckerBelowEulerDomain.height (m:=m))
      KroneckerBelowEulerDomain.slope KroneckerBelowEulerDomain.value r L) :
    JointLimit (height (m:=m)) slope value r L := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := h ε hε
  refine ⟨min δ (((m-2 : ℕ) : ℝ)-r),lt_min hδ (sub_pos.mpr hr),N,?_⟩
  intro x hx hs
  have hb : slope x ≤ ((m-2 : ℕ) : ℝ) := by
    have hd := lt_of_lt_of_le hs (min_le_right δ (((m-2 : ℕ) : ℝ)-r))
    rw [Real.dist_eq] at hd
    have hu := (abs_lt.mp hd).2
    linarith
  exact hN ⟨x,hb⟩ hx (lt_of_lt_of_le hs (min_le_left _ _))

end KroneckerEulerAlphabetNeighborhood
end

/- Original module: KroneckerEulerCentralJoint -/
section
set_option autoImplicit false
namespace KroneckerEulerCentralJoint
open KroneckerLogic KroneckerEulerObservables KroneckerClosedAlphabetEntropy

theorem euler_central_joint (m : ℕ) (hm : 4 ≤ m) :
    JointLimit (height (m:=m)) slope value 1 (entropy m 1) := by
  apply KroneckerEulerAlphabetNeighborhood.below_to_full_joint
  · exact_mod_cast (show 1 < m-2 by omega)
  · exact KroneckerBelowEulerJoint.below_euler_joint m hm 1
      ⟨le_rfl,by exact_mod_cast (show 1 ≤ m-2 by omega)⟩

end KroneckerEulerCentralJoint
end

/- Original module: KroneckerThreeEulerJoint -/
section
/-! Transfer the literal frame entropy to Euler observables under their existing Literature interface. -/
set_option autoImplicit false
namespace KroneckerThreeEulerJoint
open KroneckerEulerObservables KroneckerEulerFramePositivity KroneckerThreeEntropy

theorem three_euler_joint (r : ℝ) (hr : r ∈ interior) :
    KroneckerLogic.JointLimit (height (m:=3)) slope value r (entropy r) := by
  apply KroneckerLogic.jointLimit_of_sequences (height (m:=3)) slope value
  intro x ha hs
  apply KroneckerLiteralEulerLimitTransfer.literal_euler_limit_transfer 3 (by omega) x _ ha
  · exact KroneckerEventualFrameAlphabet.eventual_frame_alphabet
      (fun n => (x n).P.a) (fun n => (x n).P.b) (fun n => (x n).P.d₁) 2 r ha
      (fun n => (toFrame (x n)).hd) hs hr.1 hr.2
  · exact KroneckerThreeEntropySequences.three_frame_sequence r hr
      (fun n => toFrame (x n)) ha hs

end KroneckerThreeEulerJoint
end

/- Original module: KroneckerScopedActualFrameJointTransfer -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedActualFrameJointTransfer
open Filter KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerFrameIdentity KroneckerScopedActualFrameApplication
open KroneckerScopedActualFrameChoice KroneckerLogic
open scoped Topology

def inputHeight {m : ℕ} (x : Input m) : ℕ := x.a
def inputSlope {m : ℕ} (x : Input m) : ℝ := (x.b : ℝ)/x.a
def inputValue (G : Geometry) {m : ℕ} (x : Input m) : ℝ :=
  Real.log (euler (family G) m x.a x.b : ℝ)/(x.a : ℝ)

theorem joint_to_input (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m)
    (r L : ℝ) (h : JointLimit (KroneckerEulerObservables.height (m:=m))
      KroneckerEulerObservables.slope KroneckerEulerObservables.value r L) :
    JointLimit (inputHeight (m:=m)) inputSlope (inputValue G) r L := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := h ε hε
  refine ⟨δ,hδ,N,?_⟩
  intro x hx hs
  have ht := hN (toEuler G A m hm x)
  simp only [toEuler_height, toEuler_slope, toEuler_value] at ht
  exact ht hx hs

theorem input_to_actual (G : Geometry) (m : ℕ) (r L : ℝ) (hr : 1 < r)
    (h : JointLimit (inputHeight (m:=m)) inputSlope (inputValue G) r L) :
    JointLimit (height (M:=family G) (m:=m)) slope value r L := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := h ε hε
  refine ⟨min δ (r-1), lt_min hδ (sub_pos.mpr hr), max N 2, ?_⟩
  intro p hp hs
  have ha : 2 ≤ p.val.1 := (le_max_right N 2).trans hp
  have hapos : (0:ℝ) < p.val.1 := by exact_mod_cast p.property.1
  have hab : p.val.1 < p.val.2 := by
    have hd := (abs_lt.mp (show |slope p-r| < r-1 by
      simpa only [Real.dist_eq] using hs.trans_le (min_le_right _ _))).1
    have hrp : 1 < (p.val.2:ℝ)/p.val.1 := by change 1 < slope p; linarith
    have ht := (lt_div_iff₀ hapos).mp hrp
    simp only [one_mul] at ht
    exact_mod_cast ht
  exact hN ⟨p.val.1,p.val.2,ha,hab,p.property.2.2.1⟩
    ((le_max_left N 2).trans hp) (hs.trans_le (min_le_left _ _))

theorem joint_to_actual (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m)
    (r L : ℝ) (hr : 1 < r)
    (h : JointLimit (KroneckerEulerObservables.height (m:=m))
      KroneckerEulerObservables.slope KroneckerEulerObservables.value r L) :
    JointLimit (height (M:=family G) (m:=m)) slope value r L :=
  input_to_actual G m r L hr (joint_to_input G A m hm r L h)

theorem input_sequence {α : Type*} {l : Filter α} (G : Geometry) (m : ℕ)
    (r L : ℝ) (h : JointLimit (inputHeight (m:=m)) inputSlope (inputValue G) r L)
    (a b : α → ℕ) (ha : Tendsto a l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 r))
    (hp : ∀ᶠ i in l, 2 ≤ a i ∧ a i < b i ∧ (a i).Coprime (b i)) :
    Tendsto (fun i => Real.log (euler (family G) m (a i) (b i) : ℝ)/(a i : ℝ)) l (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := h ε hε
  filter_upwards [ha.eventually (eventually_ge_atTop N),
    (Metric.tendsto_nhds.mp hs) δ hδ, hp] with i hai hsi hpi
  exact hN ⟨a i,b i,hpi.1,hpi.2.1,hpi.2.2⟩ hai hsi

abbrev BelowInput (m : ℕ) := {x : Input m // inputSlope x ≤ (m-2 : ℕ)}

def toBelowEuler (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : BelowInput m) :
    KroneckerBelowEulerDomain.BelowEulerPoint m :=
  ⟨toEuler G A m hm x.val, by rw [toEuler_slope]; exact x.property⟩

theorem below_joint (G : Geometry) (A : Application G) (m : ℕ) (hm : 4 ≤ m)
    (r : ℝ) (hr : r ∈ KroneckerClosedAlphabetEntropy.interval m) :
    JointLimit (fun x : BelowInput m => inputHeight x.val)
      (fun x => inputSlope x.val) (fun x => inputValue G x.val)
      r (KroneckerClosedAlphabetEntropy.entropy m r) := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := KroneckerBelowEulerJoint.below_euler_joint m hm r hr ε hε
  refine ⟨δ,hδ,N,?_⟩
  intro x hx hs
  have ht := hN (toBelowEuler G A m (by omega) x)
  have hh : KroneckerBelowEulerDomain.height (toBelowEuler G A m (by omega) x) = inputHeight x.val :=
    toEuler_height G A m (by omega) x.val
  have hs' : KroneckerBelowEulerDomain.slope (toBelowEuler G A m (by omega) x) = inputSlope x.val :=
    toEuler_slope G A m (by omega) x.val
  have hv : KroneckerBelowEulerDomain.value (toBelowEuler G A m (by omega) x) = inputValue G x.val :=
    toEuler_value G A m (by omega) x.val
  rw [hh, hs', hv] at ht
  exact ht hx hs

theorem below_sequence {α : Type*} {l : Filter α} (G : Geometry) (A : Application G)
    (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ KroneckerClosedAlphabetEntropy.interval m)
    (a b : α → ℕ) (ha : Tendsto a l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 r))
    (hp : ∀ᶠ i in l, 2 ≤ a i ∧ a i < b i ∧ (a i).Coprime (b i) ∧
      (b i : ℝ)/a i ≤ (m-2 : ℕ)) :
    Tendsto (fun i => Real.log (euler (family G) m (a i) (b i) : ℝ)/(a i : ℝ)) l
      (𝓝 (KroneckerClosedAlphabetEntropy.entropy m r)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := below_joint G A m hm r hr ε hε
  filter_upwards [ha.eventually (eventually_ge_atTop N),
    (Metric.tendsto_nhds.mp hs) δ hδ, hp] with i hai hsi hpi
  exact hN ⟨⟨a i,b i,hpi.1,hpi.2.1,hpi.2.2.1⟩,hpi.2.2.2⟩ hai hsi

theorem three_joint (G : Geometry) (A : Application G) (r : ℝ) (hr : r ∈ Set.Ioo 1 2) :
    JointLimit (height (M:=family G) (m:=3)) slope value r (KroneckerThreeEntropy.entropy r) :=
  joint_to_actual G A 3 (by decide) r _ hr.1 (KroneckerThreeEulerJoint.three_euler_joint r hr)

theorem three_positive (G : Geometry) (A : Application G) (r : ℝ) (hr : r ∈ Set.Ioo 1 2) :
    ∃ L : ℝ, 0 < L ∧ JointLimit (height (M:=family G) (m:=3)) slope value r L :=
  ⟨_, KroneckerThreeEntropyPositive.entropy_positive r hr, three_joint G A r hr⟩

theorem central_input_joint (G : Geometry) (A : Application G) (m : ℕ) (hm : 4 ≤ m) :
    JointLimit (inputHeight (m:=m)) inputSlope (inputValue G) 1
      (KroneckerClosedAlphabetEntropy.entropy m 1) :=
  joint_to_input G A m (by omega) 1 _ (KroneckerEulerCentralJoint.euler_central_joint m hm)

theorem interior_joint (G : Geometry) (A : Application G) (m : ℕ) (hm : 4 ≤ m)
    (r : ℝ) (hr : 1 < r ∧ r < ((m-2 : ℕ) : ℝ)) :
    JointLimit (height (M:=family G) (m:=m)) slope value r (KroneckerClosedAlphabetEntropy.entropy m r) :=
  joint_to_actual G A m (by omega) r _ hr.1
    (KroneckerEulerAlphabetNeighborhood.below_to_full_joint m r _ hr.2
      (KroneckerBelowEulerJoint.below_euler_joint m hm r ⟨hr.1.le,hr.2.le⟩))

theorem interior_positive (G : Geometry) (A : Application G) (m : ℕ) (hm : 4 ≤ m)
    (r : ℝ) (hr : 1 < r ∧ r < ((m-2 : ℕ) : ℝ)) :
    ∃ L : ℝ, 0 < L ∧ JointLimit (height (M:=family G) (m:=m)) slope value r L :=
  ⟨_, KroneckerClosedAlphabetBounds.closed_entropy_positive m hm r ⟨hr.1.le,hr.2.le⟩,
    interior_joint G A m hm r hr⟩

end KroneckerScopedActualFrameJointTransfer
end
end
