import KroneckerManuscriptLimitStatements
import KroneckerUpperIntegerLimit

/-! Proposition 5.1: the explicit intersection A_m ∩ S_m and the two
one-sided limits. The arrows denote approach from one side; they impose
no monotonicity condition on a sequence. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerRestrictedIntegerLimits
open Filter KroneckerLogic KroneckerPeriodicTail
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerScopedActualFrameChoice KroneckerScopedActualFrameJointTransfer
open KroneckerManuscriptTarget
open scoped Topology

def Alphabet (m : ℕ) (hm : 3 ≤ m) (x : Input m) : Prop :=
  ∀ r ∈ KroneckerFrameBadDensity.frameWord x.a x.b (parameters m hm x).d₁,
    1 ≤ r ∧ r ≤ m-2

/-- Input records b>a≥2 and gcd(a,b)=1. The remaining clause is precisely
that every simple-run vertical length of U(a,b) lies in [m-2]. -/
def S_m (m : ℕ) (hm : 3 ≤ m) : Set (ℕ × ℕ) :=
  {ab | ∃ x : Input m, (x.a,x.b)=ab ∧ Alphabet m hm x}

def A_m (m : ℕ) : Set (ℕ × ℕ) :=
  {ab | Allowed (family KroneckerReadableMain.geometry) m ab.1 ab.2}

abbrev RestrictedDimension (m : ℕ) (hm : 3 ≤ m) :=
  {ab : ℕ × ℕ // ab ∈ A_m m ∩ S_m m hm}

def restrictedInput {m : ℕ} {hm : 3 ≤ m} (x : RestrictedDimension m hm) : Input m :=
  Classical.choose x.property.2

theorem restrictedInput_spec {m : ℕ} {hm : 3 ≤ m} (x : RestrictedDimension m hm) :
    ((restrictedInput x).a,(restrictedInput x).b)=x.val ∧
      Alphabet m hm (restrictedInput x) := Classical.choose_spec x.property.2

theorem integer_joint (m k : ℕ) (hm : 4 ≤ m) (hk : 1 ≤ k ∧ k ≤ m-2) :
    JointLimit (fun x : RestrictedDimension m (by omega) => x.val.1)
      (fun x => (x.val.2 : ℝ)/x.val.1)
      (fun x => Real.log (euler (family KroneckerReadableMain.geometry) m
        x.val.1 x.val.2 : ℝ)/(x.val.1 : ℝ)) (k : ℝ) (periodicGrowth m [k]) := by
  apply jointLimit_of_sequences
  intro x ha hs
  have he (n : ℕ) := (restrictedInput_spec (x n)).1
  have hea (n : ℕ) : (restrictedInput (x n)).a = (x n).val.1 := congrArg Prod.fst (he n)
  have heb (n : ℕ) : (restrictedInput (x n)).b = (x n).val.2 := congrArg Prod.snd (he n)
  have h := KroneckerManuscriptLimitStatements.integer_actual_sequence
    KroneckerReadableMain.geometry KroneckerReadableMain.counting m k hm hk
    (fun n => restrictedInput (x n))
    (by simpa only [show (fun n => (restrictedInput (x n)).a) =
      (fun n => (x n).val.1) from funext (fun n => hea n)] using ha)
    (by simpa only [inputSlope, show (fun n => ((restrictedInput (x n)).b : ℝ)/
      (restrictedInput (x n)).a) = (fun n => ((x n).val.2 : ℝ)/(x n).val.1) from
      funext (fun n => by rw [hea n, heb n])] using hs)
    (Filter.Eventually.of_forall fun n => (restrictedInput_spec (x n)).2)
  have hv : (fun n => inputValue KroneckerReadableMain.geometry (restrictedInput (x n))) =
      (fun n => Real.log (euler (family KroneckerReadableMain.geometry) m
        (x n).val.1 (x n).val.2 : ℝ)/((x n).val.1 : ℝ)) := by
    funext n
    simp only [inputValue, hea n, heb n]
  simpa only [hv] using h

theorem mem_S_m_of_slope (m : ℕ) (hm : 4 ≤ m) (a b : ℕ)
    (ha : 2 ≤ a) (hab : a < b) (hc : a.Coprime b)
    (hs : (b : ℝ)/a ≤ (m-2 : ℕ)) : (a,b) ∈ S_m m (by omega) := by
  let x : Input m := ⟨a,b,ha,hab,hc⟩
  refine ⟨x,rfl,?_⟩
  have h := KroneckerUpperIntegerLimit.parameter_below_alphabet
    (parameters m (by omega) x) (m-2)
    (by simpa only [(parameters_spec m (by omega) x).2.1,
      (parameters_spec m (by omega) x).2.2] using hs)
  simpa only [Alphabet, (parameters_spec m (by omega) x).2.1,
    (parameters_spec m (by omega) x).2.2] using h

/-- Transfer to a one-sided domain whose sufficiently close points lie
in the open strip (1,m-2). This removes S_m from the limit subscript. -/
theorem integer_on_side (m k : ℕ) (hm : 4 ≤ m) (hk : 1 ≤ k ∧ k ≤ m-2)
    (J : Set ℝ) (ε : ℝ) (hε : 0 < ε)
    (hJ : ∀ s ∈ J, dist s (k : ℝ) < ε → 1 < s ∧ s ≤ (m-2 : ℕ)) :
    JointLimit (fun x : {x : Dimension (family KroneckerReadableMain.geometry) m //
        slope x ∈ J} => height x.val)
      (fun x => slope x.val) (fun x => value x.val)
      (k : ℝ) (periodicGrowth m [k]) := by
  intro e he
  obtain ⟨d,hd,N,hN⟩ := integer_joint m k hm hk e he
  refine ⟨min d ε,lt_min hd hε,max N 2,?_⟩
  intro x hx hs
  have ha : 2 ≤ x.val.val.1 := (le_max_right N 2).trans hx
  have hstrip := hJ _ x.property (hs.trans_le (min_le_right _ _))
  have hapos : (0 : ℝ) < x.val.val.1 := by exact_mod_cast x.val.property.1
  have hab : x.val.val.1 < x.val.val.2 := by
    have h := (lt_div_iff₀ hapos).mp hstrip.1
    simp only [one_mul] at h
    exact_mod_cast h
  exact hN ⟨x.val.val,x.val.property,
    mem_S_m_of_slope m hm _ _ ha hab x.val.property.2.2.1 hstrip.2⟩
    ((le_max_left N 2).trans hx) (hs.trans_le (min_le_left _ _))

theorem downarrow_one (m : ℕ) (hm : 4 ≤ m) :
    JointLimit (fun x : {x : Dimension (family KroneckerReadableMain.geometry) m //
        1 < slope x} => height x.val)
      (fun x => slope x.val) (fun x => value x.val) 1 (periodicGrowth m [1]) := by
  have hM : (1 : ℝ) < (m-2 : ℕ) := by exact_mod_cast (show 1 < m-2 by omega)
  have h := integer_on_side m 1 hm ⟨by omega,by omega⟩ (Set.Ioi 1)
    ((m-2 : ℕ)-1) (by linarith) (by
      intro s hs hd
      have h := (abs_lt.mp (show |s-1| < (m-2 : ℕ)-1 by
        simpa [Real.dist_eq] using hd)).2
      exact ⟨hs,by linarith⟩)
  simp only [Nat.cast_one] at h
  exact h

theorem uparrow_M (m : ℕ) (hm : 4 ≤ m) :
    JointLimit (fun x : {x : Dimension (family KroneckerReadableMain.geometry) m //
        slope x < (m-2 : ℕ)} => height x.val)
      (fun x => slope x.val) (fun x => value x.val)
      (m-2 : ℕ) (periodicGrowth m [m-2]) := by
  have hM : (1 : ℝ) < (m-2 : ℕ) := by exact_mod_cast (show 1 < m-2 by omega)
  apply integer_on_side m (m-2) hm ⟨by omega,by omega⟩ (Set.Iio (m-2 : ℕ))
    ((m-2 : ℕ)-1) (by linarith)
  intro s hs hd
  have h := (abs_lt.mp (show |s-(m-2 : ℕ)| < (m-2 : ℕ)-1 by
    simpa [Real.dist_eq] using hd)).1
  exact ⟨by linarith,le_of_lt hs⟩

end KroneckerRestrictedIntegerLimits
