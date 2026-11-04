import KroneckerSourceGradingDictionary

/- Original module: KroneckerSourceGradeBounds -/
section
/-! Source grade bounds are consequences of the two finite totals.
They justify replacing unbounded grading domains by finite domains. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceGradeBounds
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerWeights
open KroneckerSourceIntervalCounts KroneckerSourceGradingDictionary
open scoped BigOperators

def hPart {K N : ℕ} (shape : ℕ → Bool) (d : Grades K N) (i : Fin N) : ℤ :=
  if shape i.val then (d i).val else 0
def vPart {K N : ℕ} (shape : ℕ → Bool) (d : Grades K N) (i : Fin N) : ℤ :=
  if shape i.val then 0 else (d i).val

theorem hPart_nonnegative {K N : ℕ} (shape : ℕ → Bool) (d : Grades K N) (i : Fin N) :
    0≤hPart shape d i := by unfold hPart; split <;> positivity

theorem vPart_nonnegative {K N : ℕ} (shape : ℕ → Bool) (d : Grades K N) (i : Fin N) :
    0≤vPart shape d i := by unfold vPart; split <;> positivity

theorem horizontal_formula {K N : ℕ} (shape : ℕ → Bool) (d : Grades K N) :
    hWeight (rawTrace shape d) 0 N=∑i:Fin N,hPart shape d i := by
  rw [raw_eq_representative,hWeight_total]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : shape i.val <;> simp [hs,hPart,paint,hGrade,grade,representative]

theorem vertical_formula {K N : ℕ} (shape : ℕ → Bool) (d : Grades K N) :
    vWeight (rawTrace shape d) 0 N=∑i:Fin N,vPart shape d i := by
  rw [raw_eq_representative,vWeight_total]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : shape i.val <;> simp [hs,vPart,paint,vGrade,grade,representative]

theorem total_grade_sum {K N : ℕ} (shape : ℕ → Bool) (d : Grades K N) :
    hWeight (rawTrace shape d) 0 N+vWeight (rawTrace shape d) 0 N=
      ∑i:Fin N,((d i).val:ℤ) := by
  rw [horizontal_formula,vertical_formula,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : shape i.val <;> simp [hs,hPart,vPart]

theorem grade_le_total {K N : ℕ} (shape : ℕ → Bool) (d : Grades K N) (i : Fin N) :
    ((d i).val:ℤ)≤hWeight (rawTrace shape d) 0 N+vWeight (rawTrace shape d) 0 N := by
  rw [total_grade_sum]
  exact Finset.single_le_sum (fun j _ => Int.natCast_nonneg _) (Finset.mem_univ i)

theorem source_grade_bound {K N a b : ℕ} {shape : ℕ → Bool} {d : Grades K N}
    (ht : SourceTight shape a b d) (i : Fin N) : (d i).val≤a+b := by
  have h := grade_le_total shape d i
  rw [ht.2.1,ht.2.2.1] at h
  exact_mod_cast (show ((d i).val:ℤ)≤(a:ℤ)+b by omega)

theorem zero_horizontal_total {K N : ℕ} {shape : ℕ → Bool} {d : Grades K N}
    (hz : hWeight (rawTrace shape d) 0 N=0) (i : Fin N) (hi : shape i.val=true) :
    (d i).val=0 := by
  rw [horizontal_formula] at hz
  have h := Finset.single_le_sum (s:=Finset.univ) (f:=hPart shape d)
    (fun j _ => hPart_nonnegative shape d j) (Finset.mem_univ i)
  rw [hz] at h
  simp only [hPart,hi,ite_true] at h
  omega

theorem zero_vertical_total {K N : ℕ} {shape : ℕ → Bool} {d : Grades K N}
    (hz : vWeight (rawTrace shape d) 0 N=0) (i : Fin N) (hi : shape i.val=false) :
    (d i).val=0 := by
  rw [vertical_formula] at hz
  have h := Finset.single_le_sum (s:=Finset.univ) (f:=vPart shape d)
    (fun j _ => vPart_nonnegative shape d j) (Finset.mem_univ i)
  rw [hz] at h
  simp only [vPart,hi,Bool.false_eq_true,ite_false] at h
  omega

theorem rawTrace_congr {K M N : ℕ} (shape : ℕ → Bool) {d : Grades K N} {e : Grades M N}
    (h : ∀i,(d i).val=(e i).val) : rawTrace shape d=rawTrace shape e := by
  funext i
  unfold rawTrace
  split_ifs <;> simp_all only []

end KroneckerSourceGradeBounds
end
end

/- Original module: KroneckerSourceBinomialTruncation -/
section
/-! Exact finite truncation of Theorem 4.10's incoming binomial weights.
No coefficient is dropped without a proof that its contribution is zero. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceBinomialTruncation
open KroneckerWeights KroneckerSourceGradingDictionary KroneckerSourceGradeBounds
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def Within {K N : ℕ} (m : ℕ) (d : Grades K N) : Prop := ∀i,(d i).val≤m
def embed {m K N : ℕ} (hmK : m≤K) (d : Grades m N) : Grades K N :=
  fun i => ⟨(d i).val,by have := (d i).isLt; omega⟩
def lower {m K N : ℕ} (d : Grades K N) (h : Within m d) : Grades m N :=
  fun i => ⟨(d i).val,Nat.lt_succ_of_le (h i)⟩
def binomialWeight {K N : ℕ} (m : ℕ) (d : Grades K N) : ℕ := ∏i:Fin N,Nat.choose m (d i).val

theorem embed_value {m K N : ℕ} (hmK : m≤K) (d : Grades m N) (i : Fin N) :
    (embed hmK d i).val=(d i).val := rfl

theorem embed_injective {m K N : ℕ} (hmK : m≤K) :
    Function.Injective (embed (N:=N) hmK) := by
  intro d e h
  funext i
  exact Fin.ext (congrArg (fun f : Grades K N => (f i).val) h)

theorem embed_within {m K N : ℕ} (hmK : m≤K) (d : Grades m N) :
    Within m (embed hmK d) := fun i => Nat.le_of_lt_succ (d i).isLt

theorem lower_value {m K N : ℕ} (d : Grades K N) (h : Within m d) (i : Fin N) :
    (lower d h i).val=(d i).val := rfl

theorem lower_embed {m K N : ℕ} (hmK : m≤K) (d : Grades m N) :
    lower (embed hmK d) (embed_within hmK d)=d := rfl

theorem embed_lower {m K N : ℕ} (hmK : m≤K) (d : Grades K N) (h : Within m d) :
    embed hmK (lower d h)=d := rfl

def boundedEquiv {m K N : ℕ} (hmK : m≤K) : Grades m N ≃ {d : Grades K N // Within m d} where
  toFun d := ⟨embed hmK d,embed_within hmK d⟩
  invFun d := lower d.val d.property
  left_inv := lower_embed hmK
  right_inv d := Subtype.ext (embed_lower hmK d.val d.property)

theorem weight_embed {m k K N : ℕ} (hkK : k≤K) (d : Grades k N) :
    binomialWeight m (embed hkK d)=binomialWeight m d := rfl

theorem weight_zero {m K N : ℕ} (d : Grades K N) (h : ¬Within m d) :
    binomialWeight m d=0 := by
  obtain ⟨i,hi⟩ := not_forall.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (Nat.choose_eq_zero_of_lt (by omega))

theorem weight_positive_iff {m K N : ℕ} (d : Grades K N) :
    0<binomialWeight m d ↔ Within m d := by
  constructor
  · intro h
    by_contra hn
    rw [weight_zero d hn] at h
    omega
  · intro h
    exact Finset.prod_pos fun i _ => Nat.choose_pos (h i)

theorem source_tight_congr {K M N : ℕ} (shape : ℕ → Bool) (a b : ℤ)
    {d : Grades K N} {e : Grades M N} (h : ∀i,(d i).val=(e i).val) :
    SourceTight shape a b d ↔ SourceTight shape a b e := by
  unfold SourceTight
  rw [rawTrace_congr shape h]

theorem source_tight_embed {m K N : ℕ} (hmK : m≤K) (shape : ℕ → Bool) (a b : ℤ)
    (d : Grades m N) : SourceTight shape a b (embed hmK d) ↔ SourceTight shape a b d :=
  source_tight_congr shape a b fun _ => rfl

theorem sum_restrict_of_zero {m K N : ℕ} (hmK : m≤K) (f : Grades K N→ℕ)
    (hz : ∀d,¬Within m d→f d=0) :
    (∑d:Grades K N,f d)=∑d:Grades m N,f (embed hmK d) := by
  have hs := Fintype.sum_subtype_add_sum_subtype (Within m) f
  have hzsum : (∑d:{d : Grades K N // ¬Within m d},f d.val)=0 := by
    apply Finset.sum_eq_zero
    intro d _
    exact hz d.val d.property
  rw [hzsum,Nat.add_zero] at hs
  rw [← hs]
  exact (Equiv.sum_comp (boundedEquiv (N:=N) hmK) (fun d => f d.val)).symm

theorem finite_sum_restrict {m K N : ℕ} (hmK : m≤K) (P : Grades K N→Prop) :
    (∑d:Grades K N,if P d then binomialWeight m d else 0)=
      ∑d:Grades m N,if P (embed hmK d) then weight d else 0 := by
  have h := sum_restrict_of_zero hmK (fun d => if P d then binomialWeight m d else 0)
    (by intro d hd; simp [weight_zero d hd])
  exact h

def sourceSum (m K N : ℕ) (shape : ℕ → Bool) (a b : ℤ) : ℕ :=
  ∑d:Grades K N,if SourceTight shape a b d then binomialWeight m d else 0

theorem source_sum_restrict {m K N : ℕ} (hmK : m≤K) (shape : ℕ → Bool) (a b : ℤ) :
    sourceSum m K N shape a b=weightedCount (SourceTight (m:=m) (N:=N) shape a b) := by
  rw [sourceSum,finite_sum_restrict hmK]
  unfold weightedCount
  apply Finset.sum_congr rfl
  intro d _
  rw [source_tight_embed]

theorem source_sum_total_bound {m K N a b : ℕ} (hab : a+b≤K) (shape : ℕ → Bool) :
    sourceSum m K N shape a b=weightedCount (SourceTight (m:=m) (N:=N) shape a b) := by
  let L := max m K
  have hKL : K≤L := le_max_right _ _
  have hmain := source_sum_restrict (N:=N) (le_max_left m K) shape (a:ℤ) (b:ℤ)
  have hzero : ∀d:Grades L N,¬Within K d→
      (if SourceTight shape a b d then binomialWeight m d else 0)=0 := by
    intro d hn
    split_ifs with ht
    · exact False.elim (hn (fun i => (source_grade_bound ht i).trans hab))
    · rfl
  have hs := sum_restrict_of_zero hKL _ hzero
  have hcut : sourceSum m L N shape a b=sourceSum m K N shape a b := by
    unfold sourceSum
    rw [hs]
    apply Finset.sum_congr rfl
    intro d _
    rw [source_tight_embed,weight_embed]
  exact hcut.symm.trans hmain

end KroneckerSourceBinomialTruncation
end
end

/- Original module: KroneckerSourceNaturalGradings -/
section
/-! The published grading domain is nonnegative integers, not bounded colors.
Its tight subset is finite because the two prescribed totals bound each grade. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceNaturalGradings
open KroneckerStack KroneckerCompatibility KroneckerWeights
open KroneckerSourceIntervalCounts KroneckerSourceCompatibility
open KroneckerSourceGradingDictionary KroneckerSourceGradeBounds
open scoped BigOperators

def naturalTrace {N : ℕ} (shape : ℕ → Bool) (g : Fin N→ℕ) (i : ℕ) : Edge :=
  if h : N=0 then .H 0 else
  if shape (i%N) then .H (g ⟨i%N,Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩)
  else .V (g ⟨i%N,Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩)

def NaturalTight {N : ℕ} (shape : ℕ → Bool) (a b : ℕ) (g : Fin N→ℕ) : Prop :=
  Cyclic (naturalTrace shape g) N ∧ hWeight (naturalTrace shape g) 0 N=(b:ℤ) ∧
    vWeight (naturalTrace shape g) 0 N=(a:ℤ) ∧
    KroneckerSourceHorizontalShadow.Support (naturalTrace shape g) N

def capacity {N : ℕ} (g : Fin N→ℕ) : ℕ := ∑i:Fin N,g i

theorem natural_trace_before {N : ℕ} (shape : ℕ → Bool) (g : Fin N→ℕ) (i : Fin N) :
    naturalTrace shape g i.val=if shape i.val then .H (g i) else .V (g i) := by
  simp [naturalTrace,Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) i.isLt),Nat.mod_eq_of_lt i.isLt]

theorem trace_of_bounded {K N : ℕ} (shape : ℕ → Bool) (d : Grades K N) :
    naturalTrace shape (fun i => (d i).val)=rawTrace shape d := rfl

theorem natural_tight_bounded_iff {K N a b : ℕ} (shape : ℕ → Bool) (d : Grades K N) :
    NaturalTight shape a b (fun i => (d i).val) ↔ SourceTight shape a b d := Iff.rfl

theorem grade_le_capacity {N : ℕ} (g : Fin N→ℕ) (i : Fin N) : g i≤capacity g :=
  Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

def encode {N : ℕ} (g : Fin N→ℕ) : Grades (capacity g) N :=
  fun i => ⟨g i,Nat.lt_succ_of_le (grade_le_capacity g i)⟩

theorem encode_value {N : ℕ} (g : Fin N→ℕ) (i : Fin N) : (encode g i).val=g i := rfl

theorem encode_trace {N : ℕ} (shape : ℕ → Bool) (g : Fin N→ℕ) :
    rawTrace shape (encode g)=naturalTrace shape g := rfl

theorem natural_total {N : ℕ} (shape : ℕ → Bool) (g : Fin N→ℕ) :
    hWeight (naturalTrace shape g) 0 N+vWeight (naturalTrace shape g) 0 N=(capacity g:ℤ) := by
  rw [← encode_trace shape g,total_grade_sum]
  simp [capacity,encode]

theorem capacity_of_tight {N a b : ℕ} {shape : ℕ → Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) : capacity g=a+b := by
  have h := natural_total shape g
  rw [ht.2.1,ht.2.2.1] at h
  omega

theorem natural_grade_bound {N a b : ℕ} {shape : ℕ → Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) (i : Fin N) : g i≤a+b := by
  rw [← capacity_of_tight ht]
  exact grade_le_capacity g i

def cap {N a b : ℕ} {shape : ℕ → Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) : Grades (a+b) N :=
  fun i => ⟨g i,Nat.lt_succ_of_le (natural_grade_bound ht i)⟩

theorem cap_trace {N a b : ℕ} {shape : ℕ → Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) : rawTrace shape (cap ht)=naturalTrace shape g := rfl

theorem cap_tight {N a b : ℕ} {shape : ℕ → Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) : SourceTight shape a b (cap ht) := ht

def tightEquiv (N a b : ℕ) (shape : ℕ → Bool) :
    {g : Fin N→ℕ // NaturalTight shape a b g} ≃
      {d : Grades (a+b) N // SourceTight shape a b d} where
  toFun g := ⟨cap g.property,cap_tight g.property⟩
  invFun d := ⟨fun i => (d.val i).val,d.property⟩
  left_inv g := rfl
  right_inv d := rfl

theorem tightEquiv_preserves_grades {N a b : ℕ} {shape : ℕ → Bool}
    (g : {g : Fin N→ℕ // NaturalTight shape a b g}) (i : Fin N) :
    (((tightEquiv N a b shape) g).val i).val=g.val i := rfl

theorem natural_tight_finite (N a b : ℕ) (shape : ℕ → Bool) :
    Finite {g : Fin N→ℕ // NaturalTight shape a b g} :=
  Finite.of_equiv _ (tightEquiv N a b shape).symm

theorem natural_tight_card (N a b : ℕ) (shape : ℕ → Bool) :
    Nat.card {g : Fin N→ℕ // NaturalTight shape a b g}=
      Nat.card {d : Grades (a+b) N // SourceTight shape a b d} :=
  Nat.card_congr (tightEquiv N a b shape)

end KroneckerSourceNaturalGradings
end
end
