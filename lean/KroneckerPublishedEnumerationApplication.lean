import KroneckerSourceNaturalGradings
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import KroneckerSourceParameterGates
import Mathlib.Algebra.Polynomial.Coeff

/- Original module: KroneckerSourcePartitions -/
section
/-! Source partitions: positive vertical grades first, horizontal grades second.
Incoming constant coefficients are 1, so discarding zero parts preserves weight. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourcePartitions
open KroneckerStack KroneckerWeights KroneckerSourceIntervalCounts
open KroneckerSourceNaturalGradings KroneckerSourceGradeBounds
open scoped BigOperators

def hTerm {N : ℕ} (shape : ℕ→Bool) (g : Fin N→ℕ) (i : Fin N) := if shape i.val then g i else 0
def vTerm {N : ℕ} (shape : ℕ→Bool) (g : Fin N→ℕ) (i : Fin N) := if shape i.val then 0 else g i
def hTotal {N : ℕ} (shape : ℕ→Bool) (g : Fin N→ℕ) := ∑i:Fin N,hTerm shape g i
def vTotal {N : ℕ} (shape : ℕ→Bool) (g : Fin N→ℕ) := ∑i:Fin N,vTerm shape g i

theorem horizontal_total_cast {N : ℕ} (shape : ℕ→Bool) (g : Fin N→ℕ) :
    (hTotal shape g:ℤ)=hWeight (naturalTrace shape g) 0 N := by
  rw [← encode_trace shape g,horizontal_formula]
  unfold hTotal
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  cases hs : shape i.val <;> simp [hs,hTerm,hPart,encode]

theorem vertical_total_cast {N : ℕ} (shape : ℕ→Bool) (g : Fin N→ℕ) :
    (vTotal shape g:ℤ)=vWeight (naturalTrace shape g) 0 N := by
  rw [← encode_trace shape g,vertical_formula]
  unfold vTotal
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  cases hs : shape i.val <;> simp [hs,vTerm,vPart,encode]

theorem horizontal_total_of_tight {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) : hTotal shape g=b := by
  exact_mod_cast ((horizontal_total_cast shape g).trans ht.2.1)

theorem vertical_total_of_tight {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) : vTotal shape g=a := by
  exact_mod_cast ((vertical_total_cast shape g).trans ht.2.2.1)

def horizontalPartition {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) : Nat.Partition b :=
  Nat.Partition.ofSums b (Finset.univ.val.map (hTerm shape g)) (horizontal_total_of_tight ht)
def verticalPartition {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) : Nat.Partition a :=
  Nat.Partition.ofSums a (Finset.univ.val.map (vTerm shape g)) (vertical_total_of_tight ht)

def signature {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) : Nat.Partition a × Nat.Partition b :=
  (verticalPartition ht,horizontalPartition ht)

theorem horizontal_parts_member {N a b k : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) :
    k∈(horizontalPartition ht).parts ↔ ∃i:Fin N,shape i.val=true ∧ g i=k ∧ 0<k := by
  simp only [horizontalPartition,Nat.Partition.ofSums,Multiset.mem_filter,Multiset.mem_map,
    Finset.mem_val,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨i,hi⟩,hk⟩
    by_cases hs : shape i.val=true
    · exact ⟨i,hs,by simpa [hTerm,hs] using hi,Nat.pos_of_ne_zero hk⟩
    · simp [hTerm,hs] at hi
      exact False.elim (hk hi.symm)
  · rintro ⟨i,hs,hg,hk⟩
    exact ⟨⟨i,by simp [hTerm,hs,hg]⟩,Nat.ne_of_gt hk⟩

theorem vertical_parts_member {N a b k : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) :
    k∈(verticalPartition ht).parts ↔ ∃i:Fin N,shape i.val=false ∧ g i=k ∧ 0<k := by
  simp only [verticalPartition,Nat.Partition.ofSums,Multiset.mem_filter,Multiset.mem_map,
    Finset.mem_val,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨i,hi⟩,hk⟩
    cases hs : shape i.val
    · exact ⟨i,hs,by simpa [vTerm,hs] using hi,Nat.pos_of_ne_zero hk⟩
    · simp [vTerm,hs] at hi
      exact False.elim (hk hi.symm)
  · rintro ⟨i,hs,hg,hk⟩
    exact ⟨⟨i,by simp [vTerm,hs,hg]⟩,Nat.ne_of_gt hk⟩

def partitionWeight {R : Type*} [CommMonoid R] {n : ℕ} (c : ℕ→R) (p : Nat.Partition n) : R :=
  (p.parts.map c).prod

theorem partition_product_ignore_zero {R : Type*} [CommMonoid R] (c : ℕ→R) (h0 : c 0=1)
    {n : ℕ} (s : Multiset ℕ) (hs : s.sum=n) :
    partitionWeight c (Nat.Partition.ofSums n s hs)=(s.map c).prod := by
  unfold partitionWeight Nat.Partition.ofSums
  have hz : ((s.filter (fun k => k=0)).map c).prod=1 := by
    apply Multiset.prod_eq_one
    intro x hx
    obtain ⟨k,hk,rfl⟩ := Multiset.mem_map.mp hx
    rw [(Multiset.mem_filter.mp hk).2,h0]
  conv_rhs => rw [← Multiset.filter_add_not (fun k => k=0) s]
  rw [Multiset.map_add,Multiset.prod_add,hz,one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem horizontal_weight {R : Type*} [CommMonoid R] (c : ℕ→R) (h0 : c 0=1)
    {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ} (ht : NaturalTight shape a b g) :
    partitionWeight c (horizontalPartition ht)=∏i:Fin N,c (hTerm shape g i) := by
  unfold horizontalPartition
  rw [partition_product_ignore_zero c h0,Multiset.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem vertical_weight {R : Type*} [CommMonoid R] (c : ℕ→R) (h0 : c 0=1)
    {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ} (ht : NaturalTight shape a b g) :
    partitionWeight c (verticalPartition ht)=∏i:Fin N,c (vTerm shape g i) := by
  unfold verticalPartition
  rw [partition_product_ignore_zero c h0,Multiset.map_map]
  rfl

theorem source_weight_partitions {R : Type*} [CommMonoid R] (c₁ c₂ : ℕ→R)
    (h₁ : c₁ 0=1) (h₂ : c₂ 0=1) {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) :
    (∏i:Fin N,if shape i.val then c₂ (g i) else c₁ (g i))=
      partitionWeight c₁ (verticalPartition ht)*partitionWeight c₂ (horizontalPartition ht) := by
  rw [horizontal_weight c₂ h₂,vertical_weight c₁ h₁,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases hs : shape i.val <;> simp [hs,hTerm,vTerm,h₁,h₂]

theorem binomial_partitions (m : ℕ) {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) :
    (∏i:Fin N,Nat.choose m (g i))=
      partitionWeight (Nat.choose m) (verticalPartition ht)*
      partitionWeight (Nat.choose m) (horizontalPartition ht) := by
  simpa using source_weight_partitions (Nat.choose m) (Nat.choose m) (by simp) (by simp) ht

theorem rational_binomial_partitions (m : ℕ) {N a b : ℕ} {shape : ℕ→Bool} {g : Fin N→ℕ}
    (ht : NaturalTight shape a b g) :
    (∏i:Fin N,(Nat.choose m (g i):ℚ))=
      partitionWeight (fun k => (Nat.choose m k:ℚ)) (verticalPartition ht)*
      partitionWeight (fun k => (Nat.choose m k:ℚ)) (horizontalPartition ht) := by
  simpa using source_weight_partitions (fun k => (Nat.choose m k:ℚ))
    (fun k => (Nat.choose m k:ℚ)) (by simp) (by simp) ht

end KroneckerSourcePartitions
end
end

/- Original module: KroneckerSourcePartitionSums -/
section
/-! Reindex the literal grading sum by its two source partitions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourcePartitionSums
open KroneckerWeights KroneckerSourceNaturalGradings KroneckerSourcePartitions
open KroneckerSourceGradingDictionary KroneckerSourceBinomialTruncation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Grading (N a b : ℕ) (shape : ℕ→Bool) := {g : Fin N→ℕ // NaturalTight shape a b g}
instance gradingFinite (N a b : ℕ) (shape : ℕ→Bool) : Finite (Grading N a b shape) :=
  natural_tight_finite N a b shape
instance gradingFintype (N a b : ℕ) (shape : ℕ→Bool) : Fintype (Grading N a b shape) := Fintype.ofFinite _

def sig {N a b : ℕ} {shape : ℕ→Bool} (g : Grading N a b shape) : Nat.Partition a × Nat.Partition b :=
  signature g.property

def coefficient (N a b : ℕ) (shape : ℕ→Bool) (P : Nat.Partition a × Nat.Partition b) : ℕ :=
  Nat.card {g : Grading N a b shape // sig g=P}

def sigWeight {R : Type*} [CommMonoid R] {a b : ℕ} (c₁ c₂ : ℕ→R)
    (P : Nat.Partition a × Nat.Partition b) : R := partitionWeight c₁ P.1*partitionWeight c₂ P.2

def naturalSum {R : Type*} [CommSemiring R] (N a b : ℕ) (shape : ℕ→Bool) (c₁ c₂ : ℕ→R) : R :=
  ∑g:Grading N a b shape,∏i:Fin N,if shape i.val then c₂ (g.val i) else c₁ (g.val i)

def partitionSum {R : Type*} [CommSemiring R] (N a b : ℕ) (shape : ℕ→Bool) (c₁ c₂ : ℕ→R) : R :=
  ∑P:Nat.Partition a × Nat.Partition b,(coefficient N a b shape P:R)*sigWeight c₁ c₂ P

theorem weight_is_signature {R : Type*} [CommMonoid R] {N a b : ℕ} {shape : ℕ→Bool}
    (c₁ c₂ : ℕ→R) (h₁ : c₁ 0=1) (h₂ : c₂ 0=1) (g : Grading N a b shape) :
    (∏i:Fin N,if shape i.val then c₂ (g.val i) else c₁ (g.val i))=sigWeight c₁ c₂ (sig g) :=
  source_weight_partitions c₁ c₂ h₁ h₂ g.property

theorem fiber_weight_constant {R : Type*} [CommMonoid R] {N a b : ℕ} {shape : ℕ→Bool}
    (c₁ c₂ : ℕ→R) (h₁ : c₁ 0=1) (h₂ : c₂ 0=1) (P : Nat.Partition a × Nat.Partition b)
    (g : {g : Grading N a b shape // sig g=P}) :
    (∏i:Fin N,if shape i.val then c₂ (g.val.val i) else c₁ (g.val.val i))=sigWeight c₁ c₂ P := by
  rw [weight_is_signature c₁ c₂ h₁ h₂,g.property]

theorem fiber_sum {R : Type*} [CommSemiring R] {N a b : ℕ} {shape : ℕ→Bool}
    (c₁ c₂ : ℕ→R) (h₁ : c₁ 0=1) (h₂ : c₂ 0=1) (P : Nat.Partition a × Nat.Partition b) :
    (∑g:{g : Grading N a b shape // sig g=P},
      ∏i:Fin N,if shape i.val then c₂ (g.val.val i) else c₁ (g.val.val i))=
      (coefficient N a b shape P:R)*sigWeight c₁ c₂ P := by
  simp only [fiber_weight_constant c₁ c₂ h₁ h₂,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,coefficient,Nat.card_eq_fintype_card]

theorem reindex_partitions {R : Type*} [CommSemiring R] (N a b : ℕ) (shape : ℕ→Bool)
    (c₁ c₂ : ℕ→R) (h₁ : c₁ 0=1) (h₂ : c₂ 0=1) :
    naturalSum N a b shape c₁ c₂=partitionSum N a b shape c₁ c₂ := by
  let f := fun g : Grading N a b shape => ∏i:Fin N,if shape i.val then c₂ (g.val i) else c₁ (g.val i)
  have h := Equiv.sum_comp (Equiv.sigmaFiberEquiv (sig (N:=N) (a:=a) (b:=b) (shape:=shape))) f
  rw [Fintype.sum_sigma] at h
  unfold naturalSum partitionSum
  rw [← h]
  apply Finset.sum_congr rfl
  intro P _
  exact fiber_sum c₁ c₂ h₁ h₂ P

theorem coefficient_counts_literal (N a b : ℕ) (shape : ℕ→Bool) (P : Nat.Partition a × Nat.Partition b) :
    coefficient N a b shape P=Nat.card {g : Grading N a b shape //
      verticalPartition g.property=P.1 ∧ horizontalPartition g.property=P.2} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun g => Prod.mk_inj

theorem total_coefficients (N a b : ℕ) (shape : ℕ→Bool) :
    (∑P:Nat.Partition a × Nat.Partition b,coefficient N a b shape P)=Nat.card (Grading N a b shape) := by
  have h := reindex_partitions N a b shape (fun _ => (1:ℕ)) (fun _ => (1:ℕ)) rfl rfl
  simpa [naturalSum,partitionSum,sigWeight,partitionWeight,Nat.card_eq_fintype_card] using h.symm

theorem natural_binomial_to_bounded (m N a b : ℕ) (shape : ℕ→Bool) :
    naturalSum N a b shape (Nat.choose m) (Nat.choose m)=sourceSum m (a+b) N shape a b := by
  unfold naturalSum sourceSum
  have h := Equiv.sum_comp (tightEquiv N a b shape).symm
    (fun g : Grading N a b shape => ∏i:Fin N,Nat.choose m (g.val i))
  simp only [ite_self]
  rw [← h]
  change (∑d:{d:Grades (a+b) N // SourceTight shape a b d},binomialWeight m d.val)=_
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (SourceTight (m:=a+b) (N:=N) shape a b))
    (by intro d; simp) (binomialWeight m)).symm

theorem natural_binomial_to_colored (m N a b : ℕ) (shape : ℕ→Bool) :
    naturalSum N a b shape (Nat.choose m) (Nat.choose m)=
      weightedCount (SourceTight (m:=m) (N:=N) shape a b) := by
  rw [natural_binomial_to_bounded,source_sum_total_bound (le_refl _)]

theorem binomial_partition_to_colored (m N a b : ℕ) (shape : ℕ→Bool) :
    partitionSum N a b shape (Nat.choose m) (Nat.choose m)=
      weightedCount (SourceTight (m:=m) (N:=N) shape a b) := by
  rw [← reindex_partitions N a b shape (Nat.choose m) (Nat.choose m) (by simp) (by simp),
    natural_binomial_to_colored]

theorem rational_partition_to_colored (m N a b : ℕ) (shape : ℕ→Bool) :
    partitionSum N a b shape (fun k => (Nat.choose m k:ℚ)) (fun k => (Nat.choose m k:ℚ))=
      (weightedCount (SourceTight (m:=m) (N:=N) shape a b):ℚ) := by
  rw [← reindex_partitions N a b shape _ _ (by simp) (by simp)]
  have h := natural_binomial_to_colored m N a b shape
  apply_fun (fun x : ℕ => (x:ℚ)) at h
  simpa [naturalSum] using h

end KroneckerSourcePartitionSums
end
end

/- Original module: KroneckerPublishedEnumerationApplication -/
section
/-! The incoming polynomial and its finite partition-weight dictionary.
The accepted finite enumeration input is in KroneckerFiniteCoefficientIntegration. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPublishedEnumerationApplication
open KroneckerWeights KroneckerColoring KroneckerStack KroneckerFrameIdentity
open KroneckerSourceMaximalPath KroneckerSourceGradingDictionary
open KroneckerSourcePartitions KroneckerSourcePartitionSums KroneckerSourceParameterGates
open scoped BigOperators

def incoming (m : ℕ) : Polynomial ℚ := (1+Polynomial.X)^m

theorem incoming_coefficient (m k : ℕ) : (incoming m).coeff k=(Nat.choose m k:ℚ) :=
  Polynomial.coeff_one_add_X_pow ℚ m k

theorem incoming_constant (m : ℕ) : (incoming m).coeff 0=1 := by rw [incoming_coefficient]; simp

theorem incoming_degree_cutoff (m k : ℕ) (hk : m<k) : (incoming m).coeff k=0 := by
  rw [incoming_coefficient,Nat.choose_eq_zero_of_lt hk,Nat.cast_zero]

theorem incoming_partition_weight (m n : ℕ) (P : Nat.Partition n) :
    partitionWeight (incoming m).coeff P=partitionWeight (fun k => (Nat.choose m k:ℚ)) P := by
  congr 1
  funext k
  exact incoming_coefficient m k

theorem incoming_partition_enumeration (m N a b : ℕ) (shape : ℕ→Bool) :
    partitionSum N a b shape (incoming m).coeff (incoming m).coeff=
      (weightedCount (SourceTight (m:=m) (N:=N) shape a b):ℚ) := by
  have hc : (incoming m).coeff=(fun k => (Nat.choose m k:ℚ)) := funext (incoming_coefficient m)
  rw [hc,rational_partition_to_colored]

end KroneckerPublishedEnumerationApplication
end
end
