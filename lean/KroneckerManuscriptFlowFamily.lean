import KroneckerManuscriptFlowIntervals
import KroneckerEnumeratedStableExistence
import KroneckerChainRepresentativeStability

/-! The manuscript family F_{a,k}, with k = n+2 and t = i.val+1.
The functions here are actual edge flows on the labeled chain incidence type. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace KroneckerManuscriptFlowFamily
open KroneckerChainIncidence KroneckerChainLatticeParameters
open KroneckerChainFlowIntegrality KroneckerChainFlowWeights
open KroneckerIncidenceDivergence KroneckerFlowEdgeExtension
open KroneckerFiniteStateBins KroneckerFiniteBinLattices
open KroneckerEnumeratedStableExistence KroneckerChainBlockSizes

structure Coordinates (n : ℕ) (x : ℝ) where
  l : Connector n → ℝ
  r : Connector n → ℝ
  left_mem : ∀ t, x/256 ≤ l t ∧ l t < 2*x/256
  right_mem : ∀ t, 0 < r t ∧ r t < x/256
  left_lattice : ∀ t, OnLattice (offset x t) (l t)
  right_lattice : ∀ t, OnLattice (-offset x t) (r t)

def toFlow {n : ℕ} {x : ℝ} (C : Coordinates n x) : Edge (@incidence n) → ℝ :=
  chainFlow x (extend C.l) (extend C.r)

def Family (a n : ℕ) : Set (Edge (@incidence n) → ℝ) :=
  {f | ∃ C : Coordinates n ((a : ℝ)/((n : ℝ)+2)), toFlow C = f}

def sourceDimension {n : ℕ} (x : ℝ) (f : Edge (@incidence n) → ℝ) (b : Block n) : ℝ :=
  x - ∑ i : Connector n, extendFlow f i b

theorem port_values {n : ℕ} {x : ℝ} (C : Coordinates n x) (t : Connector n) :
    toFlow C ⟨(t,portBlock t 0),port_incident t 0⟩ = C.l t ∧
    toFlow C ⟨(t,portBlock t 1),port_incident t 1⟩ = x+1-C.l t-C.r t ∧
    toFlow C ⟨(t,portBlock t 2),port_incident t 2⟩ = C.r t := by
  simpa only [toFlow,chainFlow,extend_at] using port_weights x (extend C.l) (extend C.r) t

theorem sourceDimension_eq {n : ℕ} {x : ℝ} (C : Coordinates n x) (b : Block n) :
    sourceDimension x (toFlow C) b = blockSize n x (extend C.l) (extend C.r) b := by
  unfold sourceDimension toFlow
  rw [KroneckerChainFlowEquations.column_balance]
  ring

theorem canonical_right_bin (n : ℕ) (t : Connector n) :
    rightBin (canonicalBins n).2 t = 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) t <;> simp [rightBin,canonicalBins]

def toCanonical {n : ℕ} {x : ℝ} (C : Coordinates n x) : LatticeFor x (canonicalBins n) := by
  constructor
  · intro t
    refine ⟨(C.left_lattice t).choose, ?_⟩
    change (C.left_lattice t).choose ∈ binIndices x (offset x t) 1
    rw [KroneckerManuscriptFlowIntervals.left_interval, ←(C.left_lattice t).choose_spec]
    exact C.left_mem t
  · intro t
    refine ⟨(C.right_lattice t).choose, ?_⟩
    rw [canonical_right_bin, KroneckerManuscriptFlowIntervals.right_interval,
      ←(C.right_lattice t).choose_spec]
    exact C.right_mem t

theorem leftFlow_toCanonical {n : ℕ} {x : ℝ} (C : Coordinates n x) :
    leftFlow (toCanonical C) = extend C.l := by
  funext t
  by_cases ht : t < n+1
  · simp only [leftFlow,extend,dite_eq_left ht,toCanonical]
    exact (C.left_lattice ⟨t,ht⟩).choose_spec.symm
  · simp [leftFlow,extend,ht]

theorem rightFlow_toCanonical {n : ℕ} {x : ℝ} (C : Coordinates n x) :
    rightFlow (toCanonical C) = extend C.r := by
  funext t
  by_cases ht : t < n+1
  · simp only [rightFlow,extend,dite_eq_left ht,toCanonical]
    exact (C.right_lattice ⟨t,ht⟩).choose_spec.symm
  · simp [rightFlow,extend,ht]

def ofCanonical {n : ℕ} {x : ℝ} (L : LatticeFor x (canonicalBins n)) : Coordinates n x where
  l t := leftFlow L t
  r t := rightFlow L t
  left_mem t := by
    have h := (KroneckerManuscriptFlowIntervals.left_interval x (offset x t) (L.1 t).val).mp (L.1 t).property
    simpa only [leftFlow,extend_at] using h
  right_mem t := by
    have hm : (L.2 t).val ∈ positiveBinIndices x (-offset x t) 0 :=
      (congrArg (fun b => (L.2 t).val ∈ positiveBinIndices x (-offset x t) b)
        (canonical_right_bin n t)).mp (L.2 t).property
    have h := (KroneckerManuscriptFlowIntervals.right_interval x (offset x t) (L.2 t).val).mp hm
    simpa only [rightFlow,extend_at] using h
  left_lattice t := ⟨(L.1 t).val, by simp only [leftFlow,extend_at]⟩
  right_lattice t := ⟨(L.2 t).val, by simp only [rightFlow,extend_at]⟩

theorem positive {n : ℕ} {x : ℝ} (C : Coordinates n x) (hx : 100000 ≤ x) :
    ∀ e, 0 < toFlow C e := by
  have h := KroneckerChainBinFamily.bin_flows_positive n x _ _ _ _ hx
    (lattice_parameter_bins (toCanonical C))
  simpa only [leftFlow_toCanonical,rightFlow_toCanonical,toFlow] using h

theorem dimension_bounds {n : ℕ} {x : ℝ} (C : Coordinates n x) (hx : 100000 ≤ x) :
    ∀ b, 256 < sourceDimension x (toFlow C) b ∧ sourceDimension x (toFlow C) b < x := by
  have h := KroneckerChainBinFamily.bin_block_size_bounds n x _ _ _ _ hx
    (lattice_parameter_bins (toCanonical C))
  simpa only [leftFlow_toCanonical,rightFlow_toCanonical,sourceDimension_eq] using h

theorem dimension_sum {n a : ℕ} {x : ℝ} (C : Coordinates n x)
    (ha : ((n : ℝ)+2)*x=a) :
    (∑ b, sourceDimension x (toFlow C) b) = (a : ℝ)-((n : ℝ)+1) := by
  simp only [sourceDimension_eq,block_size_sum,ha]

theorem dimensions_integral {n a : ℕ} {x : ℝ} (C : Coordinates n x)
    (ha : ((n : ℝ)+2)*x=a) :
    ∀ b, ∃ z : ℤ, sourceDimension x (toFlow C) b = z := by
  have h := KroneckerChainIntegerDimensions.all_block_sizes_integral n a x _ _ ha
    (lattice_parameter_integrality (toCanonical C)).1 (lattice_parameter_integrality (toCanonical C)).2
  simpa only [leftFlow_toCanonical,rightFlow_toCanonical,sourceDimension_eq] using h

/-- Equal block dimensions determine the flow. Only tree-flow uniqueness is used. -/
theorem sourceDimension_injective (a n : ℕ) :
    Function.Injective (fun f : Family a n =>
      sourceDimension ((a : ℝ)/((n : ℝ)+2)) f.val) := by
  rintro ⟨f,⟨C,rfl⟩⟩ ⟨g,⟨D,rfl⟩⟩ h
  apply Subtype.ext
  apply KroneckerTreeFlowUniqueness.tree_divergence_injective
    (@incidence n) (KroneckerChainSkeletonTree.chain_tree n)
  funext v
  cases v with
  | inl i =>
    rw [←extended_row,←extended_row]
    exact (row_balance _ (extend C.l) (extend C.r) i).trans
      (row_balance _ (extend D.l) (extend D.r) i).symm
  | inr b =>
    have hb := congrFun h b
    dsimp only [sourceDimension] at hb
    rw [extended_column,extended_column] at hb
    linarith

end KroneckerManuscriptFlowFamily

#print axioms KroneckerManuscriptFlowFamily.Coordinates
#print axioms KroneckerManuscriptFlowFamily.toFlow
#print axioms KroneckerManuscriptFlowFamily.Family
#print axioms KroneckerManuscriptFlowFamily.sourceDimension
#print axioms KroneckerManuscriptFlowFamily.port_values
#print axioms KroneckerManuscriptFlowFamily.sourceDimension_eq
#print axioms KroneckerManuscriptFlowFamily.toCanonical
#print axioms KroneckerManuscriptFlowFamily.ofCanonical
#print axioms KroneckerManuscriptFlowFamily.positive
#print axioms KroneckerManuscriptFlowFamily.dimension_bounds
#print axioms KroneckerManuscriptFlowFamily.dimension_sum
#print axioms KroneckerManuscriptFlowFamily.dimensions_integral

#print axioms KroneckerManuscriptFlowFamily.sourceDimension_injective
