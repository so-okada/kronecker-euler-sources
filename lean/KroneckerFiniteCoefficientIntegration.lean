import KroneckerPublishedInputBoundary
import KroneckerScopedActualFrameApplication
import KroneckerPublishedEnumerationApplication
import KroneckerDirectCoprimePosition
import KroneckerCitedGeometry
import KroneckerExchangeEuler

/-! Finite enumeration is derived from BLMMR Theorems 3.2 and 4.10 and
Reineke--Weist Theorem 12.1. Existence of a formal solution is proved by
coefficient recursion; the common-series equality follows by uniqueness.
All statements use equal parameters.
The auxiliary series used by the application are algebraic packaging;
they are not identified with geometric scattering walls.
See audit/common-series-theorem32-20261101/SOURCE-CORRESPONDENCE.md. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFiniteCoefficientIntegration
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerFrameIdentity KroneckerColoring
open KroneckerWeights KroneckerSourceMaximalPath KroneckerSourcePartitions
open KroneckerSourcePartitionSums KroneckerSourceParameterGates
open KroneckerPublishedEnumerationApplication
open scoped BigOperators

structure FiniteEnumeration (G : Geometry) where
  lambda : ∀ a b, Nat.Partition a × Nat.Partition b → ℕ
  count : ∀ a b d₁ d₂ (shape : ℕ → Bool), 0<a → 0<b → a≤d₁ → b≤d₂ →
    Maximal d₁ d₂ shape → (a:ℤ)*d₂-(b:ℤ)*d₁=-(Nat.gcd a b:ℕ) →
    ∀ P : Nat.Partition a × Nat.Partition b,
      lambda a b P=coefficient (d₁+d₂) a b shape P
  primitive_euler : ∀ m a b, 3≤m → 0<a → 0<b → a.Coprime b →
    (∑ P : Nat.Partition a × Nat.Partition b, (lambda a b P:ℚ) *
      sigWeight (incoming m).coeff (incoming m).coeff P) =
      (m:ℚ)*(G.euler (KroneckerAllMPublishedDatum.datum m a b):ℚ)

end KroneckerFiniteCoefficientIntegration

namespace KroneckerFiniteEnumerationSourceSplit
open KroneckerScopedModuli KroneckerSourceMaximalPath
open KroneckerSourcePartitions KroneckerSourcePartitionSums
open KroneckerPublishedEnumerationApplication
open KroneckerOrdinarySingularEuler
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

/-- BLMMR Theorem 4.10(2): the negative-determinant counting statement,
with its coefficient series specialized to incoming polynomials (1+x)^m.
The first partition records vertical weights, the second horizontal weights.
The fields `wall`, `constant`, and `expansion` package that series algebraically.
The geometric identification in 4.10(1) enters through `BLMMRTheorem32`. -/
structure BLMMRTheorem410 where
  lambda : ∀ a b, Nat.Partition a × Nat.Partition b → ℕ
  count : ∀ a b d₁ d₂ (shape : ℕ → Bool), 0 < a → 0 < b → a ≤ d₁ → b ≤ d₂ →
    Maximal d₁ d₂ shape → (a : ℤ) * d₂ - (b : ℤ) * d₁ = -(Nat.gcd a b : ℕ) →
    ∀ P : Nat.Partition a × Nat.Partition b,
      lambda a b P = coefficient (d₁ + d₂) a b shape P
  wall : ℕ → ℕ → ℕ → PowerSeries ℚ
  constant : ∀ m a b, PowerSeries.constantCoeff (wall m a b) = 1
  expansion : ∀ m a b k, 3 ≤ m → 0 < a → 0 < b → a.Coprime b → 0 < k →
    PowerSeries.coeff k (wall m a b) =
      ∑ P : Nat.Partition (k * a) × Nat.Partition (k * b),
      (lambda (k * a) (k * b) P : ℚ) *
        sigWeight (incoming m).coeff (incoming m).coeff P

/-- Ordered length-m partitions, including zero entries as in RW Section 3.
They are different types from the unordered partitions in BLMMR. -/
abbrev OrderedPartition (m n : ℕ) :=
  {p : Fin m → Fin (n + 1) // ∑ i, (p i).val = n}

/-- RW's complete bipartite quiver K(m,m): arrows go from the second
ordered partition to the first. The weight is negative on proper subobjects. -/
def bipartiteDatum {m a b : ℕ} (P : OrderedPartition m a) (Q : OrderedPartition m b) : Datum where
  V := Fin m ⊕ Fin m
  A := Fin m × Fin m
  vertices := inferInstance
  arrows := inferInstance
  source e := Sum.inr e.2
  target e := Sum.inl e.1
  dimension := Sum.elim (fun i => (P.val i).val) (fun j => (Q.val j).val)
  weight := Sum.elim (fun _ => -(b : ℤ)) (fun _ => (a : ℤ))

theorem bipartite_acyclic {m a b : ℕ}
    (P : OrderedPartition m a) (Q : OrderedPartition m b) : Acyclic (bipartiteDatum P Q) := by
  refine ⟨Sum.elim (fun _ => 1) (fun _ => 0), ?_⟩
  intro e
  change (0 : ℕ) < 1
  decide

theorem bipartite_balanced {m a b : ℕ}
    (P : OrderedPartition m a) (Q : OrderedPartition m b) : Balanced (bipartiteDatum P Q) := by
  have hp : (∑ i, ((P.val i).val : ℤ)) = a := by exact_mod_cast P.property
  have hq : (∑ j, ((Q.val j).val : ℤ)) = b := by exact_mod_cast Q.property
  change (∑ v : Fin m ⊕ Fin m,
    (Sum.elim (fun _ => -(b : ℤ)) (fun _ => (a : ℤ)) v) *
      ((Sum.elim (fun i => (P.val i).val) (fun j => (Q.val j).val) v : ℕ) : ℤ)) = 0
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum]
  rw [hp, hq]
  ring

/-- Actual ordinary singular Euler characteristic of the stable quotient.
Finite homology uses the existing King--Reineke--Dimca input. -/
def bipartiteEuler {m a b : ℕ} (P : OrderedPartition m a) (Q : OrderedPartition m b) : ℤ :=
  ordinaryEuler (canonical (bipartiteDatum P Q))
    (Classical.choice (KroneckerCitedGeometry.king_dimca_realization (bipartiteDatum P Q)
      (bipartite_acyclic P Q) (bipartite_balanced P Q))).canonicalAdmissible

def bipartiteSum (m a b : ℕ) : ℤ :=
  ∑ P : OrderedPartition m a, ∑ Q : OrderedPartition m b, bipartiteEuler P Q

/-- Generalized binomial coefficient over Q. -/
def rationalBinomial (r : ℚ) (j : ℕ) : ℚ :=
  (∏ i ∈ Finset.range j, (r - (i : ℚ))) / (j.factorial : ℚ)

/-- For constant coefficient one, this is the formal binomial power f^r.
The coefficient definition uses only finite sums. -/
def rationalPower (f : PowerSeries ℚ) (r : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ∑ j ∈ Finset.range (n + 1),
    rationalBinomial r j * PowerSeries.coeff n ((f - 1) ^ j)

theorem rationalPower_constant (f : PowerSeries ℚ) (r : ℚ) :
    PowerSeries.constantCoeff (rationalPower f r) = 1 := by
  simp [rationalPower, rationalBinomial]

theorem rationalPower_linear (f : PowerSeries ℚ) (r : ℚ) :
    PowerSeries.coeff 1 (rationalPower f r) = r * PowerSeries.coeff 1 f := by
  simp [rationalPower, rationalBinomial, Finset.sum_range_succ]

/-- The equation in BLMMR Theorem 3.2 and RW Theorem 8.1 for equal
parameters m, in BLMMR Section 3's primitive-ray variable T.
The infinite product is expressed coefficientwise: factors k>n cannot affect
coefficient n. The source uses E=(m*m*a*b-m*a*a-m*b*b)/(m*m). -/
def RWFunctionalEquation (m a b : ℕ) (f : PowerSeries ℚ) : Prop :=
  PowerSeries.constantCoeff f = 1 ∧ ∀ n : ℕ,
    PowerSeries.coeff n f = PowerSeries.coeff n
      (∏ k ∈ Finset.Icc 1 n,
        rationalPower
          (1 - (PowerSeries.X * rationalPower f
            (((m : ℚ) * m * a * b - m * a * a - m * b * b) / (m * m))) ^ k)
          (-(k : ℚ) * (bipartiteSum m (k * a) (k * b) : ℚ)))

/-- BLMMR Theorem 4.10(1), followed by Theorem 3.2: identify the counting
series with the geometric wall and apply its Euler-sum functional equation.
The paper's parameters b,c are both m; its primitive pair d,e is a,b. -/
def BLMMRTheorem32 (B : BLMMRTheorem410) : Prop :=
  ∀ m a b, 3 ≤ m → 0 < a → 0 < b → a.Coprime b →
    RWFunctionalEquation m a b (B.wall m a b)

namespace RWUniqueness
open PowerSeries

/-- Agreement of all coefficients strictly below n. -/
def Agree (n : ℕ) (f g : PowerSeries ℚ) : Prop :=
  ∀ j < n, coeff j f = coeff j g

theorem agree_refl (n : ℕ) (f : PowerSeries ℚ) : Agree n f f := by
  intro j hj
  rfl

theorem agree_sub {n : ℕ} {f g u v : PowerSeries ℚ}
    (h : Agree n f g) (h' : Agree n u v) : Agree n (f - u) (g - v) := by
  intro j hj
  simp only [map_sub, h j hj, h' j hj]

theorem agree_mul {n : ℕ} {f g u v : PowerSeries ℚ}
    (h : Agree n f g) (h' : Agree n u v) : Agree n (f * u) (g * v) := by
  intro j hj
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = j := Finset.mem_antidiagonal.mp hp
  rw [h p.1 (by omega), h' p.2 (by omega)]

theorem agree_pow {n : ℕ} {f g : PowerSeries ℚ}
    (h : Agree n f g) (k : ℕ) : Agree n (f ^ k) (g ^ k) := by
  induction k with
  | zero => simpa using agree_refl n (1 : PowerSeries ℚ)
  | succ k ih => simpa only [pow_succ] using agree_mul ih h

theorem agree_prod {ι : Type*} (s : Finset ι) {n : ℕ}
    {f g : ι → PowerSeries ℚ} (h : ∀ i ∈ s, Agree n (f i) (g i)) :
    Agree n (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using agree_refl n (1 : PowerSeries ℚ)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact agree_mul (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem agree_rationalPower {n : ℕ} {f g : PowerSeries ℚ}
    (h : Agree n f g) (r : ℚ) : Agree n (rationalPower f r) (rationalPower g r) := by
  intro j hj
  simp only [rationalPower, coeff_mk]
  apply Finset.sum_congr rfl
  intro k hk
  rw [agree_pow (agree_sub h (agree_refl n 1)) k j hj]

theorem agree_X_mul {n : ℕ} {f g : PowerSeries ℚ}
    (h : Agree n f g) : Agree (n + 1) (X * f) (X * g) := by
  intro j hj
  cases j with
  | zero => simp
  | succ j =>
    rw [coeff_succ_X_mul, coeff_succ_X_mul]
    exact h j (by omega)

/-- The finite product used to determine coefficient n of a solution. -/
def rwOperator (E : ℚ) (c : ℕ → ℚ) (n : ℕ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  ∏ k ∈ Finset.Icc 1 n,
    rationalPower (1 - (X * rationalPower f E) ^ k) (-(k : ℚ) * c k)

theorem rwOperator_agree {n : ℕ} {f g : PowerSeries ℚ}
    (h : Agree n f g) (E : ℚ) (c : ℕ → ℚ) (N : ℕ) :
    Agree (n + 1) (rwOperator E c N f) (rwOperator E c N g) := by
  apply agree_prod
  intro k hk
  exact agree_rationalPower
    (agree_sub (agree_refl (n + 1) 1)
      (agree_pow (agree_X_mul (agree_rationalPower h E)) k)) _

/-- Coefficient n is constructed from the coefficients with index below n.
The zero extension supplies a power series at each finite recursion step. -/
def rwCoefficient (E : ℚ) (c : ℕ → ℚ) (n : ℕ) : ℚ :=
  coeff n (rwOperator E c n
    (PowerSeries.mk fun j => if _h : j < n then rwCoefficient E c j else 0))
termination_by n

/-- The formal solution for arbitrary rational E and coefficient sequence c. -/
def rwSeries (E : ℚ) (c : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (rwCoefficient E c)

theorem rwSeries_fixed_point (E : ℚ) (c : ℕ → ℚ) (n : ℕ) :
    coeff n (rwSeries E c) = coeff n (rwOperator E c n (rwSeries E c)) := by
  conv_lhs => rw [rwSeries, coeff_mk, rwCoefficient]
  apply rwOperator_agree (n := n) ?_ E c n n (by omega)
  intro j hj
  simp [rwSeries, hj]

theorem rwSeries_constant (E : ℚ) (c : ℕ → ℚ) :
    constantCoeff (rwSeries E c) = 1 := by
  have h := rwSeries_fixed_point E c 0
  simpa [rwOperator] using h

/-- The functional equation determines every coefficient by induction.
No geometric or common-series input is used. -/
theorem rw_fixed_point_unique (E : ℚ) (c : ℕ → ℚ) {f g : PowerSeries ℚ}
    (hf : ∀ n, coeff n f = coeff n (rwOperator E c n f))
    (hg : ∀ n, coeff n g = coeff n (rwOperator E c n g)) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [hf n, hg n]
    exact rwOperator_agree ih E c n n (by omega)

end RWUniqueness

theorem rw_functional_equation_unique {m a b : ℕ} {f g : PowerSeries ℚ}
    (hf : RWFunctionalEquation m a b f) (hg : RWFunctionalEquation m a b g) :
    f = g := by
  exact RWUniqueness.rw_fixed_point_unique
    (((m : ℚ) * m * a * b - m * a * a - m * b * b) / (m * m))
    (fun k => (bipartiteSum m (k * a) (k * b) : ℚ)) hf.2 hg.2

/-- A family of formal solutions of the RW functional equation.
Existence follows by coefficient recursion and contains no geometric assertion. -/
structure RWTheorem81 where
  series : ℕ → ℕ → ℕ → PowerSeries ℚ
  equation : ∀ m a b, 3 ≤ m → 0 < a → 0 < b → a.Coprime b →
    RWFunctionalEquation m a b (series m a b)

/-- Equality of the BLMMR and RW series on the admissible domain. -/
def CommonSeries (B : BLMMRTheorem410) (W : RWTheorem81) : Prop :=
  ∀ m a b, 3 ≤ m → 0 < a → 0 < b → a.Coprime b →
    B.wall m a b = W.series m a b

/-- The BLMMR wall and the formal solution satisfy the same equation.
Its coefficientwise uniqueness proves equality of the complete series. -/
theorem common_series_from_theorem_3_2 (B : BLMMRTheorem410) (W : RWTheorem81)
    (hB : BLMMRTheorem32 B) : CommonSeries B W := by
  intro m a b hm ha hb hc
  exact rw_functional_equation_unique (hB m a b hm ha hb hc)
    (W.equation m a b hm ha hb hc)

/-- RW Theorem 12.1. Its pair (ka,kb) means sink dimension ka and source
dimension kb, hence the reversed arguments of the project's datum. -/
def RWTheorem121 (G : Geometry) : Prop :=
  ∀ m a b k, 3 ≤ m → 0 < a → 0 < b → a.Coprime b → 0 < k →
    bipartiteSum m (k * a) (k * b) =
      (m : ℤ) * G.euler (KroneckerAllMPublishedDatum.datum m (k * b) (k * a))

/-- Coefficient extraction is an internal algebraic step, not an axiom. -/
theorem rw_first_coefficient (W : RWTheorem81) (m a b : ℕ)
    (hm : 3 ≤ m) (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b) :
    PowerSeries.coeff 1 (W.series m a b) = (bipartiteSum m a b : ℚ) := by
  have h := (W.equation m a b hm ha hb hc).2 1
  simpa [rationalPower_linear, rationalPower_constant] using h

theorem euler_exchange (G : Geometry) (m a b : ℕ) :
    G.euler (KroneckerAllMPublishedDatum.datum m b a) =
      G.euler (KroneckerAllMPublishedDatum.datum m a b) := by
  rw [← G.euler_comparison, ← G.euler_comparison]
  exact KroneckerExchangeEuler.euler_eq m b a _ _

/-- Assemble the finite consequence from the coefficient expansion,
functional equation, common-series equality, and Euler comparison. -/
theorem finite_enumeration_from_sources (G : Geometry)
    (B : BLMMRTheorem410) (W : RWTheorem81)
    (hSeries : CommonSeries B W) (hBalanced : RWTheorem121 G) :
    Nonempty (KroneckerFiniteCoefficientIntegration.FiniteEnumeration G) := by
  refine ⟨{ lambda := B.lambda, count := B.count, primitive_euler := ?_ }⟩
  intro m a b hm ha hb hc
  have hEnumeration :
      (∑ P : Nat.Partition a × Nat.Partition b, (B.lambda a b P : ℚ) *
        sigWeight (incoming m).coeff (incoming m).coeff P) =
      PowerSeries.coeff 1 (B.wall m a b) := by
    let total (u v : ℕ) : ℚ :=
      ∑ P : Nat.Partition u × Nat.Partition v, (B.lambda u v P : ℚ) *
        sigWeight (incoming m).coeff (incoming m).coeff P
    have h := (B.expansion m a b 1 hm ha hb hc (by decide)).symm
    change total (1 * a) (1 * b) = PowerSeries.coeff 1 (B.wall m a b) at h
    change total a b = PowerSeries.coeff 1 (B.wall m a b)
    simpa only [one_mul] using h
  rw [hEnumeration, hSeries m a b hm ha hb hc, rw_first_coefficient W m a b hm ha hb hc]
  have h := hBalanced m a b 1 hm ha hb hc (by decide)
  simp only [one_mul] at h
  rw [euler_exchange] at h
  exact_mod_cast h

/-- Accepted negative-determinant specialization of BLMMR Theorem 4.10(2),
with algebraic series packaging. The geometric content of 4.10(1) is included
in `blmmr_theorem_3_2`. -/
axiom blmmr_theorem_4_10 : Nonempty BLMMRTheorem410

/-- Existence of formal solutions, proved by coefficient recursion.
This is not an external input or a formalization of the geometric content
of RW Theorem 8.1. The declaration name is retained for compatibility. -/
theorem reineke_weist_theorem_8_1 : Nonempty RWTheorem81 := by
  refine ⟨{
    series := fun m a b =>
      RWUniqueness.rwSeries
        (((m : ℚ) * m * a * b - m * a * a - m * b * b) / (m * m))
        (fun k => (bipartiteSum m (k * a) (k * b) : ℚ))
    equation := ?_ }⟩
  intro m a b _ _ _ _
  exact ⟨RWUniqueness.rwSeries_constant _ _, RWUniqueness.rwSeries_fixed_point _ _⟩

/-- Witness supplied by the BLMMR theorem input. -/
def blmmr : BLMMRTheorem410 := Classical.choice blmmr_theorem_4_10

/-- Formal solution supplied by the coefficient-recursion theorem. -/
def reinekeWeist : RWTheorem81 := Classical.choice reineke_weist_theorem_8_1

/-- Accepted equal-parameter composite of BLMMR Theorem 4.10(1), pp. 13–14,
and Theorem 3.2, p. 8. The first identifies the counting series with the
geometric wall; the second gives its functional equation using RW Theorem 8.1.
The equality with the separately constructed formal solution is proved below.
See audit/n2-n4-n5-20261101/SOURCE-CORRESPONDENCE.md. -/
axiom blmmr_theorem_3_2 : BLMMRTheorem32 blmmr

/-- Common-series equality derived from BLMMR 3.2 and the formal solution. -/
theorem common_series : CommonSeries blmmr reinekeWeist :=
  common_series_from_theorem_3_2 blmmr reinekeWeist blmmr_theorem_3_2

/-- Accepted equal-length specialization of RW Theorem 12.1. -/
axiom reineke_weist_theorem_12_1 (G : Geometry) : RWTheorem121 G

end KroneckerFiniteEnumerationSourceSplit

namespace KroneckerFiniteCoefficientIntegration
open KroneckerFiniteEnumerationSourceSplit
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerFrameIdentity KroneckerColoring
open KroneckerWeights KroneckerSourceMaximalPath KroneckerSourcePartitions
open KroneckerSourcePartitionSums KroneckerSourceParameterGates
open KroneckerPublishedEnumerationApplication
open scoped BigOperators

/-- Finite consequence of three cited theorem inputs, assembled by formal
existence and uniqueness, coefficient extraction, and source/sink exchange. -/
theorem finite_enumeration (G : Geometry) : Nonempty (FiniteEnumeration G) :=
  finite_enumeration_from_sources G blmmr reinekeWeist common_series
    (reineke_weist_theorem_12_1 G)

theorem weighted_euler (G : Geometry) (S : FiniteEnumeration G) (p : Parameters) :
    (weightedCount (fun d : Grades p.m (ambientLength p) =>
      KroneckerTight.Tight (frameShape p) p.a p.b (representative d)):ℚ) =
      (p.m:ℚ)*(euler (family G) p.m p.a p.b:ℚ) := by
  rw [← KroneckerSourceGradingDictionary.weighted_tight_eq,
    ← incoming_partition_enumeration]
  have h := source_hypotheses p
  have hc : ∀ P : Nat.Partition p.a × Nat.Partition p.b,
      S.lambda p.a p.b P=coefficient (ambientLength p) p.a p.b (frameShape p) P := by
    intro P
    have he := S.count p.a p.b p.d₁ p.d₂ (frameShape p) h.1 h.2.1
      h.2.2.2.2.1 h.2.2.2.2.2.1 (ambient_path_maximal p)
      h.2.2.2.2.2.2.2.1 P
    simpa only [ambientLength,frameLength,p.length_eq] using he
  rw [partitionSum]
  simp_rw [← hc]
  rw [S.primitive_euler p.m p.a p.b p.hm h.1 h.2.1 p.coprime,
    euler_comparison]

def auxiliary (E : ℤ) : PowerSeries ℚ := 1 + PowerSeries.C (E:ℚ) * PowerSeries.X

theorem auxiliary_constant (E : ℤ) : PowerSeries.constantCoeff (auxiliary E)=1 := by
  simp [auxiliary]

theorem auxiliary_linear (E : ℤ) : PowerSeries.coeff 1 (auxiliary E)=(E:ℚ) := by
  simp [auxiliary]

def application (G : Geometry) (S : FiniteEnumeration G) :
    KroneckerScopedActualFrameApplication.Application G := fun p => {
  positive := (auxiliary (euler (family G) p.m p.a p.b))^p.m
  cluster := auxiliary (euler (family G) p.m p.a p.b)
  constant := auxiliary_constant _
  position := fun _ ht => KroneckerDirectCoprimePosition.source_position p ht
  enumeration := by
    rw [KroneckerWall.first_coefficient_power _ p.m (auxiliary_constant _),
      auxiliary_linear]
    exact weighted_euler G S p
  change_lattice := by
    rw [KroneckerWall.lattice_exponent p.coprime (by have := p.hm; omega)]
  euler := auxiliary_linear _ }

end KroneckerFiniteCoefficientIntegration
#print axioms KroneckerFiniteCoefficientIntegration.weighted_euler
#print axioms KroneckerFiniteCoefficientIntegration.application

#print axioms KroneckerFiniteEnumerationSourceSplit.finite_enumeration_from_sources
#print axioms KroneckerFiniteCoefficientIntegration.finite_enumeration

#print axioms KroneckerFiniteEnumerationSourceSplit.RWUniqueness.rw_fixed_point_unique
#print axioms KroneckerFiniteEnumerationSourceSplit.rw_functional_equation_unique
#print axioms KroneckerFiniteEnumerationSourceSplit.common_series_from_theorem_3_2
#print axioms KroneckerFiniteEnumerationSourceSplit.common_series
#print axioms KroneckerFiniteEnumerationSourceSplit.RWUniqueness.rwSeries_fixed_point
#print axioms KroneckerFiniteEnumerationSourceSplit.RWUniqueness.rwSeries_constant
#print axioms KroneckerFiniteEnumerationSourceSplit.reineke_weist_theorem_8_1
