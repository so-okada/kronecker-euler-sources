import KroneckerPublishedEnumerationApplication
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
N2: exact checks of BLMMR Appendix A, Tables A1 and A2 (published p. 35).
The coefficient is the existing signature-fiber cardinality. The finite
enumerator below is proved equivalent to that definition, including both
endpoint exclusions and the shadow support condition. No geometric or
BLMMR counting axiom is imported. Each table is checked on two admissible
negative-determinant frames. These finite cases do not prove general frame
independence. Source: doi:10.1112/jlms.70642, Theorem 4.10(2), Tables A1–A2.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option maxSynthPendingDepth 1024
set_option synthInstance.maxSize 4096

namespace KroneckerBLMMRTableChecks
open KroneckerStack KroneckerCompatibility KroneckerDyck
open KroneckerSourceIntervalCounts KroneckerSourceCompatibility
open KroneckerSourceHorizontalShadow KroneckerSourceNaturalGradings
open KroneckerSourcePartitions KroneckerSourcePartitionSums
open KroneckerSourceMaximalPath
open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype

private theorem horizontal_iff_flag (E : ℕ → Edge) (i : ℕ) :
    Horizontal E i ↔ hFlag (E i) = 1 := by
  cases hi : E i <;> simp [Horizontal, hFlag, hi]

private theorem vertical_iff_flag (E : ℕ → Edge) (i : ℕ) :
    Vertical E i ↔ vFlag (E i) = 1 := by
  cases hi : E i <;> simp [Vertical, vFlag, hi]

private theorem positiveH_iff_grade (E : ℕ → Edge) (i : ℕ) :
    PositiveH E i ↔ 0 < hGrade (E i) := by
  cases hi : E i <;> simp [PositiveH, hGrade, hi]

private theorem positiveV_iff_grade (E : ℕ → Edge) (i : ℕ) :
    PositiveV E i ↔ 0 < vGrade (E i) := by
  cases hi : E i <;> simp [PositiveV, vGrade, hi]

/-- The same horizontal witness, with its bounded index represented by `Fin`. -/
def FiniteH (E : ℕ → Edge) (u v : ℕ) : Prop :=
  ∃ e : Fin v, u ≤ e.val ∧ vFlag (E e.val) = 1 ∧ HEquality E u e.val

instance (E : ℕ → Edge) (u v : ℕ) : Decidable (FiniteH E u v) := by
  unfold FiniteH HEquality
  infer_instance

theorem finiteH_iff (E : ℕ → Edge) (u v : ℕ) :
    FiniteH E u v ↔ SourceH E u v := by
  constructor
  · rintro ⟨e, hue, heV, heq⟩
    exact ⟨e.val, hue, e.isLt, (vertical_iff_flag E e.val).mpr heV, heq⟩
  · rintro ⟨e, hue, hev, heV, heq⟩
    exact ⟨⟨e, hev⟩, hue, (vertical_iff_flag E e).mp heV, heq⟩

/-- The same vertical witness, including the permitted endpoint `e = v`. -/
def FiniteV (E : ℕ → Edge) (u v : ℕ) : Prop :=
  ∃ e : Fin (v + 1), u < e.val ∧ hFlag (E e.val) = 1 ∧ VEquality E e.val v

instance (E : ℕ → Edge) (u v : ℕ) : Decidable (FiniteV E u v) := by
  unfold FiniteV VEquality
  infer_instance

theorem finiteV_iff (E : ℕ → Edge) (u v : ℕ) :
    FiniteV E u v ↔ SourceV E u v := by
  constructor
  · rintro ⟨e, hue, heH, heq⟩
    exact ⟨e.val, hue, Nat.le_of_lt_succ e.isLt,
      (horizontal_iff_flag E e.val).mpr heH, heq⟩
  · rintro ⟨e, hue, hev, heH, heq⟩
    exact ⟨⟨e, Nat.lt_succ_of_le hev⟩, hue,
      (horizontal_iff_flag E e).mp heH, heq⟩

def FiniteCyclic (E : ℕ → Edge) (N : ℕ) : Prop :=
  ∀ u v : Fin N, 0 < hGrade (E u.val) → 0 < vGrade (E v.val) →
    FiniteH E u.val (lift N u.val v.val) ∨ FiniteV E u.val (lift N u.val v.val)

instance (E : ℕ → Edge) (N : ℕ) : Decidable (FiniteCyclic E N) := by
  unfold FiniteCyclic
  infer_instance

theorem finiteCyclic_iff (E : ℕ → Edge) (N : ℕ) :
    FiniteCyclic E N ↔ Cyclic E N := by
  constructor
  · intro h u v hu hv huP hvP
    exact (or_congr (finiteH_iff E u (lift N u v))
      (finiteV_iff E u (lift N u v))).mp
        (h ⟨u, hu⟩ ⟨v, hv⟩ ((positiveH_iff_grade E u).mp huP)
          ((positiveV_iff_grade E v).mp hvP))
  · intro h u v huP hvP
    exact (or_congr (finiteH_iff E u.val (lift N u.val v.val))
      (finiteV_iff E u.val (lift N u.val v.val))).mpr
        (h u.val v.val u.isLt v.isLt ((positiveH_iff_grade E u.val).mpr huP)
          ((positiveV_iff_grade E v.val).mpr hvP))

/-- Absence of an earlier equality is the existing `Shadow` predicate. -/
def FiniteSupport (E : ℕ → Edge) (N : ℕ) : Prop :=
  ∀ v : Fin N, 0 < vGrade (E v.val) →
    ∃ u : Fin N, 0 < hGrade (E u.val) ∧ ¬FiniteH E u.val (lift N u.val v.val)

instance (E : ℕ → Edge) (N : ℕ) : Decidable (FiniteSupport E N) := by
  unfold FiniteSupport
  infer_instance

theorem finiteSupport_iff (E : ℕ → Edge) (N : ℕ) :
    FiniteSupport E N ↔ Support E N := by
  constructor
  · intro h v hv hvP
    obtain ⟨u, huP, hs⟩ := h ⟨v, hv⟩ ((positiveV_iff_grade E v).mp hvP)
    refine ⟨u.val, u.isLt, (positiveH_iff_grade E u.val).mpr huP, ?_⟩
    apply (shadow_iff_not_source E u.val (lift N u.val v)).mpr
    intro hh
    exact hs ((finiteH_iff E u.val (lift N u.val v)).mpr hh)
  · intro h v hvP
    obtain ⟨u, hu, huP, hs⟩ := h v.val v.isLt ((positiveV_iff_grade E v.val).mpr hvP)
    refine ⟨⟨u, hu⟩, (positiveH_iff_grade E u).mp huP, ?_⟩
    intro hh
    exact ((shadow_iff_not_source E u (lift N u v.val)).mp hs)
      ((finiteH_iff E u (lift N u v.val)).mp hh)

/-- Cheap total checks precede compatibility in the finite evaluation. -/
def FiniteTight {N : ℕ} (shape : ℕ → Bool) (a b : ℕ) (g : Fin N → ℕ) : Prop :=
  hWeight (naturalTrace shape g) 0 N = (b : ℤ) ∧
    vWeight (naturalTrace shape g) 0 N = (a : ℤ) ∧
    FiniteSupport (naturalTrace shape g) N ∧ FiniteCyclic (naturalTrace shape g) N

instance {N : ℕ} (shape : ℕ → Bool) (a b : ℕ) (g : Fin N → ℕ) :
    Decidable (FiniteTight shape a b g) := by
  unfold FiniteTight
  infer_instance

theorem finiteTight_iff {N : ℕ} (shape : ℕ → Bool) (a b : ℕ) (g : Fin N → ℕ) :
    FiniteTight shape a b g ↔ NaturalTight shape a b g := by
  constructor
  · rintro ⟨hh, hv, hs, hc⟩
    exact ⟨(finiteCyclic_iff _ _).mp hc, hh, hv, (finiteSupport_iff _ _).mp hs⟩
  · rintro ⟨hc, hh, hv, hs⟩
    exact ⟨hh, hv, (finiteSupport_iff _ _).mpr hs, (finiteCyclic_iff _ _).mpr hc⟩

def verticalParts {N : ℕ} (shape : ℕ → Bool) (g : Fin N → ℕ) : Multiset ℕ :=
  ((Finset.univ : Finset (Fin N)).val.map (vTerm shape g)).filter (fun k => k ≠ 0)

def horizontalParts {N : ℕ} (shape : ℕ → Bool) (g : Fin N → ℕ) : Multiset ℕ :=
  ((Finset.univ : Finset (Fin N)).val.map (hTerm shape g)).filter (fun k => k ≠ 0)

theorem signature_iff_parts {N a b : ℕ} {shape : ℕ → Bool} {g : Fin N → ℕ}
    (ht : NaturalTight shape a b g) (P : Nat.Partition a × Nat.Partition b) :
    signature ht = P ↔ verticalParts shape g = P.1.parts ∧ horizontalParts shape g = P.2.parts := by
  constructor
  · intro h
    exact ⟨congrArg (fun Q : Nat.Partition a × Nat.Partition b => Q.1.parts) h,
      congrArg (fun Q : Nat.Partition a × Nat.Partition b => Q.2.parts) h⟩
  · rintro ⟨hv, hh⟩
    apply Prod.ext
    · exact Nat.Partition.ext hv
    · exact Nat.Partition.ext hh

/-- Enumerate only tuples with total grade `a+b`; completeness follows from
`capacity_of_tight`. The partition filters also remove candidates early. -/
def candidates (N a b : ℕ) (shape : ℕ → Bool) (P : Nat.Partition a × Nat.Partition b) :
    Finset (Fin N → ℕ) :=
  (Finset.Nat.antidiagonalTuple N (a + b)).filter fun g =>
    verticalParts shape g = P.1.parts ∧ horizontalParts shape g = P.2.parts ∧
      FiniteTight shape a b g

theorem mem_candidates (N a b : ℕ) (shape : ℕ → Bool)
    (P : Nat.Partition a × Nat.Partition b) (g : Fin N → ℕ) :
    g ∈ candidates N a b shape P ↔
      NaturalTight shape a b g ∧ verticalParts shape g = P.1.parts ∧
        horizontalParts shape g = P.2.parts := by
  rw [candidates, Finset.mem_filter]
  constructor
  · rintro ⟨_, hv, hh, ht⟩
    exact ⟨(finiteTight_iff shape a b g).mp ht, hv, hh⟩
  · rintro ⟨ht, hv, hh⟩
    refine ⟨Finset.Nat.mem_antidiagonalTuple.mpr ?_, hv, hh,
      (finiteTight_iff shape a b g).mpr ht⟩
    exact capacity_of_tight ht

/-- An explicit equivalence with the exact signature fiber used in `coefficient`. -/
def coefficientEquiv (N a b : ℕ) (shape : ℕ → Bool) (P : Nat.Partition a × Nat.Partition b) :
    {g : Grading N a b shape // sig g = P} ≃ {g // g ∈ candidates N a b shape P} where
  toFun g := ⟨g.val.val, (mem_candidates N a b shape P g.val.val).mpr
    ⟨g.val.property, (signature_iff_parts g.val.property P).mp g.property⟩⟩
  invFun g := by
    have h := (mem_candidates N a b shape P g.val).mp g.property
    exact ⟨⟨g.val, h.1⟩, (signature_iff_parts h.1 P).mpr h.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl

theorem coefficient_eq_card (N a b : ℕ) (shape : ℕ → Bool)
    (P : Nat.Partition a × Nat.Partition b) :
    coefficient N a b shape P = (candidates N a b shape P).card := by
  unfold coefficient
  rw [Nat.card_congr (coefficientEquiv N a b shape P)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

def partitionsA1 : Fin 2 → Nat.Partition 2 :=
  ![Nat.Partition.ofSums 2 ({2} : Multiset ℕ) (by decide),
    Nat.Partition.ofSums 2 ({1, 1} : Multiset ℕ) (by decide)]

def partitionsA2 : Fin 3 → Nat.Partition 3 :=
  ![Nat.Partition.ofSums 3 ({3} : Multiset ℕ) (by decide),
    Nat.Partition.ofSums 3 ({2, 1} : Multiset ℕ) (by decide),
    Nat.Partition.ofSums 3 ({1, 1, 1} : Multiset ℕ) (by decide)]

def tableA1 : Fin 2 → Fin 2 → ℕ := ![![2, 1], ![1, 0]]
def tableA2 : Fin 3 → Fin 3 → ℕ := ![![3, 6, 1], ![6, 5, 0], ![1, 0, 0]]

/-- Both tables use `a=b=k` and frames `(d+1,d)` with `k ≤ d`. -/
theorem diagonal_frame_admissible {k d : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    k ≤ d + 1 ∧ k ≤ d ∧ Maximal (d + 1) d (pathShape (d + 1) d) ∧
      (k : ℤ) * d - (k : ℤ) * (d + 1 : ℕ) = -(Nat.gcd k k : ℕ) := by
  refine ⟨by omega, hkd, dyck_maximal (by omega) (by omega), ?_⟩
  simp only [Nat.gcd_self, Nat.cast_add, Nat.cast_one]
  ring

-- Separate declarations bound the kernel reduction cache for each table entry.
private theorem tableA1_frame32_entry00 :
    (candidates 5 2 2 (pathShape 3 2) (partitionsA1 0, partitionsA1 0)).card = 2 := by
  decide +kernel

private theorem tableA1_frame32_entry01 :
    (candidates 5 2 2 (pathShape 3 2) (partitionsA1 0, partitionsA1 1)).card = 1 := by
  decide +kernel

private theorem tableA1_frame32_entry10 :
    (candidates 5 2 2 (pathShape 3 2) (partitionsA1 1, partitionsA1 0)).card = 1 := by
  decide +kernel

private theorem tableA1_frame32_entry11 :
    (candidates 5 2 2 (pathShape 3 2) (partitionsA1 1, partitionsA1 1)).card = 0 := by
  decide +kernel

private theorem tableA1_frame32_finite : ∀ i j : Fin 2,
    (candidates 5 2 2 (pathShape 3 2) (partitionsA1 i, partitionsA1 j)).card = tableA1 i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact tableA1_frame32_entry00
  · exact tableA1_frame32_entry01
  · exact tableA1_frame32_entry10
  · exact tableA1_frame32_entry11

private theorem tableA1_frame43_entry00 :
    (candidates 7 2 2 (pathShape 4 3) (partitionsA1 0, partitionsA1 0)).card = 2 := by
  decide +kernel

private theorem tableA1_frame43_entry01 :
    (candidates 7 2 2 (pathShape 4 3) (partitionsA1 0, partitionsA1 1)).card = 1 := by
  decide +kernel

private theorem tableA1_frame43_entry10 :
    (candidates 7 2 2 (pathShape 4 3) (partitionsA1 1, partitionsA1 0)).card = 1 := by
  decide +kernel

private theorem tableA1_frame43_entry11 :
    (candidates 7 2 2 (pathShape 4 3) (partitionsA1 1, partitionsA1 1)).card = 0 := by
  decide +kernel

private theorem tableA1_frame43_finite : ∀ i j : Fin 2,
    (candidates 7 2 2 (pathShape 4 3) (partitionsA1 i, partitionsA1 j)).card = tableA1 i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact tableA1_frame43_entry00
  · exact tableA1_frame43_entry01
  · exact tableA1_frame43_entry10
  · exact tableA1_frame43_entry11

private theorem tableA2_frame43_entry00 :
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 0, partitionsA2 0)).card = 3 := by
  decide +kernel

private theorem tableA2_frame43_entry01 :
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 0, partitionsA2 1)).card = 6 := by
  decide +kernel

private theorem tableA2_frame43_entry02 :
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 0, partitionsA2 2)).card = 1 := by
  decide +kernel

private theorem tableA2_frame43_entry10 :
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 1, partitionsA2 0)).card = 6 := by
  decide +kernel

private theorem tableA2_frame43_entry11 :
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 1, partitionsA2 1)).card = 5 := by
  decide +kernel

private theorem tableA2_frame43_entry12 :
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 1, partitionsA2 2)).card = 0 := by
  decide +kernel

private theorem tableA2_frame43_entry20 :
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 2, partitionsA2 0)).card = 1 := by
  decide +kernel

private theorem tableA2_frame43_entry21 :
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 2, partitionsA2 1)).card = 0 := by
  decide +kernel

private theorem tableA2_frame43_entry22 :
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 2, partitionsA2 2)).card = 0 := by
  decide +kernel

private theorem tableA2_frame43_finite : ∀ i j : Fin 3,
    (candidates 7 3 3 (pathShape 4 3) (partitionsA2 i, partitionsA2 j)).card = tableA2 i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact tableA2_frame43_entry00
  · exact tableA2_frame43_entry01
  · exact tableA2_frame43_entry02
  · exact tableA2_frame43_entry10
  · exact tableA2_frame43_entry11
  · exact tableA2_frame43_entry12
  · exact tableA2_frame43_entry20
  · exact tableA2_frame43_entry21
  · exact tableA2_frame43_entry22

private theorem tableA2_frame54_entry00 :
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 0, partitionsA2 0)).card = 3 := by
  decide +kernel

private theorem tableA2_frame54_entry01 :
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 0, partitionsA2 1)).card = 6 := by
  decide +kernel

private theorem tableA2_frame54_entry02 :
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 0, partitionsA2 2)).card = 1 := by
  decide +kernel

private theorem tableA2_frame54_entry10 :
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 1, partitionsA2 0)).card = 6 := by
  decide +kernel

private theorem tableA2_frame54_entry11 :
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 1, partitionsA2 1)).card = 5 := by
  decide +kernel

private theorem tableA2_frame54_entry12 :
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 1, partitionsA2 2)).card = 0 := by
  decide +kernel

private theorem tableA2_frame54_entry20 :
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 2, partitionsA2 0)).card = 1 := by
  decide +kernel

private theorem tableA2_frame54_entry21 :
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 2, partitionsA2 1)).card = 0 := by
  decide +kernel

private theorem tableA2_frame54_entry22 :
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 2, partitionsA2 2)).card = 0 := by
  decide +kernel

private theorem tableA2_frame54_finite : ∀ i j : Fin 3,
    (candidates 9 3 3 (pathShape 5 4) (partitionsA2 i, partitionsA2 j)).card = tableA2 i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact tableA2_frame54_entry00
  · exact tableA2_frame54_entry01
  · exact tableA2_frame54_entry02
  · exact tableA2_frame54_entry10
  · exact tableA2_frame54_entry11
  · exact tableA2_frame54_entry12
  · exact tableA2_frame54_entry20
  · exact tableA2_frame54_entry21
  · exact tableA2_frame54_entry22


theorem tableA1_frame32 (i j : Fin 2) :
    coefficient 5 2 2 (pathShape 3 2) (partitionsA1 i, partitionsA1 j) = tableA1 i j := by
  rw [coefficient_eq_card]
  exact tableA1_frame32_finite i j

theorem tableA1_frame43 (i j : Fin 2) :
    coefficient 7 2 2 (pathShape 4 3) (partitionsA1 i, partitionsA1 j) = tableA1 i j := by
  rw [coefficient_eq_card]
  exact tableA1_frame43_finite i j

theorem tableA2_frame43 (i j : Fin 3) :
    coefficient 7 3 3 (pathShape 4 3) (partitionsA2 i, partitionsA2 j) = tableA2 i j := by
  rw [coefficient_eq_card]
  exact tableA2_frame43_finite i j

theorem tableA2_frame54 (i j : Fin 3) :
    coefficient 9 3 3 (pathShape 5 4) (partitionsA2 i, partitionsA2 j) = tableA2 i j := by
  rw [coefficient_eq_card]
  exact tableA2_frame54_finite i j

theorem tableA1_frame_independent (i j : Fin 2) :
    coefficient 5 2 2 (pathShape 3 2) (partitionsA1 i, partitionsA1 j) =
      coefficient 7 2 2 (pathShape 4 3) (partitionsA1 i, partitionsA1 j) :=
  (tableA1_frame32 i j).trans (tableA1_frame43 i j).symm

theorem tableA2_frame_independent (i j : Fin 3) :
    coefficient 7 3 3 (pathShape 4 3) (partitionsA2 i, partitionsA2 j) =
      coefficient 9 3 3 (pathShape 5 4) (partitionsA2 i, partitionsA2 j) :=
  (tableA2_frame43 i j).trans (tableA2_frame54 i j).symm

end KroneckerBLMMRTableChecks

#print axioms KroneckerBLMMRTableChecks.coefficient_eq_card
#print axioms KroneckerBLMMRTableChecks.diagonal_frame_admissible
#print axioms KroneckerBLMMRTableChecks.tableA1_frame32
#print axioms KroneckerBLMMRTableChecks.tableA1_frame43
#print axioms KroneckerBLMMRTableChecks.tableA2_frame43
#print axioms KroneckerBLMMRTableChecks.tableA2_frame54
#print axioms KroneckerBLMMRTableChecks.tableA1_frame_independent
#print axioms KroneckerBLMMRTableChecks.tableA2_frame_independent
