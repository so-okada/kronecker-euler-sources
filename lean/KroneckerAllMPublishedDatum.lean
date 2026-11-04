import KroneckerStableMatrixKernelCover
import KroneckerMatrixKingDictionary
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import KroneckerPublishedModuli
import KroneckerSupportDimensionPushforward
import KroneckerPositiveFiberTotals
import KroneckerCoprimeKingNumerator

/- Original module: KroneckerGeneralKingSemistability -/
section
/-! General finite-dimensional numerical King semistability, with exact
opposite-character and gauge-orbit transport.  No regular semi-invariant or
GIT theorem is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace KroneckerFiniteQuiverHom
open Module
open scoped BigOperators

variable {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
  {R S : Representation s t d}

/-- Internal sign convention: nonzero proper subrepresentations have
nonpositive weight. -/
def Semistable (θ : V → ℤ) (R : Representation s t d) : Prop :=
  (∑ v, θ v * (d v : ℤ)) = 0 ∧
    ∀ U : Subrep R, 0 < size U → size U < ∑ v, d v → weight θ U ≤ 0

theorem stable_implies_semistable {θ : V → ℤ} {R : Representation s t d}
    (hR : Stable θ R) : Semistable θ R :=
  ⟨hR.1, fun U hn hp ↦ le_of_lt (hR.2 U hn hp)⟩

/-- An exact wall-avoidance condition on the dimensions of all proper
subrepresentations of one representation. -/
def NoZeroWeightWall (θ : V → ℤ) (R : Representation s t d) : Prop :=
  ∀ U : Subrep R, 0 < size U → size U < ∑ v, d v → weight θ U ≠ 0

/-- A representation-independent chamber condition on every possible proper
subdimension vector. -/
def GenericForDimension (θ : V → ℤ) (d : V → ℕ) : Prop :=
  ∀ e : V → ℕ, (∀ v, e v ≤ d v) →
    0 < ∑ v, e v → ∑ v, e v < ∑ v, d v →
    (∑ v, θ v * (e v : ℤ)) ≠ 0

theorem genericForDimension_opposite_iff (θ : V → ℤ) :
    GenericForDimension (fun v ↦ -θ v) d ↔ GenericForDimension θ d := by
  simp only [GenericForDimension, neg_mul, Finset.sum_neg_distrib, neg_ne_zero]

theorem genericForDimension_noZeroWeightWall {θ : V → ℤ}
    (hθ : GenericForDimension θ d) (R : Representation s t d) :
    NoZeroWeightWall θ R := by
  intro U hn hp
  exact hθ (fun v ↦ finrank ℂ (U.space v))
    (fun v => by simpa [Space] using (U.space v).finrank_le) hn hp

theorem semistable_and_noWall_implies_stable {θ : V → ℤ}
    {R : Representation s t d} (hR : Semistable θ R)
    (hwall : NoZeroWeightWall θ R) : Stable θ R := by
  refine ⟨hR.1, ?_⟩
  intro U hn hp
  exact lt_of_le_of_ne (hR.2 U hn hp) (hwall U hn hp)

theorem semistable_iff_stable_of_generic {θ : V → ℤ}
    (hθ : GenericForDimension θ d) (R : Representation s t d) :
    Semistable θ R ↔ Stable θ R :=
  ⟨fun h ↦ semistable_and_noWall_implies_stable h
      (genericForDimension_noZeroWeightWall hθ R),
    stable_implies_semistable⟩

theorem Iso.mapSubrep_noZeroWeightWall (e : Iso R S) (θ : V → ℤ)
    (hR : NoZeroWeightWall θ R) : NoZeroWeightWall θ S := by
  intro U hn hp
  have h := hR (e.pullSubrep U)
    (by simpa only [Iso.pullSubrep_size] using hn)
    (by simpa only [Iso.pullSubrep_size] using hp)
  simpa only [Iso.pullSubrep_weight] using h

/-- General numerical semistability is invariant under all actual
same-label representation isomorphisms. -/
theorem Iso.semistable_iff (e : Iso R S) (θ : V → ℤ) :
    Semistable θ R ↔ Semistable θ S := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro U hn hp
    have hw := h.2 (e.pullSubrep U)
      (by simpa only [Iso.pullSubrep_size] using hn)
      (by simpa only [Iso.pullSubrep_size] using hp)
    simpa only [Iso.pullSubrep_weight] using hw
  · intro h
    refine ⟨h.1, ?_⟩
    intro U hn hp
    have hw := h.2 (e.symm.pullSubrep U)
      (by simpa only [Iso.pullSubrep_size] using hn)
      (by simpa only [Iso.pullSubrep_size] using hp)
    simpa only [Iso.pullSubrep_weight] using hw

end KroneckerFiniteQuiverHom

namespace KroneckerMatrixKingDictionary
open KroneckerRingQuiverFamilies
open scoped BigOperators

variable {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}

/-- Published positive-weight convention for numerical semistability. -/
def KingSemistable (θ : V → ℤ) (M : Family s t d ℂ) : Prop :=
  (∑ v, θ v * (d v : ℤ)) = 0 ∧
    ∀ U : MatrixSubrep M, 0 < size U → size U < ∑ v, d v → 0 ≤ weight θ U

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The sign translation uses exactly all matrix subrepresentations. -/
theorem kingSemistable_iff_internal (θ : V → ℤ) (M : Family s t d ℂ) :
    KingSemistable θ M ↔
      KroneckerFiniteQuiverHom.Semistable (fun v ↦ -θ v)
        (toRepresentation s t d M) := by
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨by simpa [neg_mul, Finset.sum_neg_distrib] using ht, ?_⟩
    intro U hn hp
    have hh := h (fromSubrep U) hn hp
    simpa [KroneckerFiniteQuiverHom.weight, weight, subdimension, fromSubrep,
      neg_mul, Finset.sum_neg_distrib] using neg_nonpos.mpr hh
  · rintro ⟨ht, h⟩
    refine ⟨by simpa [neg_mul, Finset.sum_neg_distrib] using ht, ?_⟩
    intro U hn hp
    have hh := h (toSubrep U) hn hp
    rw [opposite_weight] at hh
    exact neg_nonpos.mp hh

/-- Numerical semistability is constant on actual complex product-GL orbits. -/
theorem kingSemistable_gauge_iff (θ : V → ℤ) (g : Gauge d ℂ)
    (M : Family s t d ℂ) :
    KingSemistable θ (gauge s t d g M) ↔ KingSemistable θ M := by
  rw [kingSemistable_iff_internal, kingSemistable_iff_internal]
  exact (KroneckerRingQuiverFamilies.gaugeIso s t d g M).semistable_iff _ |>.symm

/-- Away from every proper subdimension wall, published-convention numerical
semistability and stability coincide in arbitrary finite dimension. -/
theorem kingSemistable_iff_stable_of_generic (θ : V → ℤ)
    (hθ : KroneckerFiniteQuiverHom.GenericForDimension θ d)
    (M : Family s t d ℂ) : KingSemistable θ M ↔ KingStable θ M := by
  rw [kingSemistable_iff_internal, kingStable_iff_internal]
  exact KroneckerFiniteQuiverHom.semistable_iff_stable_of_generic
    ((KroneckerFiniteQuiverHom.genericForDimension_opposite_iff
      (d := d) θ).2 hθ) (toRepresentation s t d M)

end KroneckerMatrixKingDictionary
end
end

/- Original module: KroneckerKingCharacter -/
section
set_option autoImplicit false
namespace KroneckerKingCharacter
open KroneckerRingQuiverFamilies
open scoped BigOperators
variable {V : Type} [Fintype V] (d : V → ℕ) (θ : V → ℤ)
variable (R : Type) [CommRing R]

/-- Determinants are units even over nonreduced base rings. -/
def determinantUnit (g : Gauge d R) (v : V) : Rˣ :=
  Units.map Matrix.detMonoidHom (g v)

/-- King's integral determinant character on the actual product general linear group. -/
noncomputable def character : Gauge d R →* Rˣ where
  toFun g := ∏ v, determinantUnit d R g v ^ θ v
  map_one' := by simp [determinantUnit]
  map_mul' g h := by
    simp only [determinantUnit, Pi.mul_apply, map_mul, mul_zpow]
    exact Finset.prod_mul_distrib

variable {R} {S : Type} [CommRing S]

theorem determinantUnit_natural (f : R →+* S) (g : Gauge d R) (v : V) :
    determinantUnit d S (changeGauge d f g) v =
      Units.map f.toMonoidHom (determinantUnit d R g v) := by
  apply Units.ext
  change Matrix.det ((↑(g v) : Matrix (Fin (d v)) (Fin (d v)) R).map f) =
    f (Matrix.det (↑(g v) : Matrix (Fin (d v)) (Fin (d v)) R))
  exact (RingHom.map_det f _).symm

/-- The character is natural over every commutative base ring, not just field points. -/
theorem character_natural (f : R →+* S) (g : Gauge d R) :
    character d θ S (changeGauge d f g) =
      Units.map f.toMonoidHom (character d θ R g) := by
  change (∏ v, determinantUnit d S (changeGauge d f g) v ^ θ v) = _
  simp only [character, MonoidHom.coe_mk, OneHom.coe_mk, map_prod, map_zpow,
    determinantUnit_natural]

/-- The actual common scalar subgroup of all vertex general linear groups. -/
def scalarDiagonal (c : Rˣ) : Gauge d R :=
  fun v => Units.map (Matrix.scalar (Fin (d v))).toMonoidHom c

theorem determinant_scalarDiagonal (c : Rˣ) (v : V) :
    determinantUnit d R (scalarDiagonal d c) v = c ^ d v := by
  apply Units.ext
  simp [determinantUnit, scalarDiagonal]

/-- Central scalar restriction has exponent equal to the dimension-weight pairing. -/
theorem character_scalarDiagonal (c : Rˣ) :
    character d θ R (scalarDiagonal d c) = c ^ (∑ v, (d v : ℤ) * θ v) := by
  change (∏ v, determinantUnit d R (scalarDiagonal d c) v ^ θ v) = _
  simp only [determinant_scalarDiagonal, ← zpow_natCast, ← zpow_mul]
  have hs (w : Finset V) : (∏ v ∈ w, c ^ ((d v : ℤ) * θ v)) =
      c ^ (∑ v ∈ w, (d v : ℤ) * θ v) := by
    classical
    induction w using Finset.induction_on with
    | empty => simp
    | @insert a w ha ih => simp [ha, ih, zpow_add]
  exact hs Finset.univ

/-- Zero total weight is exactly the sufficient central-triviality hypothesis
used before passing from GL to its common-scalar quotient. -/
theorem character_scalar_trivial (hθ : ∑ v, (d v : ℤ) * θ v = 0) (c : Rˣ) :
    character d θ R (scalarDiagonal d c) = 1 := by
  rw [character_scalarDiagonal, hθ, zpow_zero]

end KroneckerKingCharacter
end

/- Original module: KroneckerPublishedIndivisibility -/
section
/-! Apply the existing all-subrepresentation sign dictionary and genericity
theorem to the published-moduli datum. These checks are needed before invoking
King on the stable locus or treating a primitive quotient as projective. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPublishedIndivisibility
open KroneckerPublishedModuli KroneckerRingQuiverFamilies
open KroneckerFiniteQuiverHom KroneckerMatrixKingDictionary
open scoped BigOperators

def kingWeight (D : Datum) (v : D.V) : ℤ := -D.weight v

theorem king_balance (D : Datum) (h : Balanced D) :
    (∑ v, kingWeight D v * (D.dimension v : ℤ)) = 0 := by
  simpa [kingWeight, neg_mul, Finset.sum_neg_distrib] using congrArg Neg.neg h

theorem king_scalar_trivial (D : Datum) (h : Balanced D) (c : ℂˣ) :
    KroneckerKingCharacter.character D.dimension (kingWeight D) ℂ
      (KroneckerKingCharacter.scalarDiagonal D.dimension c) = 1 := by
  apply KroneckerKingCharacter.character_scalar_trivial
  simpa [mul_comm] using king_balance D h

theorem indivisible_generic (D : Datum) (h : Indivisible D) :
    GenericForDimension D.weight D.dimension := by
  intro e hle hn hp hw
  rcases h e hle hw with hz | hf
  · have hs : (∑ v, e v) = 0 := by simp [hz]
    omega
  · have hs : (∑ v, e v) = ∑ v, D.dimension v := by rw [hf]
    omega

theorem king_generic (D : Datum) (h : Indivisible D) :
    GenericForDimension (kingWeight D) D.dimension :=
  (genericForDimension_opposite_iff D.weight).mpr (indivisible_generic D h)

theorem stable_dictionary (D : Datum)
    (M : Family D.source D.target D.dimension ℂ) :
    KingStable (kingWeight D) M ↔
      Stable D.weight (toRepresentation D.source D.target D.dimension M) := by
  simpa only [kingWeight, neg_neg] using kingStable_iff_internal (kingWeight D) M

theorem semistable_dictionary (D : Datum)
    (M : Family D.source D.target D.dimension ℂ) :
    KingSemistable (kingWeight D) M ↔
      Semistable D.weight (toRepresentation D.source D.target D.dimension M) := by
  simpa only [kingWeight, neg_neg] using kingSemistable_iff_internal (kingWeight D) M

theorem semistable_eq_stable (D : Datum) (h : Indivisible D)
    (R : Representation D.source D.target D.dimension) :
    Semistable D.weight R ↔ Stable D.weight R :=
  semistable_iff_stable_of_generic (indivisible_generic D h) R

theorem king_semistable_eq_stable (D : Datum) (h : Indivisible D)
    (M : Family D.source D.target D.dimension ℂ) :
    KingSemistable (kingWeight D) M ↔ KingStable (kingWeight D) M :=
  kingSemistable_iff_stable_of_generic (kingWeight D) (king_generic D h) M

/-- The two loci coincide as subsets of the very same matrix parameter space. -/
theorem king_loci_equal (D : Datum) (h : Indivisible D) :
    {M : Family D.source D.target D.dimension ℂ | KingSemistable (kingWeight D) M} =
    {M | Stable D.weight (toRepresentation D.source D.target D.dimension M)} := by
  ext M
  exact (king_semistable_eq_stable D h M).trans (stable_dictionary D M)

end KroneckerPublishedIndivisibility
end
end

/- Original module: KroneckerPublishedCoverGates -/
section
/-! General source hypotheses for every compatible finite-support cover datum.
The proof works for arbitrary finite base quivers, and retains all support
components. It does not infer connectedness of a lifted support. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace KroneckerPublishedCoverGates
open KroneckerPublishedModuli KroneckerFiniteSupportInducedQuiver
open KroneckerSupportDimensionPushforward
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable (D : Datum) (d : (wordCover D).V →₀ ℕ)

def total : D.V →₀ ℕ := Finsupp.equivFunOnFinite.symm D.dimension

theorem compatible_iff : Compatible D d ↔ d.mapDomain Prod.fst = total D := by
  constructor
  · intro h
    ext v
    exact h v
  · intro h v
    exact congrArg (fun z : D.V →₀ ℕ => z v) h

theorem support_push (h : Compatible D d) :
    (vector d).mapDomain (fun v => v.val.1) = total D :=
  (vector_push d Prod.fst).trans ((compatible_iff D d).mp h)

theorem compatible_nonzero (hD : Nonzero D) (hd : Compatible D d) : d ≠ 0 := by
  intro hz
  apply hD
  funext v
  have h := hd v
  simpa [hz] using h.symm

theorem cover_nonzero (hd : d ≠ 0) : Nonzero (coverDatum D d) := by
  intro h
  apply hd
  ext v
  by_cases hv : v ∈ d.support
  · exact congrFun h ⟨v, hv⟩
  · exact Finsupp.notMem_support_iff.mp hv

theorem cover_acyclic (h : Acyclic D) : Acyclic (coverDatum D d) := by
  obtain ⟨r, hr⟩ := h
  refine ⟨fun v => r v.val.1, ?_⟩
  intro e
  exact hr e.val.1

theorem pushed_weight (e : SupportVertex d →₀ ℕ) :
    e.sum (fun v n => D.weight v.val.1 * (n : ℤ)) =
      ∑ v, D.weight v * (e.mapDomain (fun v => v.val.1) v : ℤ) := by
  have h := Finsupp.sum_mapDomain_index (f := fun v : SupportVertex d => v.val.1)
    (s := e) (h := fun v n => D.weight v * (n : ℤ))
    (by intro v; simp) (by intro v n m; simp [mul_add])
  rw [Finsupp.sum_fintype _ _ (by intro v; simp)] at h
  exact h.symm

theorem cover_balanced (hD : Balanced D) (hd : Compatible D d) :
    Balanced (coverDatum D d) := by
  have h := pushed_weight D d (vector d)
  rw [support_push D d hd] at h
  rw [Finsupp.sum_fintype _ _ (by intro v; simp)] at h
  exact h.trans hD

theorem cover_indivisible (hD : Indivisible D) (hd : Compatible D d) :
    Indivisible (coverDatum D d) := by
  intro e hle hw
  let E : SupportVertex d →₀ ℕ := Finsupp.equivFunOnFinite.symm e
  have hE : E ≤ vector d := hle
  have hpush : E.mapDomain (fun v => v.val.1) ≤ total D := by
    rw [← support_push D d hd]
    exact Finsupp.mapDomain_mono hE
  have hweight : (∑ v, D.weight v *
      (E.mapDomain (fun v => v.val.1) v : ℤ)) = 0 := by
    rw [← pushed_weight D d E, Finsupp.sum_fintype _ _ (by intro v; simp)]
    exact hw
  rcases hD (fun v => E.mapDomain (fun v => v.val.1) v)
    (fun v => hpush v) hweight with hzero | hfull
  · left
    have hz : E.mapDomain (fun v => v.val.1) = 0 := Finsupp.ext (congrFun hzero)
    have he := (KroneckerPositiveFiberTotals.zero_iff (fun v : SupportVertex d => v.val.1) E).mp hz
    exact congrArg DFunLike.coe he
  · right
    have hf : E.mapDomain (fun v => v.val.1) = (vector d).mapDomain (fun v => v.val.1) := by
      rw [support_push D d hd]
      exact Finsupp.ext (congrFun hfull)
    have he := KroneckerPositiveFiberTotals.comparable_equal
      (fun v : SupportVertex d => v.val.1) E (vector d) hE hf
    exact congrArg DFunLike.coe he

end KroneckerPublishedCoverGates
end
end

/- Original module: KroneckerAllMPublishedDatum -/
section
/-! Source hypotheses for the canonical Kronecker family at every arrow count.
This connects the general published-moduli boundary to the fixed all-m target. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAllMPublishedDatum
open KroneckerPublishedModuli KroneckerCanonicalKroneckerModuli
open KroneckerPublishedIndivisibility KroneckerFiniteQuiverHom
open KroneckerRingQuiverFamilies KroneckerMatrixKingDictionary
open scoped BigOperators

def datum (m a b : ℕ) : Datum where
  V := Fin 2
  A := Fin m
  vertices := inferInstance
  arrows := inferInstance
  source := source m
  target := target m
  dimension := dimension a b
  weight := character a b

theorem canonical_eq (m a b : ℕ) :
    canonical (datum m a b) = space m a b := rfl

theorem acyclic (m a b : ℕ) : Acyclic (datum m a b) :=
  ⟨Fin.val, fun _ => by change (0 : ℕ) < 1; decide⟩

theorem connected (m a b : ℕ) (hm : 0 < m) : Connected (datum m a b) := by
  intro u v
  change Fin 2 at u v
  fin_cases u <;> fin_cases v
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨⟨0, hm⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.single ⟨⟨0, hm⟩, Or.inr ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.refl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem balanced (m a b : ℕ) : Balanced (datum m a b) := by
  simp [KroneckerPublishedModuli.Balanced, datum, character, dimension, Fin.sum_univ_two, mul_comm]

theorem nonzero_iff (m a b : ℕ) : Nonzero (datum m a b) ↔ a ≠ 0 ∨ b ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    apply h
    funext v
    simp [datum, dimension, hn]
  · intro h hz
    have ha := congrFun hz (0 : Fin 2)
    have hb := congrFun hz (1 : Fin 2)
    simp [datum, dimension] at ha hb
    exact h.elim (fun hn => hn ha) (fun hn => hn hb)

theorem nonzero_of_source (m a b : ℕ) (ha : 0 < a) : Nonzero (datum m a b) :=
  (nonzero_iff m a b).mpr (Or.inl (Nat.ne_of_gt ha))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem indivisible (m a b : ℕ) (hc : a.Coprime b) : Indivisible (datum m a b) := by
  intro e hle hw
  change Fin 2 → ℕ at e
  change e ≤ dimension a b at hle
  change (∑ v : Fin 2, character a b v * (e v : ℤ)) = 0 at hw
  have hu : e 0 ≤ a := by simpa [datum, dimension] using hle 0
  have hv : e 1 ≤ b := by simpa [datum, dimension] using hle 1
  have he : b * e 0 = a * e 1 := by
    have hz : (b : ℤ) * e 0 - (a : ℤ) * e 1 = 0 := by
      simpa [datum, character, Fin.sum_univ_two, sub_eq_add_neg] using hw
    exact_mod_cast sub_eq_zero.mp hz
  rcases KroneckerCoprimeKingNumerator.equality_zero_or_full hc hu hv he with hz | hf
  · left
    funext v
    fin_cases v <;> simp [hz]
  · right
    funext v
    fin_cases v <;> simp [datum, dimension, hf]

theorem king_character_zero (m a b : ℕ) : kingWeight (datum m a b) (0 : Fin 2) = -(b : ℤ) := rfl

theorem king_character_one (m a b : ℕ) : kingWeight (datum m a b) (1 : Fin 2) = (a : ℤ) := by
  simp [kingWeight, datum, character]

theorem king_scalar_trivial (m a b : ℕ) (c : ℂˣ) :
    KroneckerKingCharacter.character (dimension a b) (kingWeight (datum m a b)) ℂ
      (KroneckerKingCharacter.scalarDiagonal (dimension a b) c) = 1 :=
  KroneckerPublishedIndivisibility.king_scalar_trivial _ (balanced m a b) c

theorem king_stable_iff (m a b : ℕ) (M : Family (source m) (target m) (dimension a b) ℂ) :
    KingStable (kingWeight (datum m a b)) M ↔
      Stable (character a b) (toRepresentation (source m) (target m) (dimension a b) M) :=
  stable_dictionary (datum m a b) M

theorem king_semistable_iff_stable (m a b : ℕ) (hc : a.Coprime b)
    (M : Family (source m) (target m) (dimension a b) ℂ) :
    KingSemistable (kingWeight (datum m a b)) M ↔
      Stable (character a b) (toRepresentation (source m) (target m) (dimension a b) M) :=
  (king_semistable_eq_stable _ (indivisible m a b hc) M).trans (stable_dictionary (datum m a b) M)

theorem cover_acyclic (m a b : ℕ) (d : (wordCover (datum m a b)).V →₀ ℕ) :
    Acyclic (coverDatum (datum m a b) d) :=
  KroneckerPublishedCoverGates.cover_acyclic _ d (acyclic m a b)

theorem cover_indivisible (m a b : ℕ) (hc : a.Coprime b)
    (d : (wordCover (datum m a b)).V →₀ ℕ) (hd : Compatible (datum m a b) d) :
    Indivisible (coverDatum (datum m a b) d) :=
  KroneckerPublishedCoverGates.cover_indivisible _ d (indivisible m a b hc) hd

end KroneckerAllMPublishedDatum
end
end
