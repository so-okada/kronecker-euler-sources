import KroneckerRootPairRecurrence
import KroneckerReflectionPrimitive

/- Original module: KroneckerCanonicalSimpleRoots -/
section
/-! The two simple-root canonical moduli are actually nonempty. These supply
concrete starting representations for the reflection-generated real roots. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalSimpleRoots
open Module KroneckerFiniteQuiverHom KroneckerCanonicalKroneckerModuli KroneckerReflectionPairModel

theorem source_nonempty (m : ℕ) : Nonempty (space m 1 0) := by
  let R : PairRep m 1 0 := fun _ => 0
  have hs : PairStable R := by
    intro U W _ hn hp
    have hu : finrank ℂ U≤1 := by simpa [Space] using U.finrank_le
    have hw : finrank ℂ W=0 := by
      have hle : finrank ℂ W≤0 := by simpa [Space] using W.finrank_le
      omega
    omega
  exact (space_nonempty_iff m 1 0).mpr ⟨toRepresentation R,
    (KroneckerReflectionPairStability.stable_iff R).mpr hs⟩

theorem sink_nonempty (m : ℕ) : Nonempty (space m 0 1) :=
  (KroneckerExchangeEuler.nonempty_iff m 1 0).mp (source_nonempty m)
end KroneckerCanonicalSimpleRoots
end
end

/- Original module: KroneckerCanonicalRootNonemptiness -/
section
/-! Every real-root pair in the recurrence is realized by an actual stable
canonical representation. This is geometric nonemptiness, not an arithmetic
admissibility declaration. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalRootNonemptiness
open KroneckerCanonicalKroneckerModuli KroneckerRootPairRecurrence

theorem successor_nonempty (m a b : ℕ) (hb : 0<b) (hn : Nonempty (space m a b)) :
    Nonempty (space m b (m*b-a)) := by
  have h1 := (KroneckerExchangeEuler.nonempty_iff m a b).mp hn
  have h2 := KroneckerReflectionNonemptyTransfer.reflected_nonempty m b a hb h1
  exact (KroneckerExchangeEuler.nonempty_iff m (m*b-a) b).mp h2

theorem pair_nonempty (m : ℕ) (hm : 3≤m) (n : ℕ) :
    Nonempty (space m (pair m n).1 (pair m n).2) := by
  induction n with
  | zero => exact KroneckerCanonicalSimpleRoots.sink_nonempty m
  | succ n ih =>
    change Nonempty (space m (pair m n).2 (m*(pair m n).2-(pair m n).1))
    exact successor_nonempty m (pair m n).1 (pair m n).2 (by have h:=growth m hm n;omega) ih
end KroneckerCanonicalRootNonemptiness
end
end
