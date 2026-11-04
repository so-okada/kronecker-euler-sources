import KroneckerReflectionCoordinateStability
import KroneckerReflectionPairStability
import KroneckerExchangeEuler

section

/-! Actual nonempty canonical moduli yield nonempty reflected canonical moduli
of dimension (ma-b,a). This is a constructive representation-level theorem,
not yet the homeomorphism or Euler reflection assertion. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionNonemptyTransfer
open KroneckerCanonicalKroneckerModuli KroneckerReflectionPairModel

theorem reflected_nonempty (m a b : ℕ) (ha : 0<a) (hn : Nonempty (space m a b)) :
    Nonempty (space m (m*a-b) a) := by
  obtain ⟨R,hR⟩ := (space_nonempty_iff m a b).mp hn
  let P := fromRepresentation R
  have hs : PairStable P := (KroneckerReflectionPairStability.stable_iff P).mp hR
  let h := KroneckerReflectionStableSurjectivity.incoming_surjective P ha hs
  let S := KroneckerReflectionKernelCoordinates.reflected P h
  apply (space_nonempty_iff m (m*a-b) a).mpr
  exact ⟨toRepresentation S,(KroneckerReflectionPairStability.stable_iff S).mpr
    (KroneckerReflectionCoordinateStability.reflected_stable P ha hs h)⟩
end KroneckerReflectionNonemptyTransfer
end
end

section

/- Original module: KroneckerReflectionNonemptyEquivalence -/
section
/-! Reflection nonemptiness is an equivalence, proved constructively by
applying the opposite reflection and the actual exchange homeomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionNonemptyEquivalence
open KroneckerCanonicalKroneckerModuli

theorem nonempty_iff (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) :
    Nonempty (space m a b) ↔ Nonempty (space m (m*a-b) a) := by
  constructor
  · exact KroneckerReflectionNonemptyTransfer.reflected_nonempty m a b ha
  · intro H
    have h1 := (KroneckerExchangeEuler.nonempty_iff m (m*a-b) a).mp H
    have h2 := KroneckerReflectionNonemptyTransfer.reflected_nonempty m a (m*a-b) ha h1
    have he : m*a-(m*a-b)=b := Nat.sub_sub_self hb
    rw [he] at h2
    exact (KroneckerExchangeEuler.nonempty_iff m b a).mp h2
end KroneckerReflectionNonemptyEquivalence
end
end

/- Original module: KroneckerReflectionPrimitive -/
section
/-! Global reflection preserves the primitive dimension condition. The proof
uses common divisors and the exact untruncated dimension identity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionPrimitive

theorem gcd (m a b : ℕ) (hb : b≤m*a) : Nat.gcd (m*a-b) a=Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · have hda := Nat.gcd_dvd_right (m*a-b) a
    have hdc := Nat.gcd_dvd_left (m*a-b) a
    have hdm := dvd_mul_of_dvd_right hda m
    have hdb := Nat.dvd_sub hdm hdc
    rw [Nat.sub_sub_self hb] at hdb
    exact Nat.dvd_gcd hda hdb
  · exact Nat.dvd_gcd (Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left a b) m)
      (Nat.gcd_dvd_right a b)) (Nat.gcd_dvd_left a b)

theorem coprime_iff (m a b : ℕ) (hb : b≤m*a) :
    Nat.Coprime (m*a-b) a ↔ Nat.Coprime a b := by
  change Nat.gcd (m*a-b) a=1 ↔ Nat.gcd a b=1
  rw [gcd m a b hb]
end KroneckerReflectionPrimitive
end
end
end

