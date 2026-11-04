import KroneckerCanonicalRootNonemptiness

section

/-! Every sorted positive integral real root admits a strictly smaller
nonnegative reflected root. This supplies a terminating classification descent. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRealRootDescent

theorem bound (m a b : ℕ) (ha : 0<a)
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b≤1) : b≤m*a := by
  by_contra h
  have hba : (m : ℤ)*a+1≤b := by exact_mod_cast (show m*a+1≤b by omega)
  have ha' : (1 : ℤ)≤a := by exact_mod_cast ha
  have hb' : (1 : ℤ)≤b := by exact_mod_cast (show 1≤b by omega)
  nlinarith

theorem decrease (m a b : ℕ) (hm : 3≤m) (ha : 0<a) (hab : a≤b)
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b≤1)
    (ht0 : 0≤(a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b) : m*a-b<a := by
  have hb := bound m a b ha ht
  have he : ((m*a-b : ℕ) : ℤ)=(m : ℤ)*a-b := by rw [Nat.cast_sub hb,Nat.cast_mul]
  by_contra h
  have hc : (a : ℤ)≤(m : ℤ)*a-b := by
    rw [←he]
    exact_mod_cast (show a≤m*a-b by omega)
  have hab' : (a : ℤ)≤b := by exact_mod_cast hab
  have hm' : (3 : ℤ)≤m := by exact_mod_cast hm
  have ha' : (1 : ℤ)≤a := by exact_mod_cast ha
  have hp := mul_nonneg (sub_nonneg.mpr hab') (show 0≤(m : ℤ)*a-a-b by linarith)
  have hma : 3*(a : ℤ)^2≤(m : ℤ)*a^2 := mul_le_mul_of_nonneg_right hm' (sq_nonneg _)
  nlinarith

theorem reflected (m a b : ℕ) (ha : 0<a)
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=1) :
    ((m*a-b : ℕ) : ℤ)^2+(a : ℤ)^2-(m : ℤ)*(m*a-b : ℕ)*a=1 := by
  have hb := bound m a b ha (le_of_eq ht)
  rw [Nat.cast_sub hb,Nat.cast_mul]
  nlinarith
end KroneckerRealRootDescent
end
end

section

/- Original module: KroneckerRealRootClassification -/
section
/-! Exhaustive classification of all nonnegative integral Tits-one pairs:
they are precisely the reflection recurrence and its source/sink exchange. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRealRootClassification
open KroneckerRootPairRecurrence

theorem sorted (m : ℕ) (hm : 3≤m) (a b : ℕ) (hab : a≤b)
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=1) : ∃ n,pair m n=(a,b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a=0
    · subst a
      have hb : b=1 := by
        simp only [Nat.cast_zero,zero_pow (by omega : 2≠0),zero_add,mul_zero] at ht
        have hb0 : (0 : ℤ)≤b := Int.natCast_nonneg b
        have hb1 : (b : ℤ)=1 := by nlinarith
        exact_mod_cast hb1
      exact ⟨0,by simp [pair,hb]⟩
    · have hap : 0<a := by omega
      have hc := KroneckerRealRootDescent.decrease m a b hm hap hab (le_of_eq ht) (by omega)
      obtain ⟨n,hn⟩ := ih (m*a-b) hc a (Nat.le_of_lt hc)
        (KroneckerRealRootDescent.reflected m a b hap ht)
      refine ⟨n+1,?_⟩
      rw [pair,hn]
      simp only
      rw [Nat.sub_sub_self (KroneckerRealRootDescent.bound m a b hap (le_of_eq ht))]

theorem classify (m : ℕ) (hm : 3≤m) (a b : ℕ)
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=1) :
    (∃ n,pair m n=(a,b)) ∨ (∃ n,pair m n=(b,a)) := by
  rcases le_total a b with hab | hba
  · exact Or.inl (sorted m hm a b hab ht)
  · exact Or.inr (sorted m hm b a hba (by nlinarith))
end KroneckerRealRootClassification
end
end

/- Original module: KroneckerRealRootRealization -/
section
/-! Every nonnegative integral Tits-one dimension pair is realized by an
actual stable canonical representation, including both simple endpoints. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRealRootRealization
open KroneckerCanonicalKroneckerModuli KroneckerRootPairRecurrence

theorem nonempty (m : ℕ) (hm : 3≤m) (a b : ℕ)
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=1) : Nonempty (space m a b) := by
  rcases KroneckerRealRootClassification.classify m hm a b ht with ⟨n,hn⟩ | ⟨n,hn⟩
  · have h := KroneckerCanonicalRootNonemptiness.pair_nonempty m hm n
    simpa only [hn] using h
  · have h := KroneckerCanonicalRootNonemptiness.pair_nonempty m hm n
    have h' : Nonempty (space m b a) := by simpa only [hn] using h
    exact (KroneckerExchangeEuler.nonempty_iff m b a).mp h'
end KroneckerRealRootRealization
end
end
end

