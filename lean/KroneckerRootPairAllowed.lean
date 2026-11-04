import KroneckerTitsOnePrimitive
import KroneckerCanonicalRootNonemptiness

section

/-! The constructed root sequence has unbounded actual source dimensions.
Its Tits value is exactly one at every step, without asymptotic approximations. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootPairHeightGrowth
open Filter KroneckerRootPairRecurrence

theorem height_tendsto (m : ℕ) (hm : 3≤m) : Tendsto (fun n => (pair m n).1) atTop atTop :=
  tendsto_atTop_mono (source_ge_index m hm) tendsto_id

theorem tits_one (m : ℕ) (hm : 3≤m) (n : ℕ) :
    ((pair m n).1 : ℤ)^2+((pair m n).2 : ℤ)^2-(m : ℤ)*(pair m n).1*(pair m n).2=1 := by
  induction n with
  | zero => simp [pair]
  | succ n ih =>
    have he : ((pair m n).1 : ℤ)+(pair m (n+1)).2=(m : ℤ)*(pair m n).2 := by
      exact_mod_cast untruncated m hm n
    have ha : (pair m (n+1)).1=(pair m n).2 := rfl
    rw [ha]
    nlinarith
end KroneckerRootPairHeightGrowth
end
end

section

/-! The actual stable root sequence lies in the manuscript domain, including
positivity, coprimality and geometric nonemptiness, after omitting its simple base. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootPairAllowed
open KroneckerRootPairRecurrence KroneckerCanonicalKroneckerModuli
open KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))

theorem allowed (m : ℕ) (hm : 3≤m) (n : ℕ) :
    Allowed (family H) m (pair m (n+1)).1 (pair m (n+1)).2 := by
  have hg := growth m hm (n+1)
  have hn := source_ge_index m hm (n+1)
  exact ⟨by omega,by omega,
    KroneckerTitsOnePrimitive.coprime _ _ _ (KroneckerRootPairHeightGrowth.tits_one m hm (n+1)),
    KroneckerCanonicalRootNonemptiness.pair_nonempty m hm (n+1)⟩

def dimension (m : ℕ) (hm : 3≤m) (n : ℕ) : Dimension (family H) m :=
  ⟨pair m (n+1),allowed H m hm n⟩
end KroneckerRootPairAllowed
end
end

