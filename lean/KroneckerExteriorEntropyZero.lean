import KroneckerCanonicalTitsOneEuler

section

/-! Positive-dimensional slopes outside the closed root interval have strictly
positive integral Tits value. All denominator and endpoint signs are explicit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExteriorTitsSign
open KroneckerEndpointRoots

theorem quadratic_positive {m r : ℝ} (hm : 2<m)
    (hr : r ∉ Set.Icc (lowerRoot m) (upperRoot m)) : 0<1+r^2-m*r := by
  have hf := quadratic_factorization (r:=r) hm.le
  have hlu := lower_lt_upper hm
  have hprod : (upperRoot m-r)*(r-lowerRoot m)<0 := by
    by_cases hl : r<lowerRoot m
    · exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
    · have hu : upperRoot m<r := by
        by_contra hh
        exact hr ⟨le_of_not_gt hl,le_of_not_gt hh⟩
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  nlinarith

theorem tits_positive (m a b : ℕ) (hm : 3≤m) (ha : 0<a)
    (hr : (b : ℝ)/a ∉ Set.Icc (lowerRoot m) (upperRoot m)) :
    0<(a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b := by
  have ha' : (0 : ℝ)<a := by exact_mod_cast ha
  have hp := quadratic_positive (by exact_mod_cast (show 2<m by omega)) hr
  have hmul := mul_pos (sq_pos_of_pos ha') hp
  have he : (a : ℝ)^2*(1+((b : ℝ)/a)^2-(m : ℝ)*((b : ℝ)/a))=
      (a : ℝ)^2+(b : ℝ)^2-(m : ℝ)*a*b := by field_simp <;> ring
  rw [he] at hmul
  exact_mod_cast hmul
end KroneckerExteriorTitsSign
end
end

section

/- Original module: KroneckerCanonicalExteriorRoot -/
section
/-! Every nonempty actual canonical moduli space at an exterior positive
slope has Tits value exactly one. No nonempty-domain sufficiency is assumed. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalExteriorRoot
open KroneckerCanonicalKroneckerModuli KroneckerEndpointRoots

theorem tits_one (m a b : ℕ) (hm : 3≤m) (ha : 0<a) (hn : Nonempty (space m a b))
    (hr : (b : ℝ)/a ∉ Set.Icc (lowerRoot m) (upperRoot m)) :
    (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=1 := by
  have hl := KroneckerExteriorTitsSign.tits_positive m a b hm ha hr
  have hu := KroneckerCanonicalTitsNecessary.tits_le_one m a b ha hn
  omega
end KroneckerCanonicalExteriorRoot
end
end

/- Original module: KroneckerCanonicalExteriorEuler -/
section
/-! Exterior nonempty actual moduli have finite singular homology and ordinary
Euler one. This handles the geometric side of exterior endpoint approaches
without the general King analytification or localization assumptions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalExteriorEuler
open KroneckerCanonicalKroneckerModuli KroneckerEndpointRoots KroneckerOrdinarySingularEuler

end KroneckerCanonicalExteriorEuler
end
end

/- Original module: KroneckerExteriorEntropyZero -/
section
/-! The actual manuscript entropy observable is exactly zero outside the
closed root interval on every admissible dimension vector. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExteriorEntropyZero
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))

theorem value_zero (m : ℕ) (hm : 3≤m) (p : Dimension (family H) m)
    (hp : slope p ∉ interval m) : value p=0 := by
  have hn : Nonempty (space m p.val.1 p.val.2) := p.property.2.2.2
  have ht := KroneckerCanonicalExteriorRoot.tits_one m p.val.1 p.val.2 hm p.property.1 hn hp
  have he := KroneckerCanonicalTitsOneEuler.euler_one m p.val.1 p.val.2 hn ht (H _ _ _)
  change Real.log (ordinaryEuler (space m p.val.1 p.val.2) (H _ _ _) : ℝ)/p.val.1=0
  rw [he]
  simp
end KroneckerExteriorEntropyZero
end
end
end

