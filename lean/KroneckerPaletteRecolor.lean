import KroneckerColoredShell

/-! The one-edge form of Definition 3.2 in the zero-based counting palette.
Palette color zero corresponds to manuscript color one. -/
set_option autoImplicit false
namespace KroneckerColoring
open KroneckerColoredShell

def regrade {m : ℕ} (p : Palette m) (k : ℕ) (hk : k ≤ m) : Palette m :=
  if k = grade p then p else fixedColor m k hk

@[simp] theorem regrade_grade {m : ℕ} (p : Palette m) (k : ℕ) (hk : k ≤ m) :
    grade (regrade p k hk) = k := by
  by_cases h : k = grade p <;> simp [regrade, h, fixedColor_grade]

@[simp] theorem regrade_same {m : ℕ} (p : Palette m) :
    regrade p (grade p) (grade_le p) = p := by simp [regrade]

theorem regrade_changed {m : ℕ} (p : Palette m) (k : ℕ) (hk : k ≤ m)
    (h : k ≠ grade p) : regrade p k hk = fixedColor m k hk := by
  simp [regrade, h]

def RespectsRecol {m : ℕ} (p q : Palette m) : Prop :=
  (grade q = grade p → q = p) ∧ (grade q ≠ grade p → q.2.val = 0)

theorem regrade_respects {m : ℕ} (p : Palette m) (k : ℕ) (hk : k ≤ m) :
    RespectsRecol p (regrade p k hk) := by
  unfold regrade
  split_ifs with h
  · exact ⟨fun _ => rfl, fun hn => False.elim (hn rfl)⟩
  · exact ⟨fun he => False.elim (h he), fun _ => rfl⟩

theorem respects_self {m : ℕ} (p : Palette m) : RespectsRecol p p := by
  simp [RespectsRecol]

theorem respects_zero {m : ℕ} (p : Palette m) : RespectsRecol p (zeroColor m) := by
  constructor
  · intro h
    exact (grade_zero_unique h.symm).symm
  · intro _; rfl

theorem regrade_one_based_color {m : ℕ} (p : Palette m) (k : ℕ) (hk : k ≤ m) :
    (regrade p k hk).2.val + 1 = if k = grade p then p.2.val + 1 else 1 := by
  by_cases h : k = grade p
  · have hp : regrade p k hk = p := ite_eq_left h
    exact (congrArg (fun q : Palette m => q.2.val + 1) hp).trans (ite_eq_left h).symm
  · have hp := regrade_changed p k hk h
    exact (congrArg (fun q : Palette m => q.2.val + 1) hp).trans (ite_eq_right h).symm

end KroneckerColoring
