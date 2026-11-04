import Mathlib.Tactic

section

set_option autoImplicit false
namespace KroneckerChainFlowRecovery

def leftEnd (x : ℝ) (l : ℕ → ℝ) := x-l 0
def rightEnd (x : ℝ) (n : ℕ) (r : ℕ → ℝ) := x-r n
def middleSize (l r : ℕ → ℝ) (t : ℕ) := l t+r t-1
def internalSize (x : ℝ) (l r : ℕ → ℝ) (t : ℕ) := x-r t-l (t+1)

/-- The labeled chain block sizes recover every flow, including the single-connector case. -/
theorem flow_recovery (x : ℝ) (n : ℕ) (l r L R : ℕ → ℝ)
    (hend : leftEnd x l=leftEnd x L)
    (hm : ∀ t≤n,middleSize l r t=middleSize L R t)
    (hi : ∀ t<n,internalSize x l r t=internalSize x L R t) :
    ∀ t≤n,l t=L t ∧ r t=R t := by
  intro t ht
  induction t with
  | zero =>
    have hl : l 0=L 0 := by unfold leftEnd at hend; linarith
    have hr := hm 0 (by omega)
    dsimp [middleSize] at hr
    exact ⟨hl,by linarith⟩
  | succ t ih =>
    have hp := ih (by omega)
    have hI := hi t (by omega)
    have hM := hm (t+1) ht
    dsimp [internalSize] at hI
    dsimp [middleSize] at hM
    constructor <;> linarith


end KroneckerChainFlowRecovery
end

section

set_option autoImplicit false
namespace KroneckerChainPositiveBins

def InBin (x : ℝ) (i : ℕ) (y : ℝ) : Prop :=
  (i : ℝ)*x/256≤y ∧ y<((i : ℝ)+1)*x/256

theorem bin_positive (x y : ℝ) (i : ℕ) (hx : 100000≤x) (hi : 1≤ i)
    (h : InBin x i y) : 0<y := by
  have hiR : (1 : ℝ)≤ i := by exact_mod_cast hi
  dsimp [InBin] at h
  nlinarith

theorem two_bin_upper (x l r : ℝ) (i h : ℕ) (hx : 0<x)
    (hi : i+h≤253) (hl : InBin x i l) (hr : InBin x h r) : l+r<x-x/256 := by
  have hiR : (i : ℝ)+(h : ℝ)≤253 := by exact_mod_cast hi
  dsimp [InBin] at hl hr
  nlinarith

theorem middle_block_size_bounds (x l r : ℝ) (i h : ℕ) (hx : 100000≤x)
    (hi : 1≤ i) (hh : i+h≤253) (hl : InBin x i l) (hr : InBin x h r) (hrp : 0<r) :
    256<l+r-1 ∧ l+r-1<x ∧ 0<x+1-l-r := by
  have hu := two_bin_upper x l r i h (by linarith) hh hl hr
  have hiR : (1 : ℝ)≤ i := by exact_mod_cast hi
  dsimp [InBin] at hl
  constructor
  · nlinarith
  · constructor <;> linarith

theorem internal_block_size_bounds (x l r : ℝ) (i h : ℕ) (hx : 100000≤x)
    (hi : 1≤ i) (hh : i+h≤253) (hl : InBin x i l) (hr : InBin x h r) (hrp : 0<r) :
    256<x-r-l ∧ x-r-l<x := by
  have hu := two_bin_upper x l r i h (by linarith) hh hl hr
  have hlp := bin_positive x l i hx hi hl
  constructor <;> linarith

theorem end_block_size_bounds (x y : ℝ) (i : ℕ) (hx : 100000≤x)
    (hi : i≤253) (hy : InBin x i y) (hyp : 0<y) : 256<x-y ∧ x-y<x := by
  have hiR : (i : ℝ)≤253 := by exact_mod_cast hi
  dsimp [InBin] at hy
  constructor
  · nlinarith
  · linarith

end KroneckerChainPositiveBins
end

