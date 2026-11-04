import KroneckerUpperEntropyKernel

noncomputable section
set_option autoImplicit false
namespace KroneckerEntropyRootTransfer
open Filter
open scoped Topology

theorem rpow_eq_exp_log_div (E a : ℝ) (hE : 0 < E) :
    E^(1/a) = Real.exp (Real.log E/a) := by
  rw [Real.rpow_def_of_pos hE]
  congr 1
  ring

variable {α : Type*} {l : Filter α} {E a : α → ℝ} {L : ℝ}

theorem root_limit_of_entropy (hE : ∀ᶠ i in l, 0 < E i)
    (h : Tendsto (fun i => Real.log (E i)/a i) l (𝓝 L)) :
    Tendsto (fun i => (E i)^(1/a i)) l (𝓝 (Real.exp L)) := by
  apply (Real.continuous_exp.tendsto L |>.comp h).congr'
  exact hE.mono fun i hi => (rpow_eq_exp_log_div (E i) (a i) hi).symm

theorem entropy_limit_of_root {B : ℝ} (hB : 0 < B)
    (hE : ∀ᶠ i in l, 0 < E i)
    (h : Tendsto (fun i => (E i)^(1/a i)) l (𝓝 B)) :
    Tendsto (fun i => Real.log (E i)/a i) l (𝓝 (Real.log B)) := by
  apply (h.log hB.ne').congr'
  exact hE.mono fun i hi => by
    dsimp only
    rw [rpow_eq_exp_log_div _ _ hi, Real.log_exp]

theorem entropy_iff_root {B : ℝ} (hB : 0 < B) (hE : ∀ᶠ i in l, 0 < E i) :
    Tendsto (fun i => Real.log (E i)/a i) l (𝓝 (Real.log B)) ↔
    Tendsto (fun i => (E i)^(1/a i)) l (𝓝 B) := by
  constructor
  · intro h
    simpa [Real.exp_log hB] using root_limit_of_entropy hE h
  · exact entropy_limit_of_root hB hE

end KroneckerEntropyRootTransfer
