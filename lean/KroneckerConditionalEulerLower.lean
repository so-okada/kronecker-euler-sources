import KroneckerFixedFactor
import KroneckerRationalFrameLower
import KroneckerFrameIdentity

/- Original module: KroneckerLowerPerturbation -/
section
/-! An error tending to zero does not change eventual asymptotic lower bounds. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerLowerPerturbation
open KroneckerFixedFactor



end KroneckerLowerPerturbation
end

/- Original module: KroneckerRationalScaledLower -/
section
/-! Remove the fixed dictionary factor from the rational lower-bound
reduction. The finite scaffold hypotheses remain explicit. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerRationalScaledLower
open KroneckerPeriodicWords KroneckerPeriodicBounds KroneckerPeriodicTail
open KroneckerRationalLowerReduction KroneckerLowerPerturbation


end KroneckerRationalScaledLower
end

/- Original module: KroneckerConditionalEulerLower -/
section
/-! Connect literal run-word counts to the existing literature-relative frame
identity. The rational lower bound still explicitly requires phase classification. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerConditionalEulerLower
open KroneckerWordCounts KroneckerPeriodicTail KroneckerFrameSlope KroneckerFrameBadDensity
open KroneckerMechanicalWords KroneckerMechanicalWindows KroneckerBadWindowBounds
open KroneckerFrameScaffoldEventual KroneckerRationalFrameLower KroneckerRationalScaledLower

open KroneckerStack KroneckerColoring KroneckerDyck KroneckerFrameIdentity
open KroneckerFrameSlope KroneckerFrameBadDensity KroneckerMechanicalRuns KroneckerMechanicalWords
open KroneckerWordCounts

theorem pathCount_shapePrefix (m n c : ℕ) (f : ℕ → Bool) :
    pathCount m (shapePrefix f n) c = Nat.card {g : Coloring m n // Connected m (word f g) c} := by
  generalize hU : shapePrefix f n = U
  have hn : U.length = n := by rw [← hU]; simp [shapePrefix]
  subst n
  have hw (g : Coloring m U.length) : pathWord U g = word f g := by
    unfold pathWord word
    congr 1
    funext i
    congr 1
    have hget := congrArg (fun Z : List Bool => Z[i.val]?.getD false) hU
    simpa [shapePrefix, KroneckerWordCounts.pathShape, List.getD, i.isLt] using hget.symm
  change Nat.card {g : Coloring m U.length // Connected m (pathWord U g) c} = _
  simp only [hw]

theorem parameter_frame_slope (p : Parameters) : frameSlope p.a p.b p.d₁ = (p.d₂ : ℝ)/(p.d₁ : ℝ) := by
  have ha0 : (p.a : ℝ) ≠ 0 := by have := p.ha; exact_mod_cast (show p.a ≠ 0 by omega)
  have hd0 : (p.d₁ : ℝ) ≠ 0 := by have := p.ha; have := p.hd₁; exact_mod_cast (show p.d₁ ≠ 0 by omega)
  have hdet : (p.b : ℝ)*(p.d₁ : ℝ)-(p.a : ℝ)*(p.d₂ : ℝ)=1 := by exact_mod_cast p.determinant
  unfold frameSlope
  field_simp
  nlinarith

theorem parameter_natRun (p : Parameters) (i : ℕ) :
    natRun (frameSlope p.a p.b p.d₁) 0 i = runLength p.d₁ p.d₂ i := by
  rw [parameter_frame_slope]
  apply Int.natCast_inj.mp
  rw [natRun_cast _ _ _ (by positivity), runLength_floor]
  simp [mechanicalRun, mechanicalPrefix, mul_comm]

theorem literal_frame_shape (p : Parameters) :
    runWord (frameWord p.a p.b p.d₁) = shapePrefix (frameShape p) (frameLength p) := by
  rw [finite_frame_word]
  simp only [frameWord, runWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  congr 1
  have hword : mechanicalWord (frameSlope p.a p.b p.d₁) 0 0 p.a =
      (List.range p.a).map (runLength p.d₁ p.d₂) := by
    apply List.ext_getElem
    · simp [mechanicalWord_length]
    · intro i hi hi'
      simp [mechanicalWord, parameter_natRun]
  rw [hword, List.flatMap_map]

theorem literal_frame_identity (p : Parameters) (E : ℤ) (s : Literature p E) :
    (runCount p.m (frameWord p.a p.b p.d₁) 0 : ℤ) = (p.m : ℤ)*E := by
  rw [runCount, literal_frame_shape, pathCount_shapePrefix]
  exact finite_frame_identity p E s




end KroneckerConditionalEulerLower
end
