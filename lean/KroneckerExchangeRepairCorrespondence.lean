import KroneckerExchangeTransport
import KroneckerLiteralRepair
import KroneckerRepairIndexCorrespondence

/-! Equality of the geometric exchange grading with the deterministic
manuscript repair, for every AdjShellExch and every connected colored input. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerExchangeRepairCorrespondence
open KroneckerPaperPaths KroneckerNaturalPathGradings
open KroneckerExplicitShellCorrespondence KroneckerManuscriptExchangeDefinitions
open KroneckerStack KroneckerColoredEdges KroneckerAdjacentExchangeLemma
open KroneckerCanonicalExchange KroneckerExchangeTransport KroneckerLiteralRepair

/-- The source shell is the manuscript's explicit grading. -/
def sourceGrading (ξ : AdjShellExch) (f : Grading ξ.X) : Grading ξ.Y :=
  KroneckerManuscriptShell.GShell ξ.X f (ξ.u.val+1) (ξ.v.val+1) 1 0

def position (ξ : AdjShellExch) (f : Grading ξ.X) : ℕ :=
  repairPosition ξ.right ξ.r (gradedWord ξ.Y (sourceGrading ξ f))

def reduction (ξ : AdjShellExch) (f : Grading ξ.X) : ℕ :=
  literalDelta ξ.right ξ.r (gradedWord ξ.Y (sourceGrading ξ f))

/-- Copy horizontal grades through τ and lower exactly the selected vertical grade. -/
def RepGr (ξ : AdjShellExch) (f : Grading ξ.X) : Grading ξ.Y' := fun e =>
  let k := (edgeEquiv ξ.Y').symm e
  if ξ.Y'.steps[k.val] then transportedShell ξ f e
  else if k.val = position ξ f then transportedShell ξ f e - reduction ξ f
  else transportedShell ξ f e

theorem uncolor_edges (P : TNEPath) (a : ColoredGrading 3 P) :
    coloredWord (edges a) = gradedWord P a.1 := by
  obtain ⟨c,rfl⟩ := KroneckerRecolConcatenation.fromPalette_surjective 3 P a
  rw [edges_fromPalette,KroneckerColoredEdgeDictionary.ofColoring_word,
    KroneckerRecolShell.gradedWord_fromPalette]

theorem geometric_exchange_word (ξ : AdjShellExch) (a : ColoredSet ξ.X) :
    gradedWord ξ.Y' (ξ.exchange a).2.val.1 =
      repairWord ξ.right ξ.r (gradedWord ξ.Y (sourceGrading ξ a.2.val.1)) := by
  have hh := KroneckerWrappedExchangeMap.exchangeMap_repairWord ξ.spec
    (operational (source ξ.spec ξ.origin) a)
  rw [← exchange_core ξ.spec ξ.origin a] at hh
  change coloredWord (edges (ξ.exchange a).2.val) =
    repairWord ξ.right (ξ.spec.u+1+(ξ.spec.P.length+1))
      (coloredWord (KroneckerEdgeShell.edgeShell ξ.spec.u ξ.spec.v
        ξ.spec.hu ξ.spec.hv ξ.spec.hm (edges a.2.val))) at hh
  rw [← shell_edges,uncolor_edges,uncolor_edges] at hh
  have hp : ξ.spec.u+1+(ξ.spec.P.length+1) = ξ.r := by
    simp [AdjShellExch.spec,KroneckerAdjacentExchangeLemma.spec,AdjShellExch.r]
    omega
  rw [hp] at hh
  exact hh

theorem geometric_reduction_eq (ξ : AdjShellExch) (a : ColoredSet ξ.X) :
    reduction ξ a.2.val.1 =
      repairDelta ξ.right ξ.r (gradedWord ξ.Y (sourceGrading ξ a.2.val.1)) := by
  let z := operational ξ.X a
  have he := (KroneckerWrappedExchangeWitness.chosen ξ.spec z).exchange
  have hc := exchange_context he
    (KroneckerEdgeShell.edgePrefix 3 ξ.spec.u ξ.spec.hu)
    (KroneckerEdgeShell.edgeSuffix 3 ξ.spec.v ξ.spec.hv ξ.spec.hm)
  have hh := reduction_eq hc
  have hp : (KroneckerEdgeShell.edgePrefix 3 ξ.spec.u ξ.spec.hu).length +
      (ξ.spec.P.length+1) = ξ.r := by
    simp [KroneckerEdgeShell.edgePrefix,AdjShellExch.spec,
      KroneckerAdjacentExchangeLemma.spec,AdjShellExch.r]
    omega
  rw [hp] at hh
  simp only [List.append_assoc] at hh
  change literalDelta ξ.right ξ.r
      (coloredWord (KroneckerEdgeShell.edgeShell ξ.spec.u ξ.spec.v ξ.spec.hu ξ.spec.hv ξ.spec.hm
        (edges a.2.val))) =
    repairDelta ξ.right ξ.r
      (coloredWord (KroneckerEdgeShell.edgeShell ξ.spec.u ξ.spec.v ξ.spec.hu ξ.spec.hv ξ.spec.hm
        (edges a.2.val))) at hh
  rw [← shell_edges,uncolor_edges] at hh
  exact hh

theorem RepGr_word (ξ : AdjShellExch) (f : Grading ξ.X) :
    gradedWord ξ.Y' (RepGr ξ f) =
      (gradedWord ξ.Y' (transportedShell ξ f)).modify (position ξ f) (lower (reduction ξ f)) := by
  apply List.ext_getElem
  · simp
  · intro k hk hl
    have hkY : k < ξ.Y'.steps.length := by simpa using hk
    simp only [List.getElem_modify,gradedWord,List.getElem_ofFn,RepGr,
      Equiv.symm_apply_apply]
    by_cases hp : k = position ξ f
    · subst k
      by_cases hd : ξ.Y'.steps[position ξ f] = true <;> simp [hd,lower]
    · have hp' : position ξ f ≠ k := Ne.symm hp
      by_cases hd : ξ.Y'.steps[k] = true <;> simp [hd,hp,hp']

/-- Literal equality of the actual map and the manuscript's deterministic grading. -/
theorem exchange_eq_RepGr (ξ : AdjShellExch) (a : ColoredSet ξ.X) :
    (ξ.exchange a).2.val.1 = RepGr ξ a.2.val.1 := by
  apply KroneckerRecolShell.gradedWord_injective ξ.Y'
  rw [geometric_exchange_word,RepGr_word]
  have ht := (shellPair ξ).transported_word_exact (sourceGrading ξ a.2.val.1)
  rw [shell_pair_position] at ht
  change gradedWord ξ.Y' (transportedShell ξ a.2.val.1) = _ at ht
  rw [ht,geometric_reduction_eq]
  rfl

end KroneckerExchangeRepairCorrespondence

#print axioms KroneckerExchangeRepairCorrespondence.geometric_exchange_word
#print axioms KroneckerExchangeRepairCorrespondence.geometric_reduction_eq
#print axioms KroneckerExchangeRepairCorrespondence.exchange_eq_RepGr
