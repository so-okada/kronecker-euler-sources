import KroneckerGeometricShadows
import KroneckerLatestPDFClaims
import KroneckerSplitFlowChoiceLemmas
import KroneckerManuscriptGluingStability

/-! Correspondence with the 148-page PDF dated 3 November 2026.
PDF SHA-256: 21972b60ad9d1fb14b9084b2ca95d7ee4ce19ba3ff9f9c1b25f8323dd4b78a0e.
Run from the repository root after `lake build`:
  lake env lean lean/verification/CurrentPDFCorrectionsCheck.lean
This file prints established statements and their axiom dependencies.
-/

/-! Lemma 2.24, Claim 1(a), PDF page 20.
Boundary k counts completed edges; manuscript U_k is occurrence k-1.
The interior quantifiers require 0 < k and k < n. The manuscript balance
A_k is minus the Lean debt, so positive debt gives equation (2.8).
-/
#check KroneckerCompatibility.root_iff_first_vertical_return
#print axioms KroneckerCompatibility.root_iff_first_vertical_return
#check KroneckerPaperPathGradings.firstShadow_iff_first_vertical_equality
#print axioms KroneckerPaperPathGradings.firstShadow_iff_first_vertical_equality
#check KroneckerPaperPathGradings.firstShadow_predecessor_and_root
#print axioms KroneckerPaperPathGradings.firstShadow_predecessor_and_root

/-! Theorem 5.8, upper bound, PDF page 56.
Claim 4 of Lemma 5.3 applies to floor_eq at i=1 and s=Gamma(a,b).
The hypothesis q>=2 gives 1<q; coprimality and the strict perturbation
bound give the first-run floor equality used alongside Claim 3.
-/
#check KroneckerRationalZeroIntercept.floor_eq
#print axioms KroneckerRationalZeroIntercept.floor_eq

/-! Lemma 7.40, Claim 4, PDF page 97.
ProperGluingData extends ZeroSumGlueData: vertex, color, vacant, map,
and nonzero quantify the slot and map families. Each map has domain C
and target (T e.val.2).ZS.Space (vertex e). The two injectivity fields
express the gluing hypotheses. stable_of_positive accepts any such D.
-/
#check KroneckerSplitGluingLemmas.ProperGluingData
#print axioms KroneckerSplitGluingLemmas.ProperGluingData
#check KroneckerManuscriptQuiverDefinitions.ZeroSumGlueData.added_invariant_iff
#print axioms KroneckerManuscriptQuiverDefinitions.ZeroSumGlueData.added_invariant_iff
#check KroneckerSplitFlowChoiceLemmas.stable_of_positive
#print axioms KroneckerSplitFlowChoiceLemmas.stable_of_positive
