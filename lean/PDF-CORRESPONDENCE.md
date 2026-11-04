# Lean correspondence with the current PDF

Date: 3 November 2026. The manuscript has 148 pages.

PDF SHA-256: `f048f51ba61ecc11e890fc15473a984539468f46edf945ca84aed10e6b955a3e`.
Main TeX SHA-256: `246f2755da531f871fa5ad969bc95a5fedc4069b036dde90420cbdd78a6fc24a`.

The title uses `\date{\today{}}`. The footnote retains its forced line
break after "at"; `\skip\footins` has 4pt of additional space above
the separator. The TeX and PDF match the verified title-page build exactly.
All twelve section sources and four figure PDFs are unchanged.

The recorded build completed three pdfLaTeX passes. The title page and
footnote were inspected visually. All 148 page renders were compared with
a control build; only page 1 differs. All 160 mapped statements and all
618 label numbers and page locations are preserved.

This synchronization verifies exact Git blob identity for all 736 project
Lean modules, the focused query file, and the three Lean/configuration
files against the recorded sanity-check inputs and the main project.
No Lean compilation, sanity-check run, or full saved-evidence audit was
performed for this synchronization.

The three local corrections are covered by established Lean declarations.
The theorem statements, proofs, Theorem 1.1 target, and eight external axiom
declarations are unchanged by this alignment update.

| PDF passage | Lean declarations | Exact correspondence |
| --- | --- | --- |
| Lemma 2.24, Claim 1(a), page 20 | `KroneckerCompatibility.root_iff_first_vertical_return`; `KroneckerPaperPathGradings.firstShadow_iff_first_vertical_equality`; `firstShadow_predecessor_and_root`, in [KroneckerGeometricShadows.lean](KroneckerGeometricShadows.lean) | Interior boundaries satisfy `0 < k` and `k < n`. The edge `U_k` has zero-based occurrence index `k-1`. The manuscript balance `A_k` is the negative of Lean's debt. The full-root conclusion gives the required precursor. |
| Theorem 5.8, upper bound, page 56 | `KroneckerRationalZeroIntercept.floor_eq`, in [KroneckerLatestPDFClaims.lean](KroneckerLatestPDFClaims.lean) | Apply the theorem at `i=1` and `s=Gamma(a,b)`. The assumption `q>=2` gives `i<q`. Coprimality and the strict bound `abs (s-p/q) < 1/q^2` give equality of the first-run floors. This is Claim 4 of Lemma 5.3, used together with Claim 3. |
| Lemma 7.40, Claim 4, page 97 | `KroneckerSplitFlowChoiceLemmas.stable_of_positive`, in [KroneckerSplitFlowChoiceLemmas.lean](KroneckerSplitFlowChoiceLemmas.lean); `ZeroSumGlueData.added_invariant_iff`, in [KroneckerManuscriptGluingStability.lean](KroneckerManuscriptGluingStability.lean) | `ProperGluingData` includes arbitrary `vertex`, `color`, `vacant`, `map`, and `nonzero` families. The map at edge `e` has type `C ->_C (T e.val.2).ZS.Space (vertex e)`. The two injectivity fields express the gluing hypotheses. Stability follows for any such choice and positive flow. |

The index restriction excludes the empty prefix. The floor theorem also handles
`i=0`, although the application here uses `i=1`. For gluing, the map is not
assumed to be an identity: `added_invariant_iff` uses `D.map e` and
`D.nonzero e` explicitly. These checks are source correspondence self-review.
They do not independently verify the manuscript's entire prose proof or the
published external inputs.

The [focused Lean check](verification/CurrentPDFCorrectionsCheck.lean) prints
the seven relevant declarations and their axiom dependencies. After building
the project, run it from the repository root:

```bash
lake env lean lean/verification/CurrentPDFCorrectionsCheck.lean
```

No Lean compilation was run for this alignment update. The focused check has
been checked against the existing declaration names and saved axiom profiles;
it has not been executed by Lean. It introduces no theorem, definition, axiom,
or proof. The default Lake build contains 736 project modules.

The main project's saved compilation evidence has 733 source files identical to
their compiler snapshots. Three files have pinned edits confined to whole-line documentation
comments: `KroneckerCanonicalKroneckerModuli`, `KroneckerCitedGeometry`, and
`KroneckerReadableMain`. Their nonblank code lines, including indentation, are
identical to the compiled snapshots. Compiler records and source snapshots are
preserved. No compiled object reuse or fresh kernel compilation is claimed
for these comment edits.
