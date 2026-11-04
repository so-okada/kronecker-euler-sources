# On Douglas' conjecture for m-Kronecker quivers

[PDF](lean/manuscript/kronecker-entropy.pdf#page=1) / [TeX source](lean/manuscript/kronecker-entropy.tex) / [Main Theorem 1.1 in Lean](lean/KroneckerReadableMain.lean) / [Formal statement](lean/KroneckerManuscriptTarget.lean)

## Lean verification

The recorded Lean build passes without `sorry` or `sorryAx` relative to the following eight external inputs and Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

The source contains no proof-placeholder use of `admit` and no use of `native_decide`.

Compilation verifies the encoded proofs; it does not prove the external inputs or independently verify the manuscript's prose. 

## Eight external interfaces

The linked Lean files state the exact hypotheses of each accepted input.

| Lean declaration | Accepted mathematical input | Sources |
| --- | --- | --- |
| [king_dimca_realization](lean/KroneckerCitedGeometry.lean) | Stable-moduli realization and finite rational homology. The quotient construction uses King and Reineke; the finiteness result uses Dimca's textbook. | [King][King], [Reineke 2008][Rei08], [Dimca][Dimca] |
| [blmmr_theorem_4_10](lean/KroneckerFiniteCoefficientIntegration.lean) | BLMMR Theorem 4.10(2): tight-grading counts independent of the admissible frame, packaged as a coefficient series. | [BLMMR][B] |
| [blmmr_theorem_3_2](lean/KroneckerFiniteCoefficientIntegration.lean) | BLMMR Theorem 4.10(1), followed by Theorem 3.2: identification of the counting series with the wall function and its Euler-sum functional equation, specialized to equal parameters. | [BLMMR][B] |
| [reineke_weist_theorem_12_1](lean/KroneckerFiniteCoefficientIntegration.lean) | Reineke–Weist Theorem 12.1: comparison of the complete bipartite Euler sum with $m$ times the Kronecker Euler characteristic, using the stated dimension convention. | [Reineke–Weist][RW] |
| [king_walter_positive](lean/KroneckerPublishedInputBoundary.lean) | Euler characteristic at least one for nonempty acyclic stable moduli under the stated stability-indivisibility hypothesis. | [King][King], [King–Walter][KW] |
| [weist_adjacent](lean/KroneckerPublishedInputBoundary.lean) | Weist Theorem 6.6: the exact Euler-characteristic formula for dimensions $(a,a+1)$. | [Weist][Weist] |
| [weist_localization](lean/KroneckerPublishedInputBoundary.lean) | The $m=3$ instance of Weist Corollary 3.16: Euler-characteristic localization over translation classes on the universal cover. | [Weist][Weist] |
| [schofield_imaginary_stable](lean/KroneckerSchofieldNonemptiness.lean) | Existence of stable representations for positive dimensions satisfying $a^2+b^2-mab\leq0$. | [Schofield 1992][Sch92], [Schofield 2001][Sch01], [Reineke 2024][Rei] |

Full bibliographic details are in the [manuscript source](lean/manuscript/kronecker-entropy.tex).

## Compilation

### Lean

Install [Elan](https://github.com/leanprover/elan) and Git. Clone this repository and run the following commands from its root:

```bash
git clone https://github.com/so-okada/kronecker-euler-sources.git
cd kronecker-euler-sources
elan toolchain install leanprover/lean4:v4.35.0
lake exe cache get
lake build
```

[`lean-toolchain`](lean-toolchain) pins Lean 4.35.0. [`lakefile.lean`](lakefile.lean) pins Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. [`lake-manifest.json`](lake-manifest.json) locks the dependency revisions. The default build includes all 736 project modules.

To print the main theorem's axiom profiles after building:

```bash
lake env lean lean/KroneckerReadableMain.lean
```

The file contains `#print axioms KroneckerReadableMain.theorem_1_1` and the corresponding checks for the other main declarations.

### TeX

Install a TeX distribution containing the packages used in the manuscript and `latexmk`. From the repository root:

```bash
cd lean/manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error kronecker-entropy.tex
```

The output is `kronecker-entropy.pdf`. All section sources and required figure PDFs are included.

[B]: https://doi.org/10.1112/jlms.70642
[Dimca]: https://doi.org/10.1007/978-1-4612-4404-2
[King]: https://doi.org/10.1093/qmath/45.4.515
[KW]: https://arxiv.org/abs/alg-geom/9403014
[Rei08]: https://doi.org/10.4171/062-1/14
[Rei]: https://doi.org/10.5802/art.12
[RW]: https://arxiv.org/abs/1103.5283
[Sch92]: https://doi.org/10.1112/plms/s3-65.1.46
[Sch01]: https://arxiv.org/abs/math/9911014
[Weist]: https://doi.org/10.1090/S1088-4165-2013-00436-3

