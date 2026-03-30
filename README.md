# Augmented Semi-Local String Comparison: Algorithms and Applications

Companion repository for the paper:

> **Augmented Semi-Local String Comparison: Algorithms and Applications**
> Gong Chen, UC Davis Genome Center

**Paper:** [`paper/paper.pdf`](paper/paper.pdf)

## Summary

Tiskin's semi-local string comparison framework encodes all LCS scores
via composable permutations. Gap-penalized scoring requires the sentinel
blow-up at a nu^2 cost in string length. We resolve the affine gap
scoring problem by introducing the **augmented seaweed comb**: each wire
carries a gap depth counter that resets on match and increments on
mismatch. The augmented output determines the complete Gotoh DP state
with zero ambiguity.

**Key results:**
- The algebraic structure is the wreath product S\_{m+n} wr Aff(Z>=0)
- Composition retains O(n log n) complexity
- Exact bijection with the sentinel blow-up at 2x vs nu x storage
- The semi-local affine gap score matrix is not Monge, confirming the wreath product is necessary

## Lean 4 Formal Proofs (304+ theorems)

The `lean/` directory contains machine-checked proofs across 22 modules. To verify:

```bash
cd lean
lake build
```

Requires Lean 4 (v4.29.0-rc6) and Mathlib (pulled automatically by `lake`).

### Proof-to-paper mapping

#### Core Algebra
| Lean file | Paper result | What is verified |
|---|---|---|
| `Basic.lean` | Section 2 | Core types: WireIdx, isMatch, DCol, DRow, DepthCol, DepthRow |
| `AffineMonoid.lean` | Definition 8 | Aff(Z>=0) monoid laws, composition, closure (a in {0,1}) |
| `TropicalCarry.lean` | Background | Tropical carry monoid, 2x2 matrix isomorphism |
| `Observer.lean` | Remark after Def 5 | Depth is pure observer: labels unchanged by augmentation |
| `WreathHomomorphism.lean` | Theorem 9 | Wreath product S\_{m+n} wr Aff(Z>=0) composition rule |

#### Composition and Structure
| Lean file | Paper result | What is verified |
|---|---|---|
| `CombComposition.lean` | Theorem 3 | Comb fold structure, composition by List.foldl\_append |
| `WreathComposition.lean` | Theorem 9 details | Full wreath product composition |
| `PathSeparation.lean` | -- | Score-path independence (separation theorem) |

#### Scoring and Extraction
| Lean file | Paper result | What is verified |
|---|---|---|
| `CorrectionFormula.lean` | Three-tier model | score = diag when epsilon <= go |
| `CorrectionScore.lean` | -- | correction(LCS, diag, go) = max(LCS - go, diag) |
| `SplitScoring.lean` | -- | Split scoring for adaptive windows |
| `CombCorrectness.lean` | -- | Comb-output correctness |
| `CrossingCountLCS.lean` | -- | Comb -> LCS via crossing count (sorry-free) |
| `LCSExtraction.lean` | -- | LCS extraction from comb output (d\_col) |
| `LCDCorrectness.lean` | -- | Longest Common Diagonal correctness |

#### Score Determination (Main Theorem)
| Lean file | Paper result | What is verified |
|---|---|---|
| `ScoreDetermination.lean` | Theorem 1 | Augmented comb determines Gotoh DP exactly (sorry-free) |
| `DepthDetermination.lean` | -- | Bridge lemmas, gotoh\_HEF\_le\_lcs |

#### Anchor Framework
| Lean file | Paper result | What is verified |
|---|---|---|
| `AnchorDecomposition.lean` | Specs 01, 03 | charfreq <= LCS, epsilon <= offDiagMatchable (sorry-free) |
| `AdditivityBound.lean` | Specs 02, 06 | LCS super-additive, epsilon >= 0, BA tier 3 detector (sorry-free) |
| `AnchorSoundness.lean` | Spec 04 | Anchor soundness infrastructure |

#### Negative Results
| Lean file | Paper result | What is verified |
|---|---|---|
| `NonMonge.lean` | Theorem 6 | Affine gap score matrix NOT Monge (counterexample) |
| `DepthExcess.lean` | -- | Depth-excess relationship analysis |
| `TropicalCollapse.lean` | Proposition | Monotone c\_j -> trivial chain (why diag works at low epsilon) |
| `BandSufficiency.lean` | Proposition 12 | Optimal alignment deviation <= epsilon, banded DP exact |

## Repository structure

```
paper/           LaTeX source for the paper
  paper.tex      Main document
  paper.pdf      Compiled PDF
  figures/       TikZ figures (B&W)
lean/            Lean 4 formal proofs
  lakefile.lean  Build configuration (pulls Mathlib)
  AugmentedSeaweed/
    *.lean       22 proof modules (304+ theorems)
```

## Building the paper

```bash
cd paper
pdflatex paper.tex && pdflatex paper.tex
```

Or with [tectonic](https://tectonic-typesetting.github.io/):
```bash
cd paper
tectonic paper.tex
```

## License

MIT
