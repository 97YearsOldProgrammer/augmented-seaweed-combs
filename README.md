# Semi-Local Affine Gap Scoring via Augmented Seaweed Combs

Companion repository for the paper:

> **Semi-Local Affine Gap Scoring via Augmented Seaweed Combs**
> Gong Chen (UC Davis Genome Center)

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

## Lean 4 Formal Proofs

The `lean/` directory contains machine-checked proofs of the key algebraic
properties. To verify:

```bash
cd lean
lake build
```

Requires Lean 4 and Mathlib (pulled automatically by `lake`).

### Proof-to-paper mapping

| Lean file | Paper result | What is verified |
|---|---|---|
| `AffineMonoid.lean` | Definition 8 (Affine monoid) | Monoid laws, composition formula, closure a in {0,1} |
| `Observer.lean` | Remark after Definition 5 | Depth is a pure observer: labels unchanged by augmentation |
| `WreathHomomorphism.lean` | Theorem 9 (Wreath product) | Composition follows the wreath product rule |
| `TropicalCarry.lean` | (Background) | Tropical carry monoid, 2x2 matrix isomorphism |
| `BandSufficiency.lean` | Proposition 12 (Band sufficiency) | Optimal alignment deviation <= epsilon, banded DP exact |
| `Basic.lean` | Section 2 (Preliminaries) | Core types: distance columns, match predicates |

## Repository structure

```
paper/           LaTeX source for the paper
  paper.tex      Main document
  paper.pdf      Compiled PDF
  figures/       TikZ figures (B&W)
lean/            Lean 4 formal proofs
  lakefile.lean  Build configuration (pulls Mathlib)
  FlashAlignment/
    *.lean       Individual proof files
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
