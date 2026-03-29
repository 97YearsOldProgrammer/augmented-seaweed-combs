# CLAUDE.md — Augmented Seaweed Combs

## What This Is

Research repo for the paper **"Semi-Local Affine Gap Scoring via Augmented Seaweed Combs"** (Gong Chen, UC Davis Genome Center). Contains the paper source, 20 Lean 4 formal proof files (304+ theorems), and Python experimental scripts.

**Core contribution:** Tiskin's semi-local string comparison framework requires sentinel blow-up (v^2 cost) for affine gap penalties. We resolve this by augmenting each seaweed wire with a gap depth counter, yielding the wreath product S_{m+n} wr Aff(Z>=0) at 2x storage instead of v x.

## Build Commands

```bash
# Lean proofs — type-check all 20 modules (pulls Mathlib automatically)
cd lean && lake build

# Paper — compile LaTeX
cd paper && pdflatex paper.tex && pdflatex paper.tex
# or: cd paper && tectonic paper.tex

# Python experiments — standalone, no dependencies beyond stdlib
python3 lean/depth_study_lib.py
```

## Project Layout

```
paper/                    LaTeX source + compiled PDF
  paper.tex               Main document (~55 KB)
  figures/                TikZ figures (krusche_comb, augmented_comb, blowup)
lean/                     Lean 4 formal proofs
  lakefile.lean           Lake config (package "flash-alignment", requires Mathlib)
  lean-toolchain          Lean v4.29.0-rc6
  AugmentedSeaweed.lean   Root import (20 modules)
  AugmentedSeaweed/       Individual proof files (see map below)
  depth_study_lib.py      Shared computation library (gotoh_dp, lcs_dp, augmented_comb)
  depth_study_q{1-4}.py   Research question scripts
  depth_study_phase1.py   Exhaustive enumeration (120K+ cases)
  depth_study_data.json   Cached verification data (34 MB)
  experiment_chain_as_lcs.py  Seed chaining as LIS/LCS
docs/
  depth-information-results.md  Research findings from exhaustive verification
```

## The Core Mathematical Chain

```
LCSS_k  <=  diag  <=  Gotoh  <=  LCS
(seeds)    (Hamming)  (affine)   (comb)
```

- **diag**: count matches at same offset (zero gaps)
- **Gotoh**: optimal affine-gap alignment (gaps penalized by go + k*ge)
- **LCS**: longest common subsequence (unlimited free gaps)
- **epsilon = LCS - diag**: how much extra unlimited gaps buy over zero gaps

**The correction formula** (fully proved):
- When epsilon <= go: Gotoh = diag exactly (gap benefit doesn't cover gap-open cost)
- When epsilon > go: Gotoh = LCS - correction(depth) (comb needed, Tier 3)

**Bridge lemmas:**
- `gotoh_ge_diag` (Bridge 1): diagonal path always feasible, so gaps can't hurt
- `gotoh_le_diag_when_eps_small` (Bridge 2): when epsilon <= go, H/E/F all <= diag
- `gotoh_HEF_le_lcs`: bounds each Gotoh component, E/F <= LCS - go <= diag when epsilon <= go

## Lean Proof Map (20 files, 304+ theorems)

### Core Algebra
| File | Paper Result | What's Proved |
|---|---|---|
| `Basic` | Section 2 | Core types: WireIdx, isMatch, DCol, DRow, DepthCol, DepthRow |
| `AffineMonoid` | Def 8 | Aff(Z>=0) monoid laws, composition, closure (a in {0,1}) |
| `TropicalCarry` | Background | Tropical carry monoid (T,K), 2x2 matrix isomorphism |
| `Observer` | Remark after Def 5 | Depth is pure observer: labels unchanged by augmentation |
| `WreathHomomorphism` | Thm 9 | Wreath product S_{m+n} wr Aff(Z>=0) composition rule |

### Composition and Structure
| File | Paper Result | What's Proved |
|---|---|---|
| `CombComposition` | Thm 3 | Comb fold structure, composition by List.foldl_append |
| `WreathComposition` | Thm 9 details | Full wreath product composition |
| `PathSeparation` | — | Score-path independence (separation theorem) |

### Scoring and Extraction
| File | Paper Result | What's Proved |
|---|---|---|
| `CorrectionFormula` | Three-tier model | score = diag when epsilon <= go |
| `CorrectionScore` | — | correction(LCS, diag, go) = max(LCS - go, diag) |
| `SplitScoring` | — | Split scoring for adaptive windows |
| `CombCorrectness` | — | Comb-output correctness |
| `CrossingCountLCS` | — | Comb -> LCS via crossing count (sorry-free) |
| `LCSExtraction` | — | Extracting LCS from comb output (d_col) |
| `LCDCorrectness` | — | Longest Common Diagonal correctness |

### Score Determination (Main Theorem)
| File | Paper Result | What's Proved |
|---|---|---|
| `ScoreDetermination` | Thm 1 | Augmented comb determines Gotoh DP exactly. Bridge lemmas, gotoh_HEF_le_lcs. All 12 helper sorrys closed. |

### Negative Results and Advanced
| File | Paper Result | What's Proved |
|---|---|---|
| `NonMonge` | Thm 6 | Affine gap score matrix NOT Monge (counterexample: A="01", B="0001") |
| `DepthExcess` | — | Depth-excess relationship analysis |
| `TropicalCollapse` | Prop | Monotone c_j -> trivial chain (WHY diag works at low epsilon) |
| `BandSufficiency` | Prop 12 | Optimal alignment deviation <= epsilon, banded DP exact |

## Working with Lean in This Repo

- **Mathlib dependency**: pulled from master via Lake. `lake build` on first run is slow (~30 min for Mathlib cache).
- **autoImplicit = false**: all variables must be explicitly declared.
- **Lean toolchain**: v4.29.0-rc6. Do not change without checking Mathlib compatibility.
- **Sorry status**: use `grep -r "^\s*sorry" lean/AugmentedSeaweed/` to check for open sorrys (comments mention sorry but actual tactic uses are what matter).
- **MCP tools available**: `lean_goal`, `lean_diagnostic_messages`, `lean_hover_info`, `lean_verify`, `lean_multi_attempt` — use these for proof development.
- **Search tools**: `lean_leansearch` (natural language), `lean_loogle` (type pattern), `lean_local_search` (local declarations).
- **After editing imports**: run `lean_build` to rebuild. Slow but necessary.

## Working with the Paper

- `paper/paper.tex` is the single source file (~55 KB)
- Figures are TikZ in `paper/figures/` (B&W only)
- Uses `algorithm2e` for pseudocode (Algorithms 1-4)
- Theorem/proposition numbering tracks closely with Lean file names

## Python Experiments

All scripts in `lean/` directory. `depth_study_lib.py` is the shared library providing:
- `gotoh_dp()`: global affine gap DP
- `lcs_dp()`: standard LCS via DP
- `augmented_comb()`: full augmented seaweed comb with depth tracking
- `lcs_from_dcol()`: LCS extraction from distance column

These are research exploration tools, not production code. No requirements.txt needed — stdlib only.

## Git Conventions

- **Commit format**: `type(phase-version): description`
  - Types: feat, fix, refactor, docs, test, chore
  - Phases: numbered (01, 02, 02.2, 02.3, etc.) tracking proof progress
- **Single branch**: `main` (linear history)
- **Package name**: still "flash-alignment" in lakefile.lean (historical, renamed to AugmentedSeaweed in code)

## Current Status

- Paper: complete draft with 304+ theorem count documented
- Lean: 20 modules, 304+ theorems, ScoreDetermination and CrossingCountLCS sorry-free
- Active work: uncommitted changes in CrossingCountLCS.lean (+642 lines) and ScoreDetermination.lean (+615 lines) — closing remaining infrastructure
- Next frontiers: any remaining sorry closure, potential Tier 3 (epsilon > go) refinements
