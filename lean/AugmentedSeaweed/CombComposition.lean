/-
  FlashAlignment/CombComposition.lean

  Composition at the comb level: the Krusche comb is a fold over query
  characters, so processing A1 then A2 gives the same result as A1·A2.

  Main results:
  - comb_composition: fold-split via List.foldl_append
  - boundary_sufficiency: d_col is a Markov boundary (future independent of past given d_col)
  - augmented_comb_composition: same for the augmented comb (d_col, depth_col)

  This connects the algebraic wreath product (WreathComposition.lean)
  to the actual comb computation: the comb produces composable outputs
  because it IS a fold, and folds split by List.foldl_append.

  Paper reference: Theorem 3 (Composition complexity)
-/
import Mathlib.Tactic
import AugmentedSeaweed.Basic

/-! ## Column Step -/

/-- Process one cell of the standard comb.
    Returns (new d_col value, new d_row value). -/
def colStep (qChar bChar d_col d_row : ℕ) : ℕ × ℕ :=
  if qChar == bChar then (d_row, d_col + 1)
  else if d_col > d_row then (d_row, d_col + 1)
  else (d_col, d_row + 1)

/-! ## Row Processing -/

/-- Column fold accumulator: (d_col list, current d_row value) -/
abbrev ColAcc := List ℕ × ℕ

/-- Process one column within a row. -/
def colFoldStep (qChar : ℕ) (b : List ℕ) (acc : ColAcc) (c : ℕ) : ColAcc :=
  let dc := acc.1.getD c 0
  let bc := b.getD c 0
  let (dc', dr') := colStep qChar bc dc acc.2
  (acc.1.set c dc', dr')

/-- Process one row: fold colFoldStep over columns.
    d_row is local — starts at d_row_init, does not persist across rows. -/
def processRow (qChar : ℕ) (b : List ℕ) (d_col : List ℕ) (d_row_init : ℕ)
    : List ℕ :=
  ((List.range b.length).foldl (colFoldStep qChar b) (d_col, d_row_init)).1

/-! ## Comb as Fold over Rows -/

/-- Row fold accumulator: (d_col, row offset).
    The offset tracks how many rows have been processed;
    d_row for the next row starts at offset + 1. -/
abbrev RowAcc := List ℕ × ℕ

/-- One step of the row fold: process one row and increment offset. -/
def rowFoldStep (b : List ℕ) (acc : RowAcc) (qChar : ℕ) : RowAcc :=
  (processRow qChar b acc.1 (acc.2 + 1), acc.2 + 1)

/-- Full comb as a fold over query characters.
    The accumulator carries (d_col, offset) where offset counts rows processed. -/
def combFold (a : List ℕ) (b : List ℕ) (init : RowAcc) : RowAcc :=
  a.foldl (rowFoldStep b) init

/-- Standard comb initialization: d_col = 0, offset = 0. -/
def combInit (n : ℕ) : RowAcc := (List.replicate n 0, 0)

/-- Compute the d_col for query a against reference b. -/
def combDcol (a : List ℕ) (b : List ℕ) : List ℕ :=
  (combFold a b (combInit b.length)).1

/-! ## The Composition Theorem -/

/-- **Composition Theorem**: the comb for A1·A2 equals running A1 then
    continuing with A2 from A1's final state.

    Proof: the comb is a `List.foldl`, and `List.foldl_append` says
    foldl over a concatenation = fold first part then continue.

    This is the mechanistic content of the paper's Theorem 3:
    the d_col at the boundary is the only transfer. -/
theorem comb_composition (a1 a2 : List ℕ) (b : List ℕ) (init : RowAcc) :
    combFold (a1 ++ a2) b init =
    combFold a2 b (combFold a1 b init) := by
  simp only [combFold, List.foldl_append]

/-- Corollary: d_col for A1·A2 = d_col from continuing A2 after A1. -/
theorem combDcol_composition (a1 a2 : List ℕ) (b : List ℕ) :
    combDcol (a1 ++ a2) b =
    (combFold a2 b (combFold a1 b (combInit b.length))).1 := by
  simp only [combDcol, comb_composition]

/-- The d_col depends on A1 only through the intermediate state.
    If two prefixes produce the same state, their continuations are identical. -/
theorem boundary_sufficiency (a2 : List ℕ) (b : List ℕ) (s₁ s₂ : RowAcc)
    (h : s₁ = s₂) :
    combFold a2 b s₁ = combFold a2 b s₂ := by
  rw [h]

/-! ## Character-by-Character Composition

The comb for a string of length m decomposes into m single-character combs,
composed sequentially. This is the "LCD as composition basis" property. -/

/-- The comb for [c] (single character) starting from state init. -/
def lcdComb (c : ℕ) (b : List ℕ) (init : RowAcc) : RowAcc :=
  combFold [c] b init

/-- A string decomposes character by character:
    comb(ch :: rest) = comb(rest) ∘ comb([ch]).
    Immediate from the fold structure. -/
theorem comb_cons (ch : ℕ) (rest : List ℕ) (b : List ℕ) (init : RowAcc) :
    combFold (ch :: rest) b init =
    combFold rest b (combFold [ch] b init) := by
  simp only [combFold, List.foldl]

/-- Empty query produces identity (no change to state). -/
theorem comb_nil (b : List ℕ) (init : RowAcc) :
    combFold [] b init = init := by
  simp [combFold]

/-! ## Augmented Comb Composition -/

/-- Augmented column step: processes labels AND depths. -/
def augColStep (qChar bChar : ℕ) (dc dr dc_depth dr_depth : ℕ) :
    ℕ × ℕ × ℕ × ℕ :=
  if qChar == bChar then
    (dr, dc + 1, 0, 0)  -- match: swap labels, reset depths
  else if dc > dr then
    (dr, dc + 1, dr_depth + 1, dc_depth + 1)  -- mismatch-swap: depths follow + increment
  else
    (dc, dr + 1, dc_depth + 1, dr_depth + 1)  -- mismatch-keep: depths increment in place

/-- Augmented row fold accumulator: (d_col, depth_col, d_row, depth_row, offset) -/
abbrev AugRowAcc := List ℕ × List ℕ × ℕ × ℕ × ℕ

/-- Process one row of the augmented comb.
    Returns (new d_col, new depth_col, final d_row, final depth_row). -/
def processAugRow (qChar : ℕ) (b : List ℕ) (d_col depth_col : List ℕ)
    (dr_init dep_init : ℕ) : List ℕ × List ℕ × ℕ × ℕ :=
  let init : List ℕ × List ℕ × ℕ × ℕ := (d_col, depth_col, dr_init, dep_init)
  (List.range b.length).foldl (fun (acc : List ℕ × List ℕ × ℕ × ℕ) c =>
    let dc := acc.1.getD c 0
    let bc := b.getD c 0
    let dc_dep := acc.2.1.getD c 0
    let (dc', dr', dc_dep', dr_dep') := augColStep qChar bc dc acc.2.2.1 dc_dep acc.2.2.2
    (acc.1.set c dc', acc.2.1.set c dc_dep', dr', dr_dep')
  ) init

/-- Augmented comb fold accumulator: (d_col, depth_col, offset) -/
abbrev AugAcc := List ℕ × List ℕ × ℕ

/-- One step of the augmented comb fold. -/
def augFoldStep (b : List ℕ) (acc : AugAcc) (qChar : ℕ) : AugAcc :=
  let (d_col', depth_col', _, _) :=
    processAugRow qChar b acc.1 acc.2.1 (acc.2.2 + 1) 0
  (d_col', depth_col', acc.2.2 + 1)

/-- Full augmented comb as a fold. -/
def augCombFold (a : List ℕ) (b : List ℕ) (init : AugAcc) : AugAcc :=
  a.foldl (augFoldStep b) init

/-- Augmented comb initialization. -/
def augCombInit (n : ℕ) : AugAcc :=
  (List.replicate n 0, List.replicate n 0, 0)

/-- **Augmented Composition**: same fold-split property as standard comb,
    but transferring (d_col, depth_col) at the boundary. -/
theorem aug_comb_composition (a1 a2 : List ℕ) (b : List ℕ) (init : AugAcc) :
    augCombFold (a1 ++ a2) b init =
    augCombFold a2 b (augCombFold a1 b init) := by
  simp only [augCombFold, List.foldl_append]

/-! ## Summary

The composition theorems establish:

1. The comb is a fold over query characters → fold-split gives composition for free
2. The boundary state (d_col for standard, (d_col, depth_col) for augmented) is
   the ONLY information that transfers
3. d_row is local to each row — it starts deterministically at offset + 1

Combined with the wreath product structure (WreathComposition.lean), this shows
that the comb produces elements of S_{m+n} ≀ Aff(Z≥0) that compose correctly.
The comb IS the homomorphism Φ: Σ* → S_{m+n} ≀ Aff(Z≥0).
-/
