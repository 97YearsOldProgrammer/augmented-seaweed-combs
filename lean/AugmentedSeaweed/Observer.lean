import Mathlib.Tactic
import AugmentedSeaweed.Basic

/-!
# Observer property: depth does not affect labels

Formalizes the key structural property that depth is a "pure observer":
the augmented comb's label dynamics are identical to the standard comb.

## Statement

For any strings A, B:
  d_col_augmented(A, B) = d_col_standard(A, B)
  d_row_augmented(A, B) = d_row_standard(A, B)

## Proof sketch

The depth values are never read during label comparison or swap decisions.
At each cell (r, c):
- The swap condition depends only on: a[r] == b[c] and d_col[c] vs d_row[r]
- Depth is updated AFTER the swap decision, based on which case occurred
- Therefore depth cannot influence the label trajectory

This is formalized as: the projection map
  π : (d_col, depth_col, d_row, depth_row) → (d_col, d_row)
commutes with the comb step function.
-/

/-- Cell state: the four values at a cell (column label, column depth,
    row label, row depth) -/
structure CellState where
  colLabel : ℕ
  colDepth : ℕ
  rowLabel : ℕ
  rowDepth : ℕ
  deriving DecidableEq, Repr

/-- Standard comb cell update (labels only) -/
def standardCellUpdate (isMatchCell : Bool) (colLabel rowLabel : ℕ) : ℕ × ℕ :=
  if isMatchCell then
    (rowLabel, colLabel)  -- swap on match
  else if colLabel > rowLabel then
    (rowLabel, colLabel)  -- swap on mismatch when col > row
  else
    (colLabel, rowLabel)  -- no swap

/-- Augmented comb cell update (labels + depths) -/
def augmentedCellUpdate (isMatchCell : Bool) (s : CellState) : CellState :=
  if isMatchCell then
    { colLabel := s.rowLabel, colDepth := 0,
      rowLabel := s.colLabel, rowDepth := 0 }
  else if s.colLabel > s.rowLabel then
    { colLabel := s.rowLabel, colDepth := s.rowDepth + 1,
      rowLabel := s.colLabel, rowDepth := s.colDepth + 1 }
  else
    { colLabel := s.colLabel, colDepth := s.colDepth + 1,
      rowLabel := s.rowLabel, rowDepth := s.rowDepth + 1 }

/-- **Observer property**: the label projection of the augmented update
    equals the standard update, regardless of depth values. -/
theorem observer_property (isMatchCell : Bool) (s : CellState) :
    let augResult := augmentedCellUpdate isMatchCell s
    let stdResult := standardCellUpdate isMatchCell s.colLabel s.rowLabel
    (augResult.colLabel, augResult.rowLabel) = stdResult := by
  simp [augmentedCellUpdate, standardCellUpdate]
  split
  · -- match case
    simp
  · -- mismatch case
    split
    · -- col > row: swap
      simp
    · -- col ≤ row: no swap
      simp

/-- Corollary: depth does not influence the swap decision -/
theorem depth_irrelevant (isMatchCell : Bool)
    (colLabel rowLabel : ℕ) (d1 d2 d3 d4 : ℕ) :
    let s1 : CellState := ⟨colLabel, d1, rowLabel, d2⟩
    let s2 : CellState := ⟨colLabel, d3, rowLabel, d4⟩
    let r1 := augmentedCellUpdate isMatchCell s1
    let r2 := augmentedCellUpdate isMatchCell s2
    (r1.colLabel, r1.rowLabel) = (r2.colLabel, r2.rowLabel) := by
  simp only [augmentedCellUpdate]
  split
  · simp
  · split <;> simp
