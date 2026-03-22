import Mathlib.Tactic
import AugmentedSeaweed.Basic
import AugmentedSeaweed.Observer

/-!
# Score-Path Separation Theorem

The composition boundary (d_col, depth_col) of the augmented Krusche comb
is a sufficient statistic for affine gap **scores** but NOT for
**alignment paths** (Gotoh DP state vectors H, E, F).

## Main results

- `boundary_eq`: two specific inputs produce identical (d_col, depth_col)
- `dp_state_ne`: the same inputs produce distinct Gotoh DP final rows
- `score_path_separation`: composition boundary does not determine DP state
-/

/-! ## Gotoh DP (List-based, fully computable) -/

/-- Final row of the Gotoh DP: H, E, F vectors at the last row. -/
structure GotohRow where
  h : List ℤ
  e : List ℤ
  f : List ℤ
  deriving DecidableEq, Repr

/-- Sentinel for negative infinity in Gotoh DP. -/
def NEG_INF : ℤ := -999999

/-- Initialize row 0 of the Gotoh DP.
    H[0][j] = 0, E[0][j] = NEG_INF, F[0][j] = NEG_INF for all j. -/
def gotohInitRow (n : ℕ) : GotohRow :=
  { h := List.replicate (n + 1) 0
    e := List.replicate (n + 1) NEG_INF
    f := List.replicate (n + 1) NEG_INF }

/-- Process one row of Gotoh DP, building H[i][*], E[i][*], F[i][*].
    Takes the previous row, the query character a[i-1], the reference b,
    and gap penalties (go, ge). Row index i (1-based) for initialization. -/
def gotohProcessRow (prev : GotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ) (i : ℕ)
    : GotohRow :=
  let n := b.length
  -- H[i][0] = -(go + ge * (i - 1)), E[i][0] = H[i][0], F[i][0] = NEG_INF
  let h0 : ℤ := -(go + ge * ((i : ℤ) - 1))
  let e0 : ℤ := h0
  let f0 : ℤ := NEG_INF
  -- Process columns 1..n, accumulating lists in reverse
  let init : List ℤ × List ℤ × List ℤ := ([h0], [e0], [f0])
  let result := (List.range n).foldl (fun (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) =>
    let j := jIdx + 1  -- 1-based column index
    let bChar := b.getD jIdx 0
    -- Previous row values
    let h_prev_j := prev.h.getD j 0
    let h_prev_j1 := prev.h.getD (j - 1) 0
    -- Current row values at j-1
    let h_curr_j1 := acc.1.head!
    let f_curr_j1 := acc.2.2.head!
    -- Diagonal score: H[i-1][j-1] + match(a[i-1], b[j-1])
    let matchScore : ℤ := if ai == bChar then 1 else 0
    let diag := h_prev_j1 + matchScore
    -- E[i][j] = max(H[i-1][j] - go, E[i-1][j] - ge)
    let e_prev_j := prev.e.getD j NEG_INF
    let eij := max (h_prev_j - go) (e_prev_j - ge)
    -- F[i][j] = max(H[i][j-1] - go, F[i][j-1] - ge)
    let fij := max (h_curr_j1 - go) (f_curr_j1 - ge)
    -- H[i][j] = max(diag, E[i][j], F[i][j])
    let hij := max diag (max eij fij)
    (hij :: acc.1, eij :: acc.2.1, fij :: acc.2.2)
  ) init
  { h := result.1.reverse
    e := result.2.1.reverse
    f := result.2.2.reverse }

/-- Compute the Gotoh DP final row for query a, reference b, gap-open go, gap-extend ge. -/
def gotohFinalRow (a : List ℕ) (b : List ℕ) (go ge : ℤ) : GotohRow :=
  let m := a.length
  let initRow := gotohInitRow b.length
  (List.range m).foldl (fun (prevRow : GotohRow) (iIdx : ℕ) =>
    let ai := a.getD iIdx 0
    gotohProcessRow prevRow ai b go ge (iIdx + 1)
  ) initRow

/-! ## Augmented Comb (List-based, reuses augmentedCellUpdate from Observer.lean) -/

/-- Output of the augmented comb: boundary vectors as Lists. -/
structure AugCombOutput where
  d_col : List ℕ
  depth_col : List ℕ
  d_row : List ℕ
  depth_row : List ℕ
  deriving DecidableEq, Repr

/-- Boundary projection: extract only (d_col, depth_col). -/
structure Boundary where
  d_col : List ℕ
  depth_col : List ℕ
  deriving DecidableEq, Repr

/-- Project the augmented comb output to the composition boundary. -/
def boundaryProj (out : AugCombOutput) : Boundary :=
  { d_col := out.d_col, depth_col := out.depth_col }

/-- Process one cell of the augmented comb, updating column and row arrays.
    Mutates d_col, depth_col at index c and d_row, depth_row at index r. -/
def processCell (d_col : List ℕ) (depth_col : List ℕ)
    (d_row : List ℕ) (depth_row : List ℕ)
    (r c : ℕ) (isMatch : Bool)
    : List ℕ × List ℕ × List ℕ × List ℕ :=
  let state : CellState :=
    { colLabel := d_col.getD c 0
      colDepth := depth_col.getD c 0
      rowLabel := d_row.getD r 0
      rowDepth := depth_row.getD r 0 }
  let newState := augmentedCellUpdate isMatch state
  ( d_col.set c newState.colLabel
  , depth_col.set c newState.colDepth
  , d_row.set r newState.rowLabel
  , depth_row.set r newState.rowDepth )

/-- Process one row of the augmented comb: iterate over all columns. -/
def processCombRow (a : List ℕ) (b : List ℕ) (r : ℕ)
    (d_col : List ℕ) (depth_col : List ℕ)
    (d_row : List ℕ) (depth_row : List ℕ)
    : List ℕ × List ℕ × List ℕ × List ℕ :=
  let n := b.length
  let ar := a.getD r 0
  (List.range n).foldl (fun (acc : List ℕ × List ℕ × List ℕ × List ℕ) (c : ℕ) =>
    let bc := b.getD c 0
    let isMatch := (ar == bc)
    processCell acc.1 acc.2.1 acc.2.2.1 acc.2.2.2 r c isMatch
  ) (d_col, depth_col, d_row, depth_row)

/-- Compute the augmented comb for query a (length m) and reference b (length n).
    Initialization: d_col = [0,...,0], depth_col = [0,...,0],
                    d_row = [1,2,...,m], depth_row = [0,...,0].
    Processes cells row-major using `augmentedCellUpdate`. -/
def augmentedComb (a : List ℕ) (b : List ℕ) : AugCombOutput :=
  let m := a.length
  let n := b.length
  let d_col_init := List.replicate n 0
  let depth_col_init := List.replicate n 0
  let d_row_init := (List.range m).map (· + 1)
  let depth_row_init := List.replicate m 0
  let result := (List.range m).foldl (fun (acc : List ℕ × List ℕ × List ℕ × List ℕ) (r : ℕ) =>
    processCombRow a b r acc.1 acc.2.1 acc.2.2.1 acc.2.2.2
  ) (d_col_init, depth_col_init, d_row_init, depth_row_init)
  { d_col := result.1
    depth_col := result.2.1
    d_row := result.2.2.1
    depth_row := result.2.2.2 }

/-! ## Counterexample inputs -/

/-- First query: [0, 0, 1, 0] -/
def a₁ : List ℕ := [0, 0, 1, 0]

/-- First reference: [1, 0, 1, 0, 0] -/
def b₁ : List ℕ := [1, 0, 1, 0, 0]

/-- Second query: [0, 1, 1, 0] -/
def a₂ : List ℕ := [0, 1, 1, 0]

/-- Second reference: [1, 0, 1, 0, 0] -/
def b₂ : List ℕ := [1, 0, 1, 0, 0]

/-- Gap-open penalty for the counterexample. -/
def go_ex : ℤ := 1

/-- Gap-extend penalty for the counterexample. -/
def ge_ex : ℤ := 1

/-! ## Theorems -/

/-- The two input pairs produce identical composition boundaries (d_col, depth_col). -/
theorem boundary_eq :
    boundaryProj (augmentedComb a₁ b₁) = boundaryProj (augmentedComb a₂ b₂) := by
  native_decide

/-- The two input pairs produce distinct Gotoh DP final rows. -/
theorem dp_state_ne :
    gotohFinalRow a₁ b₁ go_ex ge_ex ≠ gotohFinalRow a₂ b₂ go_ex ge_ex := by
  native_decide

/-- **Score-Path Separation Theorem**: the composition boundary (d_col, depth_col)
    of the augmented Krusche comb does not determine the Gotoh DP state.

    There exist inputs where the boundary is identical but the DP final
    row (H, E, F) differs. Thus the boundary is a sufficient statistic
    for scores but not for alignment paths. -/
theorem score_path_separation :
    ∃ (qa qb ra rb : List ℕ) (go ge : ℤ),
      boundaryProj (augmentedComb qa ra) = boundaryProj (augmentedComb qb rb) ∧
      gotohFinalRow qa ra go ge ≠ gotohFinalRow qb rb go ge :=
  ⟨a₁, a₂, b₁, b₂, go_ex, ge_ex, boundary_eq, dp_state_ne⟩
