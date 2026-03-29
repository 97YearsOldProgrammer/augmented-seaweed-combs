/-
  AugmentedSeaweed/DepthDetermination.lean

  Depth-Based Score Determination (Tier 3 Enhancement)

  When epsilon > go (Tier 3), the correction formula falls back to Gotoh DP.
  The depth column from the augmented comb can determine the exact Gotoh score
  WITHOUT DP in a characterizable regime:

    For equal-length sequences where lcsPathGotohScore >= 0:
      gotohStdGlobal = lcsPathGotohScore

  Main results:
  - gotohStdGlobal: standard global Gotoh DP (gap of k costs go + k*ge)
  - lcsPathGotohScore: Gotoh score of the LCS alignment path
  - gotoh_ge_lcs_path_score: Gotoh >= LCS path score (lower bound)
  - gotoh_eq_lcs_path_when_nonneg: equality for equal-length + non-negative

  Empirical basis: exhaustive verification on 120,150 cases
    (|a| <= 4, |b| <= 5, alphabet {0,1,2}, go in {1,2,3}, ge = 1)

  SORRY STATUS (3 remaining — 2026-03-29):
  - gotoh_ge_lcs_path_score: sorry (lower bound, needs path tracing argument)
  - gotoh_eq_lcs_path_when_nonneg: sorry (equal-length exactness)
  - stdGotoh_combined_gap init row case: sorry (init row horizontal gap, tedious List.getD)
  All main results verified by native_decide on small cases.
  PROVED: stdGotohAfterK_eq_gotohStdGlobal, full fold infrastructure,
    gap propagation (vertical/horizontal/combined), E propagation, match step.
  INFRASTRUCTURE for closing gotoh_ge_lcs_path_score:
    - stdGotoh_vertical_gap: H[i+d][j] >= H[i][j] - stdGapCost(d)
    - stdGotoh_horizontal_gap_succ: H[k+1][j+d] >= H[k+1][j] - stdGapCost(d)
    - stdGotoh_combined_gap: H[r+dr][c+dc] >= H[r][c] - stdGapCost(dr) - stdGapCost(dc)
    - stdGotoh_match_step: H[i+1][j+1] >= H[i][j] + match(a[i], b[j])
    Next: prove gotoh_ge_lcs_path_score via path tracing (induction on lcsTraceback).
-/
import Mathlib.Tactic
import AugmentedSeaweed.ScoreDetermination

/-! ## Standard Global Gotoh DP Infrastructure

The standard convention: gap of length k costs go + k * ge.
- Opening: H[i-1][j] - go - ge
- Extending: E[i-1][j] - ge
- Initialization: H[0][j] = -(go + j*ge), H[i][0] = -(go + i*ge)

This matches the Python depth_study_lib.py convention.
Differs from the semi-global gotohGlobalScore in PathSeparation.lean. -/

/-- Sentinel for negative infinity in standard Gotoh DP. -/
private def NEG_INF_STD : ℤ := -(10^9)

/-- Row state for the standard global Gotoh DP. -/
structure StdGotohRow where
  h : List ℤ
  e : List ℤ
  f : List ℤ
  deriving DecidableEq, Repr

/-- Initialize row 0 of standard global Gotoh DP.
    H[0][0] = 0, H[0][j] = -(go + j*ge) for j > 0.
    E[0][j] = NEG_INF, F[0][j] = NEG_INF. -/
def stdGotohInitRow (n : ℕ) (go ge : ℤ) : StdGotohRow :=
  { h := (List.range (n + 1)).map fun j =>
      if j = 0 then (0 : ℤ) else -(go + (j : ℤ) * ge)
    e := List.replicate (n + 1) NEG_INF_STD
    f := List.replicate (n + 1) NEG_INF_STD }

/-- Process one row of the standard global Gotoh DP.
    Takes previous row, query char, reference, penalties, row index (1-based).
    Builds lists by prepending then reversing. -/
def stdGotohProcessRow (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (i : ℕ) : StdGotohRow :=
  let n := b.length
  let h0 : ℤ := -(go + (i : ℤ) * ge)
  let e0 : ℤ := h0
  let f0 : ℤ := NEG_INF_STD
  let init : List ℤ × List ℤ × List ℤ := ([h0], [e0], [f0])
  let result := (List.range n).foldl (fun (acc : List ℤ × List ℤ × List ℤ) jIdx =>
    let j := jIdx + 1
    let bChar := b.getD jIdx 0
    let matchScore : ℤ := if ai == bChar then 1 else 0
    let diag := prev.h.getD (j - 1) 0 + matchScore
    let eij := max (prev.h.getD j 0 - go - ge) (prev.e.getD j NEG_INF_STD - ge)
    let fij := max (acc.1.head! - go - ge) (acc.2.2.head! - ge)
    let hij := max diag (max eij fij)
    (hij :: acc.1, eij :: acc.2.1, fij :: acc.2.2)
  ) init
  { h := result.1.reverse
    e := result.2.1.reverse
    f := result.2.2.reverse }

/-- Standard global Gotoh DP score H[m][n].
    Defined via stdGotohProcessRow fold for proof compatibility.
    Verified against Python by native_decide. -/
def gotohStdGlobal (a b : List ℕ) (go ge : ℤ) : ℤ :=
  let finalRow := (List.range a.length).foldl
    (fun (prev : StdGotohRow) iIdx =>
      stdGotohProcessRow prev (a.getD iIdx 0) b go ge (iIdx + 1)
    ) (stdGotohInitRow b.length go ge)
  finalRow.h.getD b.length 0

/-- Standard Gotoh DP after processing k rows (recursive, for induction). -/
def stdGotohAfterK (a b : List ℕ) (go ge : ℤ) : ℕ → StdGotohRow
  | 0 => stdGotohInitRow b.length go ge
  | k + 1 => stdGotohProcessRow (stdGotohAfterK a b go ge k) (a.getD k 0) b go ge (k + 1)

/-- stdGotohAfterK at full length computes gotohStdGlobal. -/
theorem stdGotohAfterK_eq_gotohStdGlobal (a b : List ℕ) (go ge : ℤ) :
    (stdGotohAfterK a b go ge a.length).h.getD b.length 0 =
    gotohStdGlobal a b go ge := by
  unfold gotohStdGlobal
  have key : ∀ k : ℕ, k ≤ a.length →
      (List.range k).foldl (fun prevRow iIdx =>
        stdGotohProcessRow prevRow (a.getD iIdx 0) b go ge (iIdx + 1)
      ) (stdGotohInitRow b.length go ge) = stdGotohAfterK a b go ge k := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [stdGotohAfterK]
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih (Nat.le_of_succ_le hn)]
      rfl
  rw [key a.length le_rfl]

/-! ## LCS DP Table and Traceback -/

/-- Full LCS DP table: table[i][j] = LCS(a[0..i), b[0..j)). -/
def lcsDPTable (a b : List ℕ) : List (List ℕ) :=
  let n := b.length
  let init := List.replicate (n + 1) 0
  a.foldl (fun (rows : List (List ℕ)) ai =>
    let prev := rows.getLast!
    let curr := (List.range n).foldl (fun (curr : List ℕ) j =>
      let bj := b.getD j 0
      let val :=
        if ai == bj then prev.getD j 0 + 1
        else max (prev.getD (j + 1) 0) (curr.getD j 0)
      curr ++ [val]
    ) [0]
    rows ++ [curr]
  ) [init]

/-- LCS traceback with fuel-based termination. -/
private def lcsTracebackGo (a b : List ℕ) (table : List (List ℕ))
    : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _, _ => []
  | _, 0, _ => []
  | _, _, 0 => []
  | fuel + 1, i + 1, j + 1 =>
    let ai := a.getD i 0
    let bj := b.getD j 0
    let dpij := (table.getD (i + 1) []).getD (j + 1) 0
    let dpDiag := (table.getD i []).getD j 0
    if ai == bj && dpij == dpDiag + 1 then
      lcsTracebackGo a b table fuel i j ++ [(i, j)]
    else if (table.getD i []).getD (j + 1) 0 ≥ (table.getD (i + 1) []).getD j 0 then
      lcsTracebackGo a b table fuel i (j + 1)
    else
      lcsTracebackGo a b table fuel (i + 1) j

/-- Extract one LCS alignment path. Returns sorted (i, j) match positions. -/
def lcsTraceback (a b : List ℕ) : List (ℕ × ℕ) :=
  lcsTracebackGo a b (lcsDPTable a b) (a.length + b.length) a.length b.length

/-! ## Gap Penalty Computation -/

/-- Gap cost for a run of length k: 0 if k=0, else go + k*ge. -/
def stdGapCost (k : ℕ) (go ge : ℤ) : ℤ :=
  if k = 0 then 0 else go + (k : ℤ) * ge

/-- Total gap penalty for an alignment path under standard convention.
    Accounts for head, inter-match, and tail gaps. -/
def pathGapPenalty (path : List (ℕ × ℕ)) (m n : ℕ) (go ge : ℤ) : ℤ :=
  match path with
  | [] => stdGapCost m go ge + stdGapCost n go ge
  | first :: _ =>
    let last := path.getLast!
    let headPenalty := stdGapCost first.1 go ge + stdGapCost first.2 go ge
    let tailPenalty := stdGapCost (m - 1 - last.1) go ge + stdGapCost (n - 1 - last.2) go ge
    let interPenalty := (List.range (path.length - 1)).foldl (fun acc k =>
      let p1 := path.getD k (0, 0)
      let p2 := path.getD (k + 1) (0, 0)
      acc + stdGapCost (p2.1 - p1.1 - 1) go ge + stdGapCost (p2.2 - p1.2 - 1) go ge
    ) (0 : ℤ)
    headPenalty + interPenalty + tailPenalty

/-- Gotoh score of the LCS alignment path = matches - gap penalty. -/
def lcsPathGotohScore (a b : List ℕ) (go ge : ℤ) : ℤ :=
  let path := lcsTraceback a b
  (path.length : ℤ) - pathGapPenalty path a.length b.length go ge

/-! ## Concrete Verification -/

theorem traceback_test1 : (lcsTraceback [0,1,0,1] [1,0,1,0]).length = 3 := by native_decide
theorem traceback_test2 : (lcsTraceback [0,1,0] [0,1,0]).length = 3 := by native_decide
theorem traceback_test3 : (lcsTraceback [0,0,0] [1,1,1]).length = 0 := by native_decide
theorem traceback_eq_lcs :
    (lcsTraceback [0,1,0,1] [1,0,1,0]).length = lcsDP [0,1,0,1] [1,0,1,0] := by native_decide

theorem std_gotoh_test1 : gotohStdGlobal [0,1,0] [0,1,0] 2 1 = 3 := by native_decide
theorem std_gotoh_test2 : gotohStdGlobal [0,0,0] [1,1,1] 1 1 = 0 := by native_decide
theorem std_gotoh_test3 : gotohStdGlobal [0,1,0,1] [1,0,1,0] 1 1 = 0 := by native_decide
theorem std_gotoh_test4 : gotohStdGlobal [0,0,0,1] [1,0,0,0] 1 1 = 2 := by native_decide
theorem std_gotoh_test5 : gotohStdGlobal [0,1,2,0] [0,2,1,0] 2 1 = 2 := by native_decide

theorem lcs_path_test1 : lcsPathGotohScore [0,1,0] [0,1,0] 2 1 = 3 := by native_decide
theorem lcs_path_test2 : lcsPathGotohScore [0,1,0,1] [1,0,1,0] 1 1 = -1 := by native_decide

-- Semi-global ≠ standard global for equal-length (important convention check)
theorem conventions_differ :
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 1 1 ≠ gotohStdGlobal [0,1,0,1] [1,0,1,0] 1 1 := by
  native_decide

-- stdGotohAfterK = gotohStdGlobal (concrete)
theorem stdGotohAfterK_eq_v1 :
    (stdGotohAfterK [0,1,0,1] [1,0,1,0] 1 1 4).h.getD 4 0 =
    gotohStdGlobal [0,1,0,1] [1,0,1,0] 1 1 := by native_decide
theorem stdGotohAfterK_eq_v2 :
    (stdGotohAfterK [0,1,0] [0,1,0] 2 1 3).h.getD 3 0 =
    gotohStdGlobal [0,1,0] [0,1,0] 2 1 := by native_decide

/-! ## Core Theorems -/

/-- Lower bound: Gotoh DP score >= LCS path Gotoh score. -/
theorem gotoh_ge_lcs_path_score (a b : List ℕ) (go ge : ℤ)
    (h_go : go ≥ 1) (h_ge : ge ≥ 1) :
    gotohStdGlobal a b go ge ≥ lcsPathGotohScore a b go ge := by
  sorry

/-- Equal-length exactness: when lcsPathGotohScore >= 0, Gotoh equals it. -/
theorem gotoh_eq_lcs_path_when_nonneg (a b : List ℕ) (go ge : ℤ)
    (h_go : go ≥ 1) (h_ge : ge ≥ 1)
    (h_len : a.length = b.length)
    (h_nonneg : lcsPathGotohScore a b go ge ≥ 0) :
    gotohStdGlobal a b go ge = lcsPathGotohScore a b go ge := by
  sorry

/-- Concrete: lower bound on test cases. -/
theorem gotoh_ge_lcs_path_v1 :
    gotohStdGlobal [0,1,0,1] [1,0,1,0] 1 1 ≥ lcsPathGotohScore [0,1,0,1] [1,0,1,0] 1 1 := by
  native_decide
theorem gotoh_ge_lcs_path_v2 :
    gotohStdGlobal [0,0,0,1] [1,0,0,0] 1 1 ≥ lcsPathGotohScore [0,0,0,1] [1,0,0,0] 1 1 := by
  native_decide

/-- Concrete: equal-length exactness when lcs_gotoh >= 0. -/
theorem gotoh_eq_lcs_path_nonneg_v1 :
    lcsPathGotohScore [0,1,0] [0,1,0] 2 1 ≥ 0 →
    gotohStdGlobal [0,1,0] [0,1,0] 2 1 = lcsPathGotohScore [0,1,0] [0,1,0] 2 1 := by
  native_decide

/-! ## Exhaustive Verification -/

theorem gotoh_ge_lcs_path_exhaustive_3x3_bin :
    ∀ (a : Fin 8) (b : Fin 8),
    let al := [(a.val / 4) % 2, (a.val / 2) % 2, a.val % 2]
    let bl := [(b.val / 4) % 2, (b.val / 2) % 2, b.val % 2]
    gotohStdGlobal al bl 1 1 ≥ lcsPathGotohScore al bl 1 1 := by
  native_decide

theorem gotoh_eq_lcs_path_exhaustive_3x3_bin :
    ∀ (a : Fin 8) (b : Fin 8),
    let al := [(a.val / 4) % 2, (a.val / 2) % 2, a.val % 2]
    let bl := [(b.val / 4) % 2, (b.val / 2) % 2, b.val % 2]
    lcsPathGotohScore al bl 1 1 ≥ 0 →
    gotohStdGlobal al bl 1 1 = lcsPathGotohScore al bl 1 1 := by
  native_decide

theorem gotoh_ge_lcs_path_exhaustive_3x3_tern :
    ∀ (a : Fin 27) (b : Fin 27),
    let al := [(a.val / 9) % 3, (a.val / 3) % 3, a.val % 3]
    let bl := [(b.val / 9) % 3, (b.val / 3) % 3, b.val % 3]
    gotohStdGlobal al bl 2 1 ≥ lcsPathGotohScore al bl 2 1 := by
  native_decide

theorem gotoh_eq_lcs_path_exhaustive_3x3_tern :
    ∀ (a : Fin 27) (b : Fin 27),
    let al := [(a.val / 9) % 3, (a.val / 3) % 3, a.val % 3]
    let bl := [(b.val / 9) % 3, (b.val / 3) % 3, b.val % 3]
    lcsPathGotohScore al bl 2 1 ≥ 0 →
    gotohStdGlobal al bl 2 1 = lcsPathGotohScore al bl 2 1 := by
  native_decide

/-! ## DP Induction Infrastructure

Mirror ScoreDetermination.lean proof infrastructure for standard global. -/

/-- H list length after processing one row. -/
theorem stdGotohProcessRow_h_length (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row : ℕ) :
    (stdGotohProcessRow prev ai b go ge row).h.length = b.length + 1 := by
  unfold stdGotohProcessRow
  simp only [List.length_reverse]
  set n := b.length
  set f := fun (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) =>
    let j := jIdx + 1
    let bChar := b.getD jIdx 0
    let matchScore : ℤ := if ai == bChar then 1 else 0
    let diag := prev.h.getD (j - 1) 0 + matchScore
    let eij := max (prev.h.getD j 0 - go - ge) (prev.e.getD j NEG_INF_STD - ge)
    let fij := max (acc.1.head! - go - ge) (acc.2.2.head! - ge)
    let hij := max diag (max eij fij)
    (hij :: acc.1, eij :: acc.2.1, fij :: acc.2.2)
  have h_step : ∀ acc jIdx, (f acc jIdx).1.length = acc.1.length + 1 := by
    intro acc jIdx; simp only [f, List.length_cons]
  suffices ∀ (init : List ℤ × List ℤ × List ℤ) (k : ℕ),
      ((List.range k).foldl f init).1.length = init.1.length + k by
    have := this ([-(go + (↑row : ℤ) * ge)],
                  [-(go + (↑row : ℤ) * ge)],
                  [NEG_INF_STD]) n
    simp only [List.length_cons, List.length_nil] at this
    omega
  intro init k
  induction k generalizing init with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [h_step, ih]; omega

/-- H list length after k rows. -/
theorem stdGotohAfterK_h_length (a b : List ℕ) (go ge : ℤ) (k : ℕ) :
    (stdGotohAfterK a b go ge k).h.length = b.length + 1 := by
  induction k with
  | zero => simp [stdGotohAfterK, stdGotohInitRow, List.length_map, List.length_range]
  | succ n ih => simp only [stdGotohAfterK]; exact stdGotohProcessRow_h_length _ _ _ _ _ _

/-! ### Column-recursive cell values -/

mutual
/-- H value at column j (column-recursive, for induction). -/
def stdGotohCellH (prev : StdGotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ) (row : ℕ) : ℕ → ℤ
  | 0 => -(go + (row : ℤ) * ge)
  | j + 1 =>
    let bChar := b.getD j 0
    let matchScore : ℤ := if ai == bChar then 1 else 0
    let diag := prev.h.getD j 0 + matchScore
    let eij := max (prev.h.getD (j + 1) 0 - go - ge) (prev.e.getD (j + 1) NEG_INF_STD - ge)
    let fij := max (stdGotohCellH prev ai b go ge row j - go - ge)
                   (stdGotohCellF prev ai b go ge row j - ge)
    max diag (max eij fij)

/-- F value at column j (column-recursive). -/
def stdGotohCellF (prev : StdGotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ) (row : ℕ) : ℕ → ℤ
  | 0 => NEG_INF_STD
  | j + 1 =>
    max (stdGotohCellH prev ai b go ge row j - go - ge)
        (stdGotohCellF prev ai b go ge row j - ge)
end

/-- H at col >= 1 is >= diagonal contribution (H = max(diag, E, F) >= diag). -/
theorem stdGotohCellH_ge_diag (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol : col ≥ 1) :
    stdGotohCellH prev ai b go ge row col ≥
    prev.h.getD (col - 1) 0 + (if ai == b.getD (col - 1) 0 then 1 else 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, col = k + 1 := ⟨col - 1, by omega⟩
  simp only [stdGotohCellH, Nat.add_sub_cancel]
  exact le_max_left _ _

/-! ### Cell-level E definition and gap bounds -/

/-- Cell-recursive E value at column j. E only depends on prev row. -/
def stdGotohCellE (prev : StdGotohRow) (go ge : ℤ) (row : ℕ) : ℕ → ℤ
  | 0 => -(go + (row : ℤ) * ge)
  | j + 1 => max (prev.h.getD (j + 1) 0 - go - ge) (prev.e.getD (j + 1) NEG_INF_STD - ge)

/-- H cell >= prev.h - go - ge (vertical gap open via E). -/
theorem stdGotohCellH_ge_prev_h (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row j : ℕ) :
    stdGotohCellH prev ai b go ge row (j + 1) ≥ prev.h.getD (j + 1) 0 - go - ge := by
  simp only [stdGotohCellH]
  exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))

/-- H cell >= H prev col - go - ge (horizontal gap via F). -/
theorem stdGotohCellH_ge_prev_col (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row j : ℕ) :
    stdGotohCellH prev ai b go ge row (j + 1) ≥
    stdGotohCellH prev ai b go ge row j - go - ge := by
  simp only [stdGotohCellH]
  exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

/-- H cell >= F cell (H = max(diag, E, F) >= F). -/
theorem stdGotohCellH_ge_cellF (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row j : ℕ) :
    stdGotohCellH prev ai b go ge row (j + 1) ≥
    stdGotohCellF prev ai b go ge row (j + 1) := by
  simp only [stdGotohCellH]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- H cell >= E cell (from E component in max). -/
theorem stdGotohCellH_ge_cellE (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row j : ℕ) :
    stdGotohCellH prev ai b go ge row (j + 1) ≥
    stdGotohCellE prev go ge row (j + 1) := by
  simp only [stdGotohCellH, stdGotohCellE]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- F cell gap open: F >= H prev col - go - ge. -/
theorem stdGotohCellF_ge_cellH (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row j : ℕ) :
    stdGotohCellF prev ai b go ge row (j + 1) ≥
    stdGotohCellH prev ai b go ge row j - go - ge := by
  simp only [stdGotohCellF]; exact le_max_left _ _

/-- F cell gap extend: F >= F prev col - ge. -/
theorem stdGotohCellF_ge_prev_F (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row j : ℕ) :
    stdGotohCellF prev ai b go ge row (j + 1) ≥
    stdGotohCellF prev ai b go ge row j - ge := by
  simp only [stdGotohCellF]; exact le_max_right _ _

/-! ### Fold infrastructure for stdGotohProcessRow bridge -/

/-- Fold step function matching stdGotohProcessRow's anonymous lambda. -/
def stdGotohRowFoldStep (prev : StdGotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ)
    (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) : List ℤ × List ℤ × List ℤ :=
  let j := jIdx + 1
  let bChar := b.getD jIdx 0
  let matchScore : ℤ := if ai == bChar then 1 else 0
  let diag := prev.h.getD (j - 1) 0 + matchScore
  let eij := max (prev.h.getD j 0 - go - ge) (prev.e.getD j NEG_INF_STD - ge)
  let fij := max (acc.1.head! - go - ge) (acc.2.2.head! - ge)
  let hij := max diag (max eij fij)
  (hij :: acc.1, eij :: acc.2.1, fij :: acc.2.2)

/-- Fold state after k steps of stdGotohProcessRow. -/
def stdGotohRowFoldAfterK (prev : StdGotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ) (row : ℕ)
    (k : ℕ) : List ℤ × List ℤ × List ℤ :=
  let h0 : ℤ := -(go + (row : ℤ) * ge)
  let e0 : ℤ := h0
  let f0 : ℤ := NEG_INF_STD
  let init : List ℤ × List ℤ × List ℤ := ([h0], [e0], [f0])
  (List.range k).foldl (stdGotohRowFoldStep prev ai b go ge) init

theorem stdGotohProcessRow_h_eq_foldAfterN (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row : ℕ) :
    (stdGotohProcessRow prev ai b go ge row).h =
    (stdGotohRowFoldAfterK prev ai b go ge row b.length).1.reverse := by
  unfold stdGotohProcessRow stdGotohRowFoldAfterK stdGotohRowFoldStep; rfl

theorem stdGotohProcessRow_e_eq_foldAfterN (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row : ℕ) :
    (stdGotohProcessRow prev ai b go ge row).e =
    (stdGotohRowFoldAfterK prev ai b go ge row b.length).2.1.reverse := by
  unfold stdGotohProcessRow stdGotohRowFoldAfterK stdGotohRowFoldStep; rfl

theorem stdGotohRowFoldStep_h_length (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) :
    (stdGotohRowFoldStep prev ai b go ge acc jIdx).1.length = acc.1.length + 1 := by
  simp [stdGotohRowFoldStep, List.length_cons]

theorem stdGotohRowFoldStep_e_length (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) :
    (stdGotohRowFoldStep prev ai b go ge acc jIdx).2.1.length = acc.2.1.length + 1 := by
  simp [stdGotohRowFoldStep, List.length_cons]

theorem stdGotohRowFoldStep_f_length (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) :
    (stdGotohRowFoldStep prev ai b go ge acc jIdx).2.2.length = acc.2.2.length + 1 := by
  simp [stdGotohRowFoldStep, List.length_cons]

theorem stdGotohRowFoldAfterK_step (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    stdGotohRowFoldAfterK prev ai b go ge row (k + 1) =
    stdGotohRowFoldStep prev ai b go ge (stdGotohRowFoldAfterK prev ai b go ge row k) k := by
  unfold stdGotohRowFoldAfterK
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem stdGotohRowFoldAfterK_h_length_fold (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    (stdGotohRowFoldAfterK prev ai b go ge row k).1.length = k + 1 := by
  induction k with
  | zero => simp [stdGotohRowFoldAfterK]
  | succ n ih => rw [stdGotohRowFoldAfterK_step, stdGotohRowFoldStep_h_length, ih]

theorem stdGotohRowFoldAfterK_e_length_fold (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    (stdGotohRowFoldAfterK prev ai b go ge row k).2.1.length = k + 1 := by
  induction k with
  | zero => simp [stdGotohRowFoldAfterK]
  | succ n ih => rw [stdGotohRowFoldAfterK_step, stdGotohRowFoldStep_e_length, ih]

theorem stdGotohRowFoldAfterK_f_length_fold (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    (stdGotohRowFoldAfterK prev ai b go ge row k).2.2.length = k + 1 := by
  induction k with
  | zero => simp [stdGotohRowFoldAfterK]
  | succ n ih => rw [stdGotohRowFoldAfterK_step, stdGotohRowFoldStep_f_length, ih]

/-- Head invariant: head of H/E/F lists = cellH/cellE/cellF at column k. -/
theorem stdGotohRowFoldAfterK_head_eq (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    (stdGotohRowFoldAfterK prev ai b go ge row k).1.head! =
        stdGotohCellH prev ai b go ge row k ∧
    (stdGotohRowFoldAfterK prev ai b go ge row k).2.1.head! =
        stdGotohCellE prev go ge row k ∧
    (stdGotohRowFoldAfterK prev ai b go ge row k).2.2.head! =
        stdGotohCellF prev ai b go ge row k := by
  induction k with
  | zero =>
    simp [stdGotohRowFoldAfterK, stdGotohCellH, stdGotohCellE, stdGotohCellF, NEG_INF_STD]
  | succ n ih =>
    obtain ⟨ih_h, _, ih_f⟩ := ih
    rw [stdGotohRowFoldAfterK_step]
    refine ⟨?_, ?_, ?_⟩
    · simp only [stdGotohRowFoldStep, List.head!_cons]
      conv_rhs => rw [stdGotohCellH]
      simp only [Nat.add_sub_cancel]
      rw [← ih_h, ← ih_f]
    · simp only [stdGotohRowFoldStep, List.head!_cons]; rfl
    · simp only [stdGotohRowFoldStep, List.head!_cons]
      conv_rhs => rw [stdGotohCellF]
      rw [← ih_h, ← ih_f]

/-- H list: unreversed getD (k-col) = cellH col. -/
theorem stdGotohRowFoldAfterK_h_getD (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k col : ℕ) (hcol : col ≤ k) :
    (stdGotohRowFoldAfterK prev ai b go ge row k).1.getD (k - col) NEG_INF_STD =
    stdGotohCellH prev ai b go ge row col := by
  induction k with
  | zero =>
    have : col = 0 := by omega
    subst this; simp [stdGotohRowFoldAfterK, stdGotohCellH]
  | succ n ih =>
    rw [stdGotohRowFoldAfterK_step]
    by_cases hcol_eq : col = n + 1
    · subst hcol_eq
      simp only [Nat.sub_self]
      unfold stdGotohRowFoldStep stdGotohCellH
      simp only [Nat.add_sub_cancel, List.getD, List.getElem?_cons_zero, Option.getD_some]
      have ⟨ih_h, _, ih_f⟩ := stdGotohRowFoldAfterK_head_eq prev ai b go ge row n
      rw [← ih_h, ← ih_f]
    · have hle : col ≤ n := by omega
      rw [show n + 1 - col = (n - col) + 1 from by omega]
      simp only [stdGotohRowFoldStep, List.getD, List.getElem?_cons_succ]
      exact ih hle

/-- E list: unreversed getD (k-col) = cellE col. -/
theorem stdGotohRowFoldAfterK_e_getD (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k col : ℕ) (hcol : col ≤ k) :
    (stdGotohRowFoldAfterK prev ai b go ge row k).2.1.getD (k - col) NEG_INF_STD =
    stdGotohCellE prev go ge row col := by
  induction k with
  | zero =>
    have : col = 0 := by omega
    subst this; simp [stdGotohRowFoldAfterK, stdGotohCellE]
  | succ n ih =>
    rw [stdGotohRowFoldAfterK_step]
    by_cases hcol_eq : col = n + 1
    · subst hcol_eq
      simp only [Nat.sub_self, stdGotohRowFoldStep, List.getD, List.getElem?_cons_zero,
        Option.getD_some]
      rfl
    · have hle : col ≤ n := by omega
      rw [show n + 1 - col = (n - col) + 1 from by omega]
      simp only [stdGotohRowFoldStep, List.getD, List.getElem?_cons_succ]
      exact ih hle

/-- H reversed: getD col = cellH col. -/
theorem stdGotohRowFoldAfterK_h_reverse_getD (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k col : ℕ) (hcol : col ≤ k) :
    (stdGotohRowFoldAfterK prev ai b go ge row k).1.reverse.getD col NEG_INF_STD =
    stdGotohCellH prev ai b go ge row col := by
  have h_len := stdGotohRowFoldAfterK_h_length_fold prev ai b go ge row k
  have h_lt : col < (stdGotohRowFoldAfterK prev ai b go ge row k).1.length := by rw [h_len]; omega
  rw [List.getD_reverse col h_lt, h_len, show k + 1 - 1 - col = k - col from by omega]
  exact stdGotohRowFoldAfterK_h_getD prev ai b go ge row k col hcol

/-- E reversed: getD col = cellE col. -/
theorem stdGotohRowFoldAfterK_e_reverse_getD (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k col : ℕ) (hcol : col ≤ k) :
    (stdGotohRowFoldAfterK prev ai b go ge row k).2.1.reverse.getD col NEG_INF_STD =
    stdGotohCellE prev go ge row col := by
  have h_len := stdGotohRowFoldAfterK_e_length_fold prev ai b go ge row k
  have h_lt : col < (stdGotohRowFoldAfterK prev ai b go ge row k).2.1.length := by
    rw [h_len]; omega
  rw [List.getD_reverse col h_lt, h_len, show k + 1 - 1 - col = k - col from by omega]
  exact stdGotohRowFoldAfterK_e_getD prev ai b go ge row k col hcol

/-! ### Bridge: cell values = processRow output -/

/-- cellH = processRow H at valid column. -/
theorem stdGotohCellH_eq_processRow (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol : col ≤ b.length) :
    stdGotohCellH prev ai b go ge row col =
    (stdGotohProcessRow prev ai b go ge row).h.getD col NEG_INF_STD := by
  rw [stdGotohProcessRow_h_eq_foldAfterN]
  exact (stdGotohRowFoldAfterK_h_reverse_getD prev ai b go ge row b.length col hcol).symm

/-- cellE = processRow E at valid column. -/
theorem stdGotohCellE_eq_processRow (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol : col ≤ b.length) :
    stdGotohCellE prev go ge row col =
    (stdGotohProcessRow prev ai b go ge row).e.getD col NEG_INF_STD := by
  rw [stdGotohProcessRow_e_eq_foldAfterN]
  exact (stdGotohRowFoldAfterK_e_reverse_getD prev ai b go ge row b.length col hcol).symm

/-! ### ProcessRow-level gap bounds -/

/-- H in new row >= H in prev row - go - ge (vertical gap step). -/
theorem stdGotohProcessRow_h_ge_prev_h (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol_ge : col ≥ 1) (hcol_le : col ≤ b.length) :
    (stdGotohProcessRow prev ai b go ge row).h.getD col NEG_INF_STD ≥
    prev.h.getD col 0 - go - ge := by
  rw [← stdGotohCellH_eq_processRow prev ai b go ge row col hcol_le]
  obtain ⟨j, rfl⟩ : ∃ j, col = j + 1 := ⟨col - 1, by omega⟩
  exact stdGotohCellH_ge_prev_h prev ai b go ge row j

/-- E open: new E >= prev H - go - ge. -/
theorem stdGotohProcessRow_e_ge_prev_h (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol_ge : col ≥ 1) (hcol_le : col ≤ b.length) :
    (stdGotohProcessRow prev ai b go ge row).e.getD col NEG_INF_STD ≥
    prev.h.getD col 0 - go - ge := by
  rw [← stdGotohCellE_eq_processRow prev ai b go ge row col hcol_le]
  obtain ⟨j, rfl⟩ : ∃ j, col = j + 1 := ⟨col - 1, by omega⟩
  simp only [stdGotohCellE]; exact le_max_left _ _

/-- E extend: new E >= prev E - ge. -/
theorem stdGotohProcessRow_e_ge_prev_e (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol_ge : col ≥ 1) (hcol_le : col ≤ b.length) :
    (stdGotohProcessRow prev ai b go ge row).e.getD col NEG_INF_STD ≥
    prev.e.getD col NEG_INF_STD - ge := by
  rw [← stdGotohCellE_eq_processRow prev ai b go ge row col hcol_le]
  obtain ⟨j, rfl⟩ : ∃ j, col = j + 1 := ⟨col - 1, by omega⟩
  simp only [stdGotohCellE]; exact le_max_right _ _

/-- H >= E within a row. -/
theorem stdGotohProcessRow_h_ge_e (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol_ge : col ≥ 1) (hcol_le : col ≤ b.length) :
    (stdGotohProcessRow prev ai b go ge row).h.getD col NEG_INF_STD ≥
    (stdGotohProcessRow prev ai b go ge row).e.getD col NEG_INF_STD := by
  rw [← stdGotohCellH_eq_processRow prev ai b go ge row col hcol_le,
      ← stdGotohCellE_eq_processRow prev ai b go ge row col hcol_le]
  obtain ⟨j, rfl⟩ : ∃ j, col = j + 1 := ⟨col - 1, by omega⟩
  exact stdGotohCellH_ge_cellE prev ai b go ge row j

/-- Match step: processRow H at col >= prev.h at (col-1) + match. -/
theorem stdGotohProcessRow_diag_ge' (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol_ge : col ≥ 1) (hcol_le : col ≤ b.length) :
    (stdGotohProcessRow prev ai b go ge row).h.getD col NEG_INF_STD ≥
    prev.h.getD (col - 1) 0 + (if ai == b.getD (col - 1) 0 then 1 else 0) := by
  rw [← stdGotohCellH_eq_processRow prev ai b go ge row col hcol_le]
  exact stdGotohCellH_ge_diag prev ai b go ge row col hcol_ge

/-! ### Cross-row gap propagation -/

/-- E extend: E[k+d][j] >= E[k][j] - d*ge (repeated gap extension across rows). -/
theorem stdGotoh_E_extend (a b : List ℕ) (go ge : ℤ) (k j : ℕ)
    (hj : j ≥ 1) (hj_le : j ≤ b.length) :
    ∀ d : ℕ, k + d ≤ a.length →
    (stdGotohAfterK a b go ge (k + d)).e.getD j NEG_INF_STD ≥
    (stdGotohAfterK a b go ge k).e.getD j NEG_INF_STD - (d : ℤ) * ge := by
  intro d; induction d with
  | zero => intro _; simp
  | succ n ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 : (stdGotohAfterK a b go ge (k + n + 1)).e.getD j NEG_INF_STD ≥
              (stdGotohAfterK a b go ge (k + n)).e.getD j NEG_INF_STD - ge :=
      stdGotohProcessRow_e_ge_prev_e (stdGotohAfterK a b go ge (k + n))
        (a.getD (k + n) 0) b go ge ((k + n) + 1) j hj hj_le
    rw [show k + (n + 1) = k + n + 1 from by omega]
    push_cast at h1 h2 ⊢; linarith

/-- E propagation: E[i+d][j] >= H[i][j] - go - d*ge (d >= 1, open + extend). -/
theorem stdGotoh_E_propagation (a b : List ℕ) (go ge : ℤ) (i j d : ℕ)
    (hd : d ≥ 1) (hj : j ≥ 1) (hj_le : j ≤ b.length) (hid : i + d ≤ a.length) :
    (stdGotohAfterK a b go ge (i + d)).e.getD j NEG_INF_STD ≥
    (stdGotohAfterK a b go ge i).h.getD j 0 - go - (d : ℤ) * ge := by
  -- E[i+1] >= H[i] - go - ge (open), then E[i+d] >= E[i+1] - (d-1)*ge (extend)
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  -- E open: E[i+1] >= H[i] - go - ge
  have h_open : (stdGotohAfterK a b go ge (i + 1)).e.getD j NEG_INF_STD ≥
      (stdGotohAfterK a b go ge i).h.getD j 0 - go - ge :=
    stdGotohProcessRow_e_ge_prev_h (stdGotohAfterK a b go ge i)
      (a.getD i 0) b go ge (i + 1) j hj hj_le
  -- E extend: E[i+1+n] >= E[i+1] - n*ge
  have h_ext := stdGotoh_E_extend a b go ge (i + 1) j hj hj_le n (by omega)
  rw [show i + 1 + n = i + (n + 1) from by omega] at h_ext
  push_cast at h_open h_ext ⊢; linarith

/-- H >= E at any row k+1 (where processRow is applied). -/
theorem stdGotoh_h_ge_e (a b : List ℕ) (go ge : ℤ) (k j : ℕ)
    (hj : j ≥ 1) (hj_le : j ≤ b.length) :
    (stdGotohAfterK a b go ge (k + 1)).h.getD j NEG_INF_STD ≥
    (stdGotohAfterK a b go ge (k + 1)).e.getD j NEG_INF_STD :=
  stdGotohProcessRow_h_ge_e (stdGotohAfterK a b go ge k)
    (a.getD k 0) b go ge (k + 1) j hj hj_le

/-- **Vertical gap propagation**: H[i+d][j] >= H[i][j] - stdGapCost(d). -/
theorem stdGotoh_vertical_gap (a b : List ℕ) (go ge : ℤ)
    (i j d : ℕ) (hj : j ≥ 1) (hj_le : j ≤ b.length) (hid : i + d ≤ a.length) :
    (stdGotohAfterK a b go ge (i + d)).h.getD j 0 ≥
    (stdGotohAfterK a b go ge i).h.getD j 0 - stdGapCost d go ge := by
  cases d with
  | zero => simp [stdGapCost]
  | succ n =>
    simp only [stdGapCost, Nat.succ_ne_zero, ↓reduceIte]
    -- H[i+n+1] >= E[i+n+1] >= H[i] - go - (n+1)*ge
    have h_len := stdGotohAfterK_h_length a b go ge (i + (n + 1))
    have h_valid : j < (stdGotohAfterK a b go ge (i + (n + 1))).h.length := by rw [h_len]; omega
    rw [List.getD_default_irrel _ _ 0 NEG_INF_STD h_valid]
    have h_he : (stdGotohAfterK a b go ge (i + (n + 1))).h.getD j NEG_INF_STD ≥
        (stdGotohAfterK a b go ge (i + (n + 1))).e.getD j NEG_INF_STD := by
      rw [show i + (n + 1) = (i + n) + 1 from by omega]
      exact stdGotoh_h_ge_e a b go ge (i + n) j hj hj_le
    have h_ep := stdGotoh_E_propagation a b go ge i j (n + 1) (by omega) hj hj_le hid
    linarith

/-! ### Within-row gap propagation -/

/-- F horizontal gap: F[j+d] >= H[j] - go - d*ge (d >= 1, cell level). -/
theorem stdGotohCellF_horizontal_gap (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row j : ℕ) :
    ∀ d : ℕ, d ≥ 1 →
    stdGotohCellF prev ai b go ge row (j + d) ≥
    stdGotohCellH prev ai b go ge row j - go - (d : ℤ) * ge := by
  intro d; induction d with
  | zero => omega
  | succ n ih =>
    intro _
    rw [show j + (n + 1) = (j + n) + 1 from by omega]
    by_cases hn : n = 0
    · subst hn; simp only [Nat.zero_add, Nat.cast_one, one_mul]
      exact stdGotohCellF_ge_cellH prev ai b go ge row j
    · have h1 := ih (by omega)
      have h2 := stdGotohCellF_ge_prev_F prev ai b go ge row (j + n)
      push_cast at h1 h2 ⊢; linarith

/-- H horizontal gap: H[j+d] >= H[j] - stdGapCost(d) (cell level). -/
theorem stdGotohCellH_horizontal_gap (prev : StdGotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row j d : ℕ) :
    stdGotohCellH prev ai b go ge row (j + d) ≥
    stdGotohCellH prev ai b go ge row j - stdGapCost d go ge := by
  cases d with
  | zero => simp [stdGapCost]
  | succ n =>
    simp only [stdGapCost, Nat.succ_ne_zero, ↓reduceIte]
    rw [show j + (n + 1) = (j + n) + 1 from by omega]
    have hF := stdGotohCellF_horizontal_gap prev ai b go ge row j (n + 1) (by omega)
    rw [show j + (n + 1) = (j + n) + 1 from by omega] at hF
    have hHF := stdGotohCellH_ge_cellF prev ai b go ge row (j + n)
    linarith

/-! ### Horizontal gap at afterK level -/

/-- Horizontal gap at afterK level for k >= 1. -/
theorem stdGotoh_horizontal_gap_succ (a b : List ℕ) (go ge : ℤ) (k j d : ℕ)
    (hj_le : j ≤ b.length) (hjd_le : j + d ≤ b.length) :
    (stdGotohAfterK a b go ge (k + 1)).h.getD (j + d) 0 ≥
    (stdGotohAfterK a b go ge (k + 1)).h.getD j 0 - stdGapCost d go ge := by
  have h_len := stdGotohAfterK_h_length a b go ge (k + 1)
  have hv1 : j + d < (stdGotohAfterK a b go ge (k + 1)).h.length := by rw [h_len]; omega
  have hv2 : j < (stdGotohAfterK a b go ge (k + 1)).h.length := by rw [h_len]; omega
  rw [List.getD_default_irrel _ _ 0 NEG_INF_STD hv1, List.getD_default_irrel _ _ 0 NEG_INF_STD hv2]
  -- Unfold stdGotohAfterK(k+1) to stdGotohProcessRow
  change (stdGotohProcessRow (stdGotohAfterK a b go ge k) (a.getD k 0) b go ge (k + 1)).h.getD
      (j + d) NEG_INF_STD ≥
    (stdGotohProcessRow (stdGotohAfterK a b go ge k) (a.getD k 0) b go ge (k + 1)).h.getD
      j NEG_INF_STD - stdGapCost d go ge
  rw [← stdGotohCellH_eq_processRow _ _ _ _ _ _ (j + d) hjd_le,
      ← stdGotohCellH_eq_processRow _ _ _ _ _ _ j hj_le]
  exact stdGotohCellH_horizontal_gap _ _ _ _ _ (k + 1) j d

/-- Combined gap: H[r+dr][c+dc] >= H[r][c] - stdGapCost(dr) - stdGapCost(dc).
    Requires c >= 1 or dr = 0 (vertical gap needs column >= 1). -/
theorem stdGotoh_combined_gap (a b : List ℕ) (go ge : ℤ)
    (h_go : go ≥ 1) (h_ge : ge ≥ 1)
    (r c dr dc : ℕ)
    (hc_le : c + dc ≤ b.length) (hr_le : r + dr ≤ a.length)
    (hc_ge : c ≥ 1 ∨ dr = 0) :
    (stdGotohAfterK a b go ge (r + dr)).h.getD (c + dc) 0 ≥
    (stdGotohAfterK a b go ge r).h.getD c 0 - stdGapCost dr go ge - stdGapCost dc go ge := by
  have h_vert : (stdGotohAfterK a b go ge (r + dr)).h.getD c 0 ≥
      (stdGotohAfterK a b go ge r).h.getD c 0 - stdGapCost dr go ge := by
    rcases hc_ge with hc1 | hdr0
    · exact stdGotoh_vertical_gap a b go ge r c dr hc1 (by omega) hr_le
    · subst hdr0; simp [stdGapCost]
  have h_horiz : (stdGotohAfterK a b go ge (r + dr)).h.getD (c + dc) 0 ≥
      (stdGotohAfterK a b go ge (r + dr)).h.getD c 0 - stdGapCost dc go ge := by
    by_cases h0 : r + dr = 0
    · -- r = dr = 0, horizontal gap on init row
      have hr0 : r = 0 := by omega
      have hdr0 : dr = 0 := by omega
      subst hr0; subst hdr0; simp only [Nat.zero_add]
      -- Init row: H[0][c+dc] >= H[0][c] - stdGapCost(dc)
      -- H[0][j] = if j = 0 then 0 else -(go + j*ge), all ≥ -(go + j*ge)
      -- stdGapCost(dc) = go + dc*ge for dc ≥ 1, 0 for dc = 0
      -- This needs a case analysis; for now use omega/native_decide after unfolding
      simp only [stdGotohAfterK, stdGotohInitRow, stdGapCost]
      sorry  -- init row horizontal gap (tedious but true for go >= 1)
    · obtain ⟨k, hk⟩ : ∃ k, r + dr = k + 1 := ⟨r + dr - 1, by omega⟩
      rw [hk]
      exact stdGotoh_horizontal_gap_succ a b go ge k c dc (by omega) hc_le
  linarith

/-! ### Match step across rows -/

/-- Match step: H[i+1][j+1] >= H[i][j] + match(a[i], b[j]). -/
theorem stdGotoh_match_step (a b : List ℕ) (go ge : ℤ) (i j : ℕ)
    (hj_le : j + 1 ≤ b.length) :
    (stdGotohAfterK a b go ge (i + 1)).h.getD (j + 1) 0 ≥
    (stdGotohAfterK a b go ge i).h.getD j 0 +
    (if a.getD i 0 == b.getD j 0 then 1 else 0) := by
  have h_len := stdGotohAfterK_h_length a b go ge (i + 1)
  have h_valid : j + 1 < (stdGotohAfterK a b go ge (i + 1)).h.length := by rw [h_len]; omega
  rw [List.getD_default_irrel _ _ 0 NEG_INF_STD h_valid]
  have h_step := stdGotohProcessRow_diag_ge' (stdGotohAfterK a b go ge i) (a.getD i 0) b
    go ge (i + 1) (j + 1) (by omega) hj_le
  simp only [Nat.add_sub_cancel] at h_step
  exact h_step

/-! ## Information Chain

  diag  ≤  Gotoh  ≤  LCS

  Tier 1 (ε = 0):       score = diag = LCS
  Tier 2 (0 < ε ≤ go):  score = diag
  Tier 3a (ε > go, lcsPathGotohScore ≥ 0, |a|=|b|): score = lcsPathGotohScore
  Tier 3b (remaining):   score = Gotoh DP (banded)
-/
