/-
  FlashAlignment/CrossingCountLCS.lean

  The Deep Theorem: Crossing Count = LCS

  The fundamental result connecting the Krusche comb to string alignment:
  the crossing count #{j ∈ [s,s+w) : d_col[j] > j-s} from the comb's
  distance column equals LCS(A, B[s:s+w]) for all windows.

  This is Tiskin's Theorem 4.10 (monograph, 2022) adapted to the
  distance column formulation.

  Paper reference: Tiskin 2022, Theorem 4.10; Krusche 2010
-/
import Mathlib.Tactic
import AugmentedSeaweed.CombComposition
import AugmentedSeaweed.LCDCorrectness

/-! ## LCS via Dynamic Programming -/

/-- LCS DP: compute LCS length of two lists. Standard O(mn) DP. -/
def lcsDp (a : List ℕ) (b : List ℕ) : ℕ :=
  let n := b.length
  let init := List.replicate (n + 1) 0
  let final := a.foldl (fun (prev : List ℕ) ai =>
    -- Build current row: dp[i][0] = 0, then dp[i][j] for j = 1..n
    (List.range n).foldl (fun (curr : List ℕ) j =>
      let bj := b.getD j 0
      let val :=
        if ai == bj then
          prev.getD j 0 + 1  -- dp[i-1][j-1] + 1 (match)
        else
          max (prev.getD (j + 1) 0) (curr.getD j 0)  -- max(dp[i-1][j], dp[i][j-1])
      curr ++ [val]
    ) [0]
  ) init
  final.getD n 0

/-! ## Crossing Count -/

/-- Crossing count at window [s, s+w) from the comb's d_col. -/
def crossingCount' (d_col : List ℕ) (s w : ℕ) : ℕ :=
  (List.range w).countP (fun i => decide (d_col.getD (s + i) 0 > i))

/-! ## Basic Properties -/

/-- LCS of empty query is 0. -/
theorem lcsDp_nil (b : List ℕ) : lcsDp [] b = 0 := by
  simp [lcsDp]

/-- Crossing count is bounded by window width. -/
theorem crossingCount'_le_w (d_col : List ℕ) (s w : ℕ) :
    crossingCount' d_col s w ≤ w := by
  unfold crossingCount'
  have h := @List.countP_le_length ℕ
    (fun i => decide (d_col.getD (s + i) 0 > i)) (List.range w)
  simp [List.length_range] at h
  exact h

/-- Any element in List.replicate n 0 is 0. -/
private theorem getD_replicate_zero (n i : ℕ) :
    (List.replicate n 0).getD i 0 = 0 := by
  simp [List.getD]
  cases h : (List.replicate n 0)[i]? with
  | none => rfl
  | some val =>
    simp [Option.getD]
    exact List.eq_of_mem_replicate (List.mem_of_getElem? h)

/-- Crossing count on all-zero d_col is 0 (0 > i is false). -/
theorem crossingCount'_zero (n s w : ℕ) :
    crossingCount' (List.replicate n 0) s w = 0 := by
  unfold crossingCount'
  rw [List.countP_eq_zero]
  intro x _
  simp only [decide_eq_true_eq, not_lt]
  rw [getD_replicate_zero]
  exact Nat.zero_le x

/-! ## Concrete Verification

Verify the crossing count = LCS theorem on specific inputs via native_decide. -/

-- Single character queries
example : crossingCount' (combDcol [0] [0,1,0,1]) 0 4 = lcsDp [0] [0,1,0,1] := by
  native_decide
example : crossingCount' (combDcol [0] [0,1,0,1]) 1 2 = lcsDp [0] [1,0] := by
  native_decide
example : crossingCount' (combDcol [1] [0,1,0,1]) 0 3 = lcsDp [1] [0,1,0] := by
  native_decide

-- Two character queries
example : crossingCount' (combDcol [0,1] [1,0,1,0]) 0 4 = lcsDp [0,1] [1,0,1,0] := by
  native_decide
example : crossingCount' (combDcol [0,1] [1,0,1,0]) 1 3 = lcsDp [0,1] [0,1,0] := by
  native_decide
example : crossingCount' (combDcol [0,1] [1,0,1,0]) 2 2 = lcsDp [0,1] [1,0] := by
  native_decide

-- Three character queries
example : crossingCount' (combDcol [0,0,1] [1,0,0,1,0]) 0 5 =
    lcsDp [0,0,1] [1,0,0,1,0] := by native_decide
example : crossingCount' (combDcol [0,0,1] [1,0,0,1,0]) 1 3 =
    lcsDp [0,0,1] [0,0,1] := by native_decide
example : crossingCount' (combDcol [1,0,1] [0,1,0,1,0,1]) 0 6 =
    lcsDp [1,0,1] [0,1,0,1,0,1] := by native_decide
example : crossingCount' (combDcol [1,0,1] [0,1,0,1,0,1]) 2 3 =
    lcsDp [1,0,1] [0,1,0] := by native_decide

-- Four character query
example : crossingCount' (combDcol [0,1,0,1] [1,0,1,0,1]) 0 5 =
    lcsDp [0,1,0,1] [1,0,1,0,1] := by native_decide
example : crossingCount' (combDcol [0,1,0,1] [1,0,1,0,1]) 1 4 =
    lcsDp [0,1,0,1] [0,1,0,1] := by native_decide

/-! ## Bounded Verification via Fin -/

/-- All windows: a=[0,1], b=[1,0,1,0] -/
example : ∀ (s : Fin 5) (w : Fin 5),
    s.val + w.val ≤ 4 → w.val > 0 →
    crossingCount' (combDcol [0,1] [1,0,1,0]) s.val w.val =
    lcsDp [0,1] ((List.drop s.val [1,0,1,0]).take w.val) := by
  native_decide

/-- All windows: a=[0,0,1], b=[1,0,0,1,0] -/
example : ∀ (s : Fin 6) (w : Fin 6),
    s.val + w.val ≤ 5 → w.val > 0 →
    crossingCount' (combDcol [0,0,1] [1,0,0,1,0]) s.val w.val =
    lcsDp [0,0,1] ((List.drop s.val [1,0,0,1,0]).take w.val) := by
  native_decide

/-- All windows: a=[1,0,1], b=[0,1,0,1,0,1] -/
example : ∀ (s : Fin 7) (w : Fin 7),
    s.val + w.val ≤ 6 → w.val > 0 →
    crossingCount' (combDcol [1,0,1] [0,1,0,1,0,1]) s.val w.val =
    lcsDp [1,0,1] ((List.drop s.val [0,1,0,1,0,1]).take w.val) := by
  native_decide

/-! ## Row Processing Lemma

The key helper: processing one row via the comb changes the crossing count
in the same way as one step of the LCS DP changes the LCS value.

We need a generalized form that works with arbitrary initial d_col (not just zeros).
The generalized form states that IF the d_col before processing row `ch` has the
property that its crossing count at every window equals the LCS from the DP, THEN
the d_col after processing `ch` also has this property (with the DP having processed
one more character).

This is formalized via a "row simulation" lemma that relates processRow to one
step of lcsDp's foldl. -/

/-- One step of the LCS DP outer fold: process character `ai` against reference `b_win`,
    given previous DP row `prev`. Returns the new DP row. -/
def lcsDpStep (ai : ℕ) (b_win : List ℕ) (prev : List ℕ) : List ℕ :=
  let n := b_win.length
  (List.range n).foldl (fun (curr : List ℕ) j =>
    let bj := b_win.getD j 0
    let val :=
      if ai == bj then prev.getD j 0 + 1
      else max (prev.getD (j + 1) 0) (curr.getD j 0)
    curr ++ [val]
  ) [0]

/-- lcsDp as a fold of lcsDpStep. -/
theorem lcsDp_as_fold (a : List ℕ) (b : List ℕ) :
    lcsDp a b = (a.foldl (fun prev ai => lcsDpStep ai b prev)
      (List.replicate (b.length + 1) 0)).getD b.length 0 := by
  simp [lcsDp, lcsDpStep]

/-! ## crossingCount = crossingCount' (definitional equality) -/

/-- crossingCount and crossingCount' are the same function. -/
theorem crossingCount_eq_crossingCount' (d_col : List ℕ) (s w : ℕ) :
    crossingCount d_col s w = crossingCount' d_col s w := by
  rfl

/-! ## Right-Induction Strategy

The key insight for the proof is to induct on `a` from the RIGHT.

When `a = rest ++ [ch]`:
- **Comb**: `combDcol (rest ++ [ch]) b` = process `rest` first (getting d_col),
  then process one more row with character `ch`. By composition:
  `combDcol (rest ++ [ch]) b = processRow ch b (combDcol rest b) (rest.length + 1)`

- **DP**: `lcsDp (rest ++ [ch]) window` = DP fold processes `rest` first (getting
  intermediate row), then processes `ch` with that row.

Both sides process `rest` first (to which the IH applies), then `ch`.
The key lemma: processing one MORE row via the comb changes the crossing
count by the same amount as one more DP row step.

### The Row Step Lemma

Given d_col (from processing `rest`), and the crossing count invariant holds
for d_col, show that after `processRow ch b d_col offset`:
- The new crossing count equals the new DP value.

This is the cell-level content of Tiskin's Theorem 4.10. -/

/-- The offset component of combFold tracks a.length + init.2. -/
theorem combFold_offset_gen (a : List ℕ) (b : List ℕ) (init : RowAcc) :
    (combFold a b init).2 = a.length + init.2 := by
  induction a generalizing init with
  | nil => simp [combFold]
  | cons ch rest ih =>
    simp only [combFold, List.foldl]
    have : (List.foldl (rowFoldStep b) (rowFoldStep b init ch) rest).2 =
        (combFold rest b (rowFoldStep b init ch)).2 := by
      rfl
    rw [this, ih]
    simp [rowFoldStep]
    omega

/-- processRow preserves the length of d_col. -/
theorem processRow_length (ch : ℕ) (b : List ℕ) (d_col : List ℕ) (dr : ℕ)
    (hlen : d_col.length = b.length) :
    (processRow ch b d_col dr).length = b.length := by
  simp only [processRow]
  suffices h : ∀ k ≤ b.length,
      ((List.range k).foldl (colFoldStep ch b) (d_col, dr)).1.length = b.length by
    exact h b.length (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => simp [hlen]
  | succ k' ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [colFoldStep, colStep]
    split <;> (try split) <;> simp [List.length_set, ih (by omega)]

/-- combFold preserves the length of d_col. -/
theorem combFold_dcol_length (a : List ℕ) (b : List ℕ) (init : RowAcc)
    (hlen : init.1.length = b.length) :
    (combFold a b init).1.length = b.length := by
  induction a generalizing init with
  | nil => simp [combFold, hlen]
  | cons ch rest ih =>
    simp only [combFold, List.foldl]
    apply ih
    simp [rowFoldStep]
    exact processRow_length ch b init.1 (init.2 + 1) hlen

/-- combDcol produces a list of length b.length. -/
theorem combDcol_length (a : List ℕ) (b : List ℕ) :
    (combDcol a b).length = b.length := by
  simp [combDcol]
  exact combFold_dcol_length a b (combInit b.length) (by simp [combInit])

/-- The offset after processing `a` from combInit equals `a.length`. -/
theorem combFold_offset (a : List ℕ) (b : List ℕ) :
    (combFold a b (combInit b.length)).2 = a.length := by
  rw [combFold_offset_gen]; simp [combInit]

/-! ## The Generalized Invariant

The inductive proof requires a generalized version that works with
arbitrary comb states, not just combInit.

**Key Definition**: `CombEncodes d_col b a` means d_col correctly encodes
the semi-local LCS of query `a` against reference `b`:
  ∀ s w, s+w ≤ b.length → w > 0 →
    crossingCount'(d_col, s, w) = lcsDp a (b.drop s |>.take w)

**Generalized Theorem**: For any initial state `init` and corresponding
query prefix `a_prev`, if `CombEncodes init.1 b a_prev`, then after
processing `a_new` via the comb:
  CombEncodes (combFold a_new b init).1 b (a_prev ++ a_new)

This would let the main theorem follow from the base case
(CombEncodes (combInit n).1 b []) and the generalized step.

However, this generalized version requires showing that the row fold step
(processRow) preserves the encoding property. This is the deep content
of Tiskin 2022, Theorem 4.10, which establishes that each cell of the
seaweed braid simultaneously maintains the crossing count invariant
for ALL windows.
-/

/-- d_col correctly encodes the semi-local LCS of query `a` vs reference `b`. -/
def CombEncodes (d_col : List ℕ) (b : List ℕ) (a : List ℕ) : Prop :=
  ∀ (s w : ℕ), s + w ≤ b.length → w > 0 →
    crossingCount' d_col s w = lcsDp a (b.drop s |>.take w)

/-- Base case: all-zero d_col encodes the empty query. -/
theorem combEncodes_nil (b : List ℕ) :
    CombEncodes (List.replicate b.length 0) b [] := by
  intro s w hs hw
  simp [lcsDp]
  exact crossingCount'_zero b.length s w

/-! ### Row Step Lemma (Tiskin 4.10, mechanistic content)

If d_col encodes `a_prev` vs `b`, then after processing one more row
(character `ch`), the result encodes `a_prev ++ [ch]` vs `b`.

This requires showing colStep simultaneously maintains the crossing
count invariant for ALL windows [s, s+w) of b. Each cell (row ch, col j):
- Match: d_col[j] ← d_row, d_row ← old d_col[j]+1
- Mismatch-swap: same as match (values happen to sort)
- Mismatch-keep: d_col[j] unchanged, d_row ← d_row+1

The proof would proceed by induction on j (columns within the row),
maintaining a "column invariant" that relates partial processRow output
to the partial DP row update for each window.

The single-row case (a_prev = []) is proved separately below
using LCD correctness results. -/

/-! ### Row Step Lemma (Tiskin 4.10, mechanistic content)

**Row Step Lemma**: If d_col encodes `a_prev` vs `b`, then after
processing one row (character `ch`), the result encodes `a_prev ++ [ch]` vs `b`.

This is the mechanistic content of Tiskin 2022, Theorem 4.10.
The proof requires showing that colStep simultaneously maintains
the crossing count invariant for ALL windows of b.

Each cell (row ch, col j) updates d_col[j] and d_row via:
- Match (ch == b[j]): d_col[j] ← d_row, d_row ← old d_col[j] + 1
- Mismatch-swap (d_col[j] > d_row): same as match
- Mismatch-keep (d_col[j] ≤ d_row): d_col[j] unchanged, d_row ← d_row + 1

These operations mirror the LCS DP cell recurrence:
- Match: dp[i][j+1] = dp[i-1][j] + 1
- Mismatch: dp[i][j+1] = max(dp[i-1][j+1], dp[i][j])

The correspondence between d_col values and the DP row requires
showing that d_col[j] > j-s iff dp_row[j+1] > dp_row[j] (the DP row
increases at position j) for every window [s, s+w) simultaneously.

### Helper: partial processRow state -/

/-- State after processing columns 0..k-1 of a row. Returns (d_col, d_row). -/
def processRowPartial (ch : ℕ) (b : List ℕ) (d_col : List ℕ) (dr_init : ℕ)
    (k : ℕ) : List ℕ × ℕ :=
  (List.range k).foldl (colFoldStep ch b) (d_col, dr_init)

/-- processRow = first component of processRowPartial at k = b.length. -/
theorem processRow_eq_partial (ch : ℕ) (b : List ℕ) (d_col : List ℕ) (dr : ℕ) :
    processRow ch b d_col dr = (processRowPartial ch b d_col dr b.length).1 := by
  simp [processRow, processRowPartial]

/-- processRowPartial at 0 is the initial state. -/
theorem processRowPartial_zero (ch : ℕ) (b : List ℕ) (d_col : List ℕ) (dr : ℕ) :
    processRowPartial ch b d_col dr 0 = (d_col, dr) := by
  simp [processRowPartial]

/-- processRowPartial step: k+1 = colFoldStep applied to result at k. -/
theorem processRowPartial_succ (ch : ℕ) (b : List ℕ) (d_col : List ℕ) (dr : ℕ)
    (k : ℕ) :
    processRowPartial ch b d_col dr (k + 1) =
    colFoldStep ch b (processRowPartial ch b d_col dr k) k := by
  simp [processRowPartial, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]

/-- processRowPartial preserves d_col length. -/
theorem processRowPartial_length (ch : ℕ) (b : List ℕ) (d_col : List ℕ)
    (dr : ℕ) (k : ℕ) (hk : k ≤ b.length) (hlen : d_col.length = b.length) :
    (processRowPartial ch b d_col dr k).1.length = b.length := by
  induction k with
  | zero => simp [processRowPartial_zero, hlen]
  | succ k' ih =>
    rw [processRowPartial_succ]
    simp only [colFoldStep, colStep]
    split <;> (try split) <;> simp [List.length_set, ih (by omega)]

/-- Positions j ≥ k are untouched by processRowPartial at step k. -/
theorem processRowPartial_getD_ge (ch : ℕ) (b : List ℕ) (d_col : List ℕ)
    (dr : ℕ) (k j : ℕ) (hjk : k ≤ j) (hk : k ≤ b.length)
    (hlen : d_col.length = b.length) :
    (processRowPartial ch b d_col dr k).1.getD j 0 = d_col.getD j 0 := by
  induction k with
  | zero => simp [processRowPartial_zero]
  | succ k' ih =>
    rw [processRowPartial_succ]
    simp only [colFoldStep, colStep]
    have hk'_len : (processRowPartial ch b d_col dr k').1.length = b.length :=
      processRowPartial_length ch b d_col dr k' (by omega) hlen
    split <;> (try split) <;> {
      simp only [List.getD, List.getElem?_set]
      simp only [show ¬(k' = j) from by omega, ↓reduceIte]
      rw [← List.getD]
      exact ih (by omega) (by omega)
    }

/-! ### Helper: LCS DP row state -/

/-- LCS DP row for query `a` against window `b_win`.
    Returns a list of length b_win.length + 1 where element j is LCS(a, b_win[0:j]). -/
def lcsDpRow (a : List ℕ) (b_win : List ℕ) : List ℕ :=
  a.foldl (fun prev ai => lcsDpStep ai b_win prev) (List.replicate (b_win.length + 1) 0)

/-- lcsDpRow gives the same answer as lcsDp. -/
theorem lcsDpRow_getD_eq_lcsDp (a : List ℕ) (b_win : List ℕ) :
    (lcsDpRow a b_win).getD b_win.length 0 = lcsDp a b_win := by
  simp [lcsDpRow, lcsDp, lcsDpStep]

/-- lcsDpRow for a ++ [ch] = lcsDpStep ch applied to lcsDpRow a. -/
theorem lcsDpRow_append_singleton (a : List ℕ) (ch : ℕ) (b_win : List ℕ) :
    lcsDpRow (a ++ [ch]) b_win = lcsDpStep ch b_win (lcsDpRow a b_win) := by
  simp [lcsDpRow, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- lcsDpRow for [] is all zeros. -/
theorem lcsDpRow_nil (b_win : List ℕ) :
    lcsDpRow [] b_win = List.replicate (b_win.length + 1) 0 := by
  simp [lcsDpRow]

/-! ### The Column Invariant

The column invariant relates the partial processRow state (after processing
columns 0..k-1) to the LCS DP. The key relationship is:

  For each window [s, s+w) with s+w ≤ b.length and w > 0:
  - If s+w ≤ k: crossingCount' on the partial d_col equals LCS(a_prev++[ch], b[s:s+w])
  - If s+w > k: crossingCount' on the partial d_col equals ... (depends on partial DP)

The full invariant tracks the DP row for EVERY window simultaneously, which is
complex. Instead, we use a simpler approach: we show that the FINAL state
(k = b.length) has the right crossing counts, by relating colStep to lcsDpStep.

The key insight: at column k, colStep updates d_col[k] and d_row.
The relationship between (d_col, d_row) and the DP row is:
  d_col[j] > j - s  iff  dp_new[j-s+1] > dp_new[j-s]
  d_row > k - s      iff  dp_new[k-s+1] > dp_old[k-s+1]

where dp_old = lcsDpRow(a_prev, window) and dp_new = lcsDpRow(a_prev++[ch], window).

We formalize this as follows: -/

/-- The partial DP row for a single step: process columns 0..k-1 of lcsDpStep. -/
def lcsDpStepPartial (ai : ℕ) (b_win : List ℕ) (prev : List ℕ) (k : ℕ) : List ℕ :=
  (List.range k).foldl (fun (curr : List ℕ) j =>
    let bj := b_win.getD j 0
    let val :=
      if ai == bj then prev.getD j 0 + 1
      else max (prev.getD (j + 1) 0) (curr.getD j 0)
    curr ++ [val]
  ) [0]

/-- lcsDpStep equals lcsDpStepPartial at full length. -/
theorem lcsDpStep_eq_partial (ai : ℕ) (b_win : List ℕ) (prev : List ℕ) :
    lcsDpStep ai b_win prev = lcsDpStepPartial ai b_win prev b_win.length := by
  simp [lcsDpStep, lcsDpStepPartial]

/-- lcsDpStepPartial at 0 is [0]. -/
theorem lcsDpStepPartial_zero (ai : ℕ) (b_win : List ℕ) (prev : List ℕ) :
    lcsDpStepPartial ai b_win prev 0 = [0] := by
  simp [lcsDpStepPartial]

/-- lcsDpStepPartial step. -/
theorem lcsDpStepPartial_succ (ai : ℕ) (b_win : List ℕ) (prev : List ℕ) (k : ℕ) :
    lcsDpStepPartial ai b_win prev (k + 1) =
    let curr := lcsDpStepPartial ai b_win prev k
    let bk := b_win.getD k 0
    let val := if ai == bk then prev.getD k 0 + 1
               else max (prev.getD (k + 1) 0) (curr.getD k 0)
    curr ++ [val] := by
  simp [lcsDpStepPartial, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]

/-- lcsDpStepPartial has length k + 1. -/
theorem lcsDpStepPartial_length (ai : ℕ) (b_win : List ℕ) (prev : List ℕ) (k : ℕ) :
    (lcsDpStepPartial ai b_win prev k).length = k + 1 := by
  induction k with
  | zero => simp [lcsDpStepPartial_zero]
  | succ k' ih =>
    rw [lcsDpStepPartial_succ]
    simp [ih]

/-! ### The Column Simulation Invariant

The column invariant relates the partial processRow state (after processing
columns 0..k-1) to the LCS DP for ALL windows simultaneously.

For each window [s, s+w) with s+w ≤ b.length and w > 0, define:
  b_win := b[s:s+w]
  dp_old := lcsDpRow(a_prev, b_win)          -- DP row before adding ch
  dp_new := lcsDpRow(a_prev ++ [ch], b_win)  -- DP row after adding ch
         = lcsDpStep(ch, b_win, dp_old)

The invariant after processing columns 0..k-1 has three parts:

Part A (crossing ↔ DP increase): For processed positions within window:
  ∀ j < min(k, s+w) - s,  d_col_partial[s+j] > j  ↔  dp_new[j+1] > dp_new[j]

Part B (d_row ↔ DP frontier): For windows containing column k:
  ∀ window [s,s+w) with s ≤ k < s+w,
    d_row > k-s  ↔  dp_new[k-s+1] > dp_old[k-s+1]

Part C (untouched): Positions j ≥ k are unchanged:
  ∀ j ≥ k,  d_col_partial[j] = d_col_orig[j]

At k = b.length, Part A covers all positions in every window,
and the crossing count equals the number of DP increases, which equals LCS. -/

/-- The column simulation invariant (simplified).

    After processing columns 0..k-1 of the row for character ch:

    (A) For every window [s,s+w) and position j within the processed region:
        d_col_k[s+j] > j  ↔  dp_new_row[j+1] > dp_new_row[j]
        (where dp_new_row = lcsDpStep(ch, b[s:s+w], lcsDpRow(a_prev, b[s:s+w])))

    (C) For all j ≥ k:  d_col_k[j] = d_col_orig[j]  -/
def ColSimInv (d_col_k : List ℕ)
    (d_col_orig : List ℕ) (b : List ℕ) (a_prev : List ℕ) (ch : ℕ)
    (k : ℕ) : Prop :=
  -- Part A: crossing ↔ DP increase for processed positions
  (∀ s w, s + w ≤ b.length → w > 0 →
    ∀ j, j < w → s + j < k →
      let b_win := (b.drop s).take w
      let dp_old := lcsDpRow a_prev b_win
      let dp_new := lcsDpStep ch b_win dp_old
      (d_col_k.getD (s + j) 0 > j ↔
       dp_new.getD (j + 1) 0 > dp_new.getD j 0)) ∧
  -- Part C: untouched positions
  (∀ j, k ≤ j → d_col_k.getD j 0 = d_col_orig.getD j 0)

/-- d_row invariant: d_row_k tracks DP frontier at column k (for k > 0).
    For every window [s,s+w) containing column k:
      d_row_k > k-s  ↔  dp_new[k-s+1] > dp_new[k-s]
    This connects the comb's d_row value to the DP cell computation at position k.
    At k=0, the invariant is vacuously True (d_row hasn't yet interacted with the comb).

    **WARNING (discovered 2026-03-28):** This invariant is INCORRECTLY FORMULATED.
    The iff does NOT hold for all windows simultaneously. Counterexample:
      a_prev = [], ch = 1, b = [1, 2], d_row_init = 1
    After processing column 0 (match: ch=1=b[0]):
      d_row becomes dc+1 = 0+1 = 1
    DRowInv at k+1=1 for window [1,2) (s=1, w=1, j=0):
      LHS: 1 > 0 = True
      RHS: dp_new[1] > dp_new[0] where dp_new = lcsDpStep(1, [2], [0,0])
           = 0 > 0 = False
      iff fails: True ↔ False

    Exhaustive verification: DRowInv fails in 35.4% of 196,920 cases
    (alphabet {0,1,2}, |a_prev|<=3, |b|<=5). The underlying issue is that
    d_row is a global comb state that does not have a per-window iff
    relationship with the DP.

    However, ColSimInv Part A IS correct (verified: 1,176,201 cases, 0 failures).
    The proof just needs a different strategy for the new-position case (s+j=k).

    DRowInv is kept as-is for now to avoid restructuring the proof. The sorry's
    that produce DRowInv at k+1 (lines 1084, 1131, 1154) are UNPROVABLE because
    DRowInv at k+1 is false in general. The sorry's that consume DRowInv (Part A
    match/swap k>0) are valid uses of a false hypothesis provided by sorry. -/
def DRowInv (b : List ℕ) (a_prev : List ℕ) (ch : ℕ)
    (k : ℕ) (d_row_k : ℕ) : Prop :=
  0 < k →
  ∀ s w, s ≤ k → k < s + w → s + w ≤ b.length → w > 0 →
    let j := k - s
    let b_win := (b.drop s).take w
    let dp_old := lcsDpRow a_prev b_win
    let dp_new := lcsDpStep ch b_win dp_old
    (d_row_k > j ↔ dp_new.getD (j + 1) 0 > dp_new.getD j 0)

/-! ### Crossing Count Decomposition -/

/-- Crossing count successor: crossing count at width w+1 equals
    crossing count at width w plus the indicator at position w. -/
theorem crossingCount'_succ (d_col : List ℕ) (s w : ℕ) :
    crossingCount' d_col s (w + 1) = crossingCount' d_col s w +
    if d_col.getD (s + w) 0 > w then 1 else 0 := by
  unfold crossingCount'
  rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
  simp [Nat.add_zero]

/-- Per-position CombEncodes: from CombEncodes (aggregate crossing = LCS for all widths),
    derive per-position: d_col[s+j] > j iff LCS increases at position j.
    Specifically: d_col.getD (s+j) 0 > j iff
      lcsDp a (b.drop s |>.take (j+1)) > lcsDp a (b.drop s |>.take j)
    (where we set lcsDp a [] = 0 for the j=0 base case).

    Proof: CombEncodes gives crossingCount' at widths j and j+1.
    Their difference is the indicator at position j.
    The LCS difference is also 0 or 1 (non-decreasing + unit step).
    The two differences must be equal, so the indicators match. -/
theorem combEncodes_per_position (d_col : List ℕ) (b : List ℕ) (a : List ℕ)
    (henc : CombEncodes d_col b a)
    (s j : ℕ) (hsj : s + j < b.length) (hs1 : s + (j + 1) ≤ b.length) :
    (d_col.getD (s + j) 0 > j ↔
     lcsDp a (b.drop s |>.take (j + 1)) > lcsDp a (b.drop s |>.take j)) := by
  -- CombEncodes at width j+1
  have henc_succ := henc s (j + 1) hs1 (by omega)
  -- crossingCount' decomposition
  have hcc_succ := crossingCount'_succ d_col s j
  rw [hcc_succ] at henc_succ
  by_cases hj0 : j = 0
  · -- Base case: j = 0, follows from inductive case with j := 0 trick
    -- We use the same structure as the inductive case but with crossingCount' at width 0 = 0
    subst hj0
    simp only [Nat.add_zero] at henc_succ ⊢
    have hcc0 : crossingCount' d_col s 0 = 0 := by simp [crossingCount']
    rw [hcc0] at henc_succ
    simp only [Nat.zero_add] at henc_succ
    -- henc_succ: (if d_col.getD s 0 > 0 then 1 else 0) = lcsDp a (take 1 ...)
    -- Goal: d_col.getD s 0 > 0 ↔ lcsDp a (take 1 ...) > lcsDp a (take 0 ...)
    -- lcsDp a (take 0 ...) = lcsDp a [] = 0 (LCS of anything vs empty is 0)
    have hlcs_empty : ∀ (a' : List ℕ), lcsDp a' [] = 0 := by
      intro a'; induction a' with
      | nil => simp [lcsDp]
      | cons _ rest ih => simp [lcsDp, lcsDpStep]; exact ih
    simp only [List.take_zero]
    rw [hlcs_empty a]
    set lcs1 := lcsDp a (List.take 1 (List.drop s b)) with hlcs1_def
    split_ifs at henc_succ with h
    · -- h: d_col.getD s 0 > 0, henc_succ: 1 = lcs1
      constructor
      · intro _; omega
      · intro _; exact h
    · -- ¬h: ¬(d_col.getD s 0 > 0), henc_succ: 0 = lcs1
      constructor
      · intro habs; exact absurd habs h
      · intro habs; omega
  · -- Inductive case: j > 0
    have hj_pos : j > 0 := by omega
    have henc_j := henc s j (by omega) hj_pos
    rw [henc_j] at henc_succ
    -- henc_succ: lcsDp(take j) + indicator = lcsDp(take (j+1))
    split_ifs at henc_succ with h
    · -- indicator = 1, so lcsDp(j+1) = lcsDp(j) + 1
      constructor
      · intro _; omega
      · intro _; exact h
    · -- indicator = 0, so lcsDp(j+1) = lcsDp(j)
      constructor
      · intro habs; exact absurd habs h
      · intro habs; omega

/-! ### List.set helper lemmas -/

/-- getD of List.set at a different index returns the original value. -/
private theorem getD_set_ne (l : List ℕ) (i j : ℕ) (v d : ℕ) (h : i ≠ j) :
    (l.set i v).getD j d = l.getD j d := by
  simp [List.getD, List.getElem?_set, show ¬(i = j) from h]

/-- getD of List.set at the same index returns the new value (if in bounds). -/
private theorem getD_set_eq (l : List ℕ) (i : ℕ) (v d : ℕ) (h : i < l.length) :
    (l.set i v).getD i d = v := by
  simp [List.getD, List.getElem?_set, Nat.sub_self, h]

/-! ### Sub-lemmas for the column invariant -/

/-- Helper: getD at index k of lcsDpStepPartial n, for k < n,
    equals getD at index k of lcsDpStepPartial (k+1).
    (Later columns don't change earlier values because we only append.) -/
private theorem lcsDpStepPartial_getD_stable (ai : ℕ) (b_win prev : List ℕ)
    (k n : ℕ) (hkn : k < n) :
    (lcsDpStepPartial ai b_win prev n).getD k 0 =
    (lcsDpStepPartial ai b_win prev (k + 1)).getD k 0 := by
  induction n with
  | zero => omega
  | succ n' ih =>
    by_cases h : k < n'
    · rw [lcsDpStepPartial_succ]
      simp only [List.getD]
      rw [List.getElem?_append_left (by rw [lcsDpStepPartial_length]; omega)]
      rw [← List.getD]
      exact ih h
    · have : n' = k := by omega
      subst this; rfl

/-- Helper: the value at position k+1 of lcsDpStepPartial (k+1). -/
private theorem lcsDpStepPartial_last (ai : ℕ) (b_win prev : List ℕ) (k : ℕ) :
    (lcsDpStepPartial ai b_win prev (k + 1)).getD (k + 1) 0 =
    if ai == b_win.getD k 0 then prev.getD k 0 + 1
    else max (prev.getD (k + 1) 0) ((lcsDpStepPartial ai b_win prev k).getD k 0) := by
  rw [lcsDpStepPartial_succ]
  have hlen := lcsDpStepPartial_length ai b_win prev k
  simp only [List.getD]
  rw [List.getElem?_append_right (by omega)]
  simp [hlen, Nat.sub_self]

/-- Helper: the value at position k of lcsDpStepPartial (k+1) equals
    the value at position k of lcsDpStepPartial k (= previous step value). -/
private theorem lcsDpStepPartial_prev_at (ai : ℕ) (b_win prev : List ℕ) (k : ℕ) :
    (lcsDpStepPartial ai b_win prev (k + 1)).getD k 0 =
    (lcsDpStepPartial ai b_win prev k).getD k 0 := by
  rw [lcsDpStepPartial_succ]
  have hlen := lcsDpStepPartial_length ai b_win prev k
  simp only [List.getD]
  rw [List.getElem?_append_left (by omega)]

/-! ### DP Prefix Locality

The DP value at position j only depends on b_win[0..j-1] and prev[0..j].
This lets us prove lcsDpRow_getD_prefix: dp[j] = lcsDp(a, b_win.take j). -/

/-- Helper: lcsDpStepPartial is determined by b_win and prev at positions below k.
    If two reference lists and two prev lists agree at the relevant positions,
    the partial DP results are identical. -/
private theorem lcsDpStepPartial_of_agree (ch : ℕ) (b1 b2 prev1 prev2 : List ℕ)
    (k : ℕ)
    (hb : ∀ i, i < k → b1.getD i 0 = b2.getD i 0)
    (hp : ∀ i, i ≤ k → prev1.getD i 0 = prev2.getD i 0) :
    lcsDpStepPartial ch b1 prev1 k = lcsDpStepPartial ch b2 prev2 k := by
  induction k with
  | zero => simp [lcsDpStepPartial_zero]
  | succ k' ih =>
    rw [lcsDpStepPartial_succ, lcsDpStepPartial_succ]
    have ih' := ih (fun i hi => hb i (by omega)) (fun i hi => hp i (by omega))
    rw [ih']
    -- Goal: curr ++ [val1] = curr ++ [val2]
    -- val1 uses b1.getD k' and prev1.getD, val2 uses b2.getD k' and prev2.getD
    have hbk : b1.getD k' 0 = b2.getD k' 0 := hb k' (by omega)
    have hpk : prev1.getD k' 0 = prev2.getD k' 0 := hp k' (by omega)
    have hpk1 : prev1.getD (k' + 1) 0 = prev2.getD (k' + 1) 0 := hp (k' + 1) (by omega)
    rw [hbk, hpk, hpk1]

/-- Helper: List.take preserves getD at positions below the take index. -/
private theorem getD_take_lt (l : List ℕ) (n i : ℕ) (hi : i < n) :
    (l.take n).getD i 0 = l.getD i 0 := by
  simp only [List.getD]
  by_cases hil : i < l.length
  · have hitn : i < (l.take n).length := by simp [List.length_take]; omega
    rw [List.getElem?_eq_getElem hitn, List.getElem?_eq_getElem hil]
    simp only [Option.getD_some, List.getElem_take]
  · have h1 : l[i]? = none := List.getElem?_eq_none (by omega)
    have h2 : (l.take n)[i]? = none :=
      List.getElem?_eq_none (by simp [List.length_take]; omega)
    rw [h1, h2]

/-- Stronger locality: the lcsDpRow folds on b_win and b_win.take j agree
    at ALL positions 0..j. Proved by induction on the query list `l`. -/
private theorem lcsDpRow_foldl_agree (l : List ℕ) (b_win : List ℕ) (j : ℕ)
    (hj : j ≤ b_win.length)
    (init1 init2 : List ℕ)
    (hinit_agree : ∀ i, i ≤ j → init1.getD i 0 = init2.getD i 0) :
    ∀ i, i ≤ j →
      (l.foldl (fun prev ai => lcsDpStep ai b_win prev) init1).getD i 0 =
      (l.foldl (fun prev ai => lcsDpStep ai (b_win.take j) prev) init2).getD i 0 := by
  induction l generalizing init1 init2 with
  | nil => simpa using hinit_agree
  | cons ch rest ih =>
    simp only [List.foldl]
    apply ih
    intro i hi
    rw [lcsDpStep_eq_partial, lcsDpStep_eq_partial]
    simp only [List.length_take]; rw [Nat.min_eq_left (by omega)]
    by_cases hij : i < j
    · rw [lcsDpStepPartial_getD_stable ch b_win init1 i b_win.length (by omega)]
      rw [lcsDpStepPartial_getD_stable ch (b_win.take j) init2 i j hij]
      have heq := lcsDpStepPartial_of_agree ch b_win (b_win.take j) init1 init2 (i + 1)
        (fun k hk => (getD_take_lt b_win j k (by omega)).symm)
        (fun k hk => hinit_agree k (by omega))
      rw [heq]
    · -- i = j case
      have hieq : i = j := by omega
      rw [hieq]
      -- Reduce left side from (partial b_win.length) to (partial j) when j < b_win.length
      -- When j = b_win.length, they're already the same
      suffices hleft : (lcsDpStepPartial ch b_win init1 b_win.length).getD j 0 =
          (lcsDpStepPartial ch b_win init1 j).getD j 0 by
        rw [hleft]
        have heq := lcsDpStepPartial_of_agree ch b_win (b_win.take j) init1 init2 j
          (fun k hk => (getD_take_lt b_win j k (by omega)).symm)
          (fun k hk => hinit_agree k (by omega))
        rw [heq]
      by_cases hjlt : j < b_win.length
      · rw [lcsDpStepPartial_getD_stable ch b_win init1 j b_win.length hjlt]
        exact lcsDpStepPartial_prev_at ch b_win init1 j
      · have : j = b_win.length := by omega
        rw [this]

/-- lcsDpRow prefix property: dp[j] = lcsDp(a, b_win[0:j]).
    The DP value at position j only depends on the first j characters of b_win.
    Verified exhaustively: 2,240 cases, 0 failures (alphabet {0,1}, |a|≤2, |b|≤4). -/
theorem lcsDpRow_getD_prefix (a : List ℕ) (b_win : List ℕ) (j : ℕ)
    (hj : j ≤ b_win.length) :
    (lcsDpRow a b_win).getD j 0 = lcsDp a (b_win.take j) := by
  suffices h : (lcsDpRow a b_win).getD j 0 = (lcsDpRow a (b_win.take j)).getD j 0 by
    rw [h, ← lcsDpRow_getD_eq_lcsDp]
    congr 1
    simp [List.length_take]; omega
  exact lcsDpRow_foldl_agree a b_win j hj
    (List.replicate (b_win.length + 1) 0)
    (List.replicate ((b_win.take j).length + 1) 0)
    (fun i _ => by rw [getD_replicate_zero, getD_replicate_zero])
    j (le_refl j)

/-- All properties of lcsDpStepPartial proved together by induction on k.

    At each step k, the computed value dp[k+1] satisfies:
    (1) Non-decreasing: dp[k+1] ≥ dp[k]
    (2) Unit increase: dp[k+1] ≤ dp[k] + 1
    (3) prev dominance: dp[k+1] ≥ prev[k+1]

    Note: (3) is needed for the inductive proof of (1) and (2).
    The match case of (1) needs prev[k] ≥ dp[k] - 1, which follows from
    (3) at the previous step: dp[k] ≥ prev[k] ⟹ prev[k] + 1 ≥ dp[k].
    And (2) match case needs prev[k] ≤ dp[k], also from (3).

    For (3) in the mismatch case: max(prev[k+1], dp[k]) ≥ prev[k+1] trivially.
    For (3) in the match case: prev[k] + 1 ≥ prev[k+1] needs prev unit increase
    (which follows from prev being non-decreasing AND prev[k+1] ≤ prev[k] + 1,
     i.e., prev satisfies unit increase — guaranteed when prev is an LCS DP row). -/
private theorem lcsDpStepPartial_properties (ai : ℕ) (b_win prev : List ℕ)
    (hprev_nd : ∀ i, i < b_win.length → prev.getD (i + 1) 0 ≥ prev.getD i 0)
    (hprev_unit : ∀ i, i < b_win.length → prev.getD (i + 1) 0 ≤ prev.getD i 0 + 1)
    (hprev_zero : prev.getD 0 0 = 0)
    (k : ℕ) (hk : k < b_win.length) :
    -- Non-decreasing
    (lcsDpStepPartial ai b_win prev (k + 1)).getD (k + 1) 0 ≥
    (lcsDpStepPartial ai b_win prev (k + 1)).getD k 0
    -- Unit increase
    ∧ (lcsDpStepPartial ai b_win prev (k + 1)).getD (k + 1) 0 ≤
      (lcsDpStepPartial ai b_win prev (k + 1)).getD k 0 + 1
    -- Prev dominance (dp_new[k+1] ≥ prev[k+1])
    ∧ (lcsDpStepPartial ai b_win prev (k + 1)).getD (k + 1) 0 ≥
      prev.getD (k + 1) 0
    -- Prev upper bound (dp_new[k+1] ≤ prev[k+1] + 1)
    ∧ (lcsDpStepPartial ai b_win prev (k + 1)).getD (k + 1) 0 ≤
      prev.getD (k + 1) 0 + 1 := by
  rw [lcsDpStepPartial_last, lcsDpStepPartial_prev_at]
  -- dp_k = (lcsDpStepPartial ... k).getD k 0 = the value at position k of the partial
  -- Get prev dominance at position k (for k > 0, from induction; for k = 0, dp[0] = 0 ≤ prev[0])
  have hprev_dom_k : (lcsDpStepPartial ai b_win prev k).getD k 0 ≥ prev.getD k 0 := by
    cases k with
    | zero =>
      simp only [lcsDpStepPartial_zero, List.getD, List.getElem?_cons_zero, Option.getD_some]
      rw [← List.getD, hprev_zero]
    | succ k' =>
      exact (lcsDpStepPartial_properties ai b_win prev hprev_nd hprev_unit hprev_zero k' (by omega)).2.2.1
  have hprev_ub_k : (lcsDpStepPartial ai b_win prev k).getD k 0 ≤ prev.getD k 0 + 1 := by
    cases k with
    | zero =>
      simp only [lcsDpStepPartial_zero, List.getD, List.getElem?_cons_zero, Option.getD_some]
      omega
    | succ k' =>
      exact (lcsDpStepPartial_properties ai b_win prev hprev_nd hprev_unit hprev_zero k' (by omega)).2.2.2
  split
  · -- match case: val = prev[k] + 1
    rename_i hmatch
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Non-decreasing: prev[k] + 1 ≥ dp_k. From hprev_ub_k: dp_k ≤ prev[k] + 1.
      omega
    · -- Unit increase: prev[k] + 1 ≤ dp_k + 1. From prev_dom: dp_k ≥ prev[k].
      omega
    · -- Prev dominance: prev[k] + 1 ≥ prev[k+1]. From prev unit increase.
      have := hprev_unit k hk; omega
    · -- Prev upper bound: prev[k] + 1 ≤ prev[k+1] + 1. From prev non-decreasing.
      have := hprev_nd k hk; omega
  · -- mismatch case: val = max(prev[k+1], dp_k)
    rename_i hmismatch
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Non-decreasing: max(prev[k+1], dp_k) ≥ dp_k
      exact le_max_right _ _
    · -- Unit increase: max(prev[k+1], dp_k) ≤ dp_k + 1
      apply Nat.max_le.mpr
      constructor
      · have h1 := hprev_unit k hk; omega
      · omega
    · -- Prev dominance: max(prev[k+1], dp_k) ≥ prev[k+1]
      exact le_max_left _ _
    · -- Prev upper bound: max(prev[k+1], dp_k) ≤ prev[k+1] + 1
      apply Nat.max_le.mpr
      constructor
      · omega
      · have := hprev_nd k hk; omega

/-- lcsDpStep produces a non-decreasing sequence.
    dp_new[j+1] ≥ dp_new[j] for all j.
    (This is because LCS(a, b[0:j+1]) ≥ LCS(a, b[0:j]).) -/
theorem lcsDpStep_nondecreasing (ai : ℕ) (b_win : List ℕ) (prev : List ℕ)
    (j : ℕ) (hj : j < b_win.length)
    (hprev_len : prev.length = b_win.length + 1)
    (hprev_nd : ∀ i, i < b_win.length → prev.getD (i + 1) 0 ≥ prev.getD i 0)
    (hprev_unit : ∀ i, i < b_win.length → prev.getD (i + 1) 0 ≤ prev.getD i 0 + 1)
    (hprev_zero : prev.getD 0 0 = 0) :
    (lcsDpStep ai b_win prev).getD (j + 1) 0 ≥
    (lcsDpStep ai b_win prev).getD j 0 := by
  rw [lcsDpStep_eq_partial]
  rw [lcsDpStepPartial_getD_stable ai b_win prev j b_win.length hj]
  by_cases hjp : j + 1 < b_win.length
  · rw [lcsDpStepPartial_getD_stable ai b_win prev (j + 1) b_win.length hjp,
        lcsDpStepPartial_prev_at]
    exact (lcsDpStepPartial_properties ai b_win prev hprev_nd hprev_unit hprev_zero j hj).1
  · have hjeq : j + 1 = b_win.length := by omega
    rw [← hjeq]
    exact (lcsDpStepPartial_properties ai b_win prev hprev_nd hprev_unit hprev_zero j hj).1

/-- lcsDpRow has length b_win.length + 1. -/
theorem lcsDpRow_length (a : List ℕ) (b_win : List ℕ) :
    (lcsDpRow a b_win).length = b_win.length + 1 := by
  simp only [lcsDpRow]
  suffices gen : ∀ (l : List ℕ) (init : List ℕ),
      init.length = b_win.length + 1 →
      (l.foldl (fun prev ai => lcsDpStep ai b_win prev) init).length = b_win.length + 1 from
    gen a _ (by simp)
  intro l
  induction l with
  | nil => intro init h; simpa
  | cons ch rest ih =>
    intro init hinit
    simp only [List.foldl]
    exact ih (lcsDpStep ch b_win init)
      (by rw [lcsDpStep_eq_partial]; exact lcsDpStepPartial_length ch b_win init b_win.length)

/-- lcsDpStep has length b_win.length + 1. -/
theorem lcsDpStep_length (ai : ℕ) (b_win : List ℕ) (prev : List ℕ) :
    (lcsDpStep ai b_win prev).length = b_win.length + 1 := by
  rw [lcsDpStep_eq_partial]; exact lcsDpStepPartial_length ai b_win prev b_win.length

/-- lcsDpStep starts at 0: dp_new[0] = 0. -/
theorem lcsDpStep_zero (ai : ℕ) (b_win : List ℕ) (prev : List ℕ) :
    (lcsDpStep ai b_win prev).getD 0 0 = 0 := by
  rw [lcsDpStep_eq_partial]
  have h : ∀ k, (lcsDpStepPartial ai b_win prev k).getD 0 0 = 0 := by
    intro k
    induction k with
    | zero => simp [lcsDpStepPartial_zero]
    | succ k' ih =>
      rw [lcsDpStepPartial_succ]
      have hlen : (lcsDpStepPartial ai b_win prev k').length = k' + 1 :=
        lcsDpStepPartial_length ai b_win prev k'
      simp only [List.getD]
      rw [List.getElem?_append_left (by omega)]
      rw [← List.getD]
      exact ih
  exact h b_win.length

/-- lcsDpRow starts at 0: dp[0] = 0. -/
theorem lcsDpRow_zero (a : List ℕ) (b_win : List ℕ) :
    (lcsDpRow a b_win).getD 0 0 = 0 := by
  simp only [lcsDpRow]
  suffices gen : ∀ (l : List ℕ) (init : List ℕ),
      init.getD 0 0 = 0 → init.length = b_win.length + 1 →
      (l.foldl (fun prev ai => lcsDpStep ai b_win prev) init).getD 0 0 = 0 from
    gen a _ (by simp [getD_replicate_zero]) (by simp)
  intro l
  induction l with
  | nil => intro init h _; simpa
  | cons ch rest ih =>
    intro init hinit hlen
    simp only [List.foldl]
    exact ih (lcsDpStep ch b_win init)
      (lcsDpStep_zero ch b_win init)
      (lcsDpStep_length ch b_win init)

/-- The crossing count of a non-decreasing sequence starting at 0 equals
    its final value. More precisely:
    #{j ∈ [0,n) : seq[j+1] > seq[j]} = seq[n] - seq[0]
    when seq is non-decreasing and each step increases by at most 1. -/
theorem countP_increases_eq_final (seq : List ℕ) (n : ℕ)
    (hlen : seq.length ≥ n + 1)
    (hnd : ∀ j, j < n → seq.getD (j + 1) 0 ≥ seq.getD j 0)
    (hstep : ∀ j, j < n → seq.getD (j + 1) 0 ≤ seq.getD j 0 + 1) :
    (List.range n).countP (fun j => decide (seq.getD (j + 1) 0 > seq.getD j 0)) =
    seq.getD n 0 - seq.getD 0 0 := by
  have hge : ∀ i j, i ≤ j → j ≤ n → seq.getD j 0 ≥ seq.getD i 0 := by
    intro i j hij hjn
    induction j with
    | zero =>
      have hi0 : i = 0 := by omega
      subst hi0; exact le_refl _
    | succ j' ihj =>
      by_cases h : i ≤ j'
      · calc seq.getD (j' + 1) 0 ≥ seq.getD j' 0 := hnd j' (by omega)
             _ ≥ seq.getD i 0 := ihj h (by omega)
      · have hi : i = j' + 1 := by omega
        subst hi; exact le_refl _
  induction n with
  | zero => simp
  | succ n' ih =>
    have ih_val := ih (by omega) (fun j hj => hnd j (by omega)) (fun j hj => hstep j (by omega))
      (fun i j hij hjn => hge i j hij (by omega))
    have hnd_n := hnd n' (by omega)
    have hstep_n := hstep n' (by omega)
    have hge_0_n' := hge 0 n' (by omega) (by omega)
    have hsplit : (List.range (n' + 1)).countP
        (fun j => decide (seq.getD (j + 1) 0 > seq.getD j 0)) =
        (List.range n').countP
          (fun j => decide (seq.getD (j + 1) 0 > seq.getD j 0)) +
        (if seq.getD (n' + 1) 0 > seq.getD n' 0 then 1 else 0) := by
      rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]; simp
    rw [hsplit, ih_val]
    by_cases h : seq.getD (n' + 1) 0 > seq.getD n' 0
    · rw [if_pos h]
      have heq : seq.getD (n' + 1) 0 = seq.getD n' 0 + 1 := by omega
      omega
    · rw [if_neg h]
      have heq : seq.getD (n' + 1) 0 = seq.getD n' 0 := by omega
      omega

/-- lcsDpStep produces at-most-unit increases.
    dp_new[j+1] ≤ dp_new[j] + 1. -/
theorem lcsDpStep_unit_increase (ai : ℕ) (b_win : List ℕ) (prev : List ℕ)
    (j : ℕ) (hj : j < b_win.length)
    (hprev_nd : ∀ i, i < b_win.length → prev.getD (i + 1) 0 ≥ prev.getD i 0)
    (hprev_unit : ∀ i, i < b_win.length → prev.getD (i + 1) 0 ≤ prev.getD i 0 + 1)
    (hprev_zero : prev.getD 0 0 = 0) :
    (lcsDpStep ai b_win prev).getD (j + 1) 0 ≤
    (lcsDpStep ai b_win prev).getD j 0 + 1 := by
  rw [lcsDpStep_eq_partial]
  rw [lcsDpStepPartial_getD_stable ai b_win prev j b_win.length hj]
  by_cases hjp : j + 1 < b_win.length
  · rw [lcsDpStepPartial_getD_stable ai b_win prev (j + 1) b_win.length hjp,
        lcsDpStepPartial_prev_at]
    exact (lcsDpStepPartial_properties ai b_win prev hprev_nd hprev_unit hprev_zero j hj).2.1
  · have hjeq : j + 1 = b_win.length := by omega
    rw [← hjeq]
    exact (lcsDpStepPartial_properties ai b_win prev hprev_nd hprev_unit hprev_zero j hj).2.1

/-- Helper: all DP row properties are preserved through the fold. -/
theorem lcsDpRow_fold_props (l : List ℕ) (b_win : List ℕ) (init : List ℕ)
    (hinit_len : init.length = b_win.length + 1)
    (hinit_nd : ∀ i, i < b_win.length → init.getD (i + 1) 0 ≥ init.getD i 0)
    (hinit_unit : ∀ i, i < b_win.length → init.getD (i + 1) 0 ≤ init.getD i 0 + 1)
    (hinit_zero : init.getD 0 0 = 0) :
    let result := l.foldl (fun prev ai => lcsDpStep ai b_win prev) init
    (∀ j, j < b_win.length → result.getD (j + 1) 0 ≥ result.getD j 0) ∧
    (∀ j, j < b_win.length → result.getD (j + 1) 0 ≤ result.getD j 0 + 1) ∧
    result.getD 0 0 = 0 ∧
    result.length = b_win.length + 1 := by
  induction l generalizing init with
  | nil => exact ⟨hinit_nd, hinit_unit, hinit_zero, hinit_len⟩
  | cons ch rest ih =>
    simp only [List.foldl]
    apply ih
    · exact lcsDpStep_length ch b_win init
    · intro i hi; exact lcsDpStep_nondecreasing ch b_win init i hi hinit_len hinit_nd hinit_unit hinit_zero
    · intro i hi; exact lcsDpStep_unit_increase ch b_win init i hi hinit_nd hinit_unit hinit_zero
    · exact lcsDpStep_zero ch b_win init

/-- lcsDpRow produces a non-decreasing sequence. -/
theorem lcsDpRow_nondecreasing (a : List ℕ) (b_win : List ℕ)
    (j : ℕ) (hj : j < b_win.length) :
    (lcsDpRow a b_win).getD (j + 1) 0 ≥ (lcsDpRow a b_win).getD j 0 := by
  have h := lcsDpRow_fold_props a b_win (List.replicate (b_win.length + 1) 0)
    (by simp)
    (by intro i _; rw [getD_replicate_zero, getD_replicate_zero])
    (by intro i _; rw [getD_replicate_zero, getD_replicate_zero]; omega)
    (by exact getD_replicate_zero _ _)
  exact h.1 j hj

/-- lcsDpRow produces at-most-unit increases. -/
theorem lcsDpRow_unit_increase (a : List ℕ) (b_win : List ℕ)
    (j : ℕ) (hj : j < b_win.length) :
    (lcsDpRow a b_win).getD (j + 1) 0 ≤ (lcsDpRow a b_win).getD j 0 + 1 := by
  have h := lcsDpRow_fold_props a b_win (List.replicate (b_win.length + 1) 0)
    (by simp)
    (by intro i _; rw [getD_replicate_zero, getD_replicate_zero])
    (by intro i _; rw [getD_replicate_zero, getD_replicate_zero]; omega)
    (by exact getD_replicate_zero _ _)
  exact h.2.1 j hj

/-! ### The d_row Invariant (DRowProp) — Key to closing all 3 sorry's

**Discovery (Phase 02.3):** The correct d_row invariant is NOT the original DRowInv
  (d_row > j iff dp_new[j+1] > dp_new[j] — fails 35.4%)
but rather:
  d_row > j iff dp_new[j] = dp_old[j]

i.e., d_row exceeds the window offset j iff adding character ch does NOT increase
the LCS within the first j characters of any window starting at position k−j.

Verified exhaustively: |a_prev| ≤ 3, |b| ≤ 5, alphabet {0,1,2}: 1,252,080 cases, 0 failures.

**How DRowProp closes all 3 sorry's:**

Match case (d_row_k stored):
  dp_new[j+1] = dp_old[j]+1 (match DP cell)
  dp_new[j+1] > dp_new[j] ↔ dp_old[j]+1 > dp_new[j] ↔ dp_new[j] = dp_old[j] ↔ d_row_k > j ∎

Swap case (d_row_k stored, mismatch):
  dp_new[j+1] = max(dp_old[j+1], dp_new[j])
  If d_row_k > j: dp_new[j] = dp_old[j], so dp_new[j+1] = max(dp_old[j+1], dp_old[j]) > dp_old[j] ↔ dp_old[j+1] > dp_old[j]
  If d_row_k ≤ j: dp_new[j] = dp_old[j]+1, dp_old[j+1] ≤ dp_old[j]+1, so max ≤ dp_new[j] → no increase

Stay case (d_col_orig[k] unchanged):
  By CombEncodes: d_col_orig[k] > j ↔ dp_old[j+1] > dp_old[j]
  Case dp_new[j] = dp_old[j]: dp_new[j+1] > dp_new[j] ↔ dp_old[j+1] > dp_old[j] ∎
  Case dp_new[j] = dp_old[j]+1: d_row_k ≤ j (DRowProp contrapositive), dc ≤ d_row_k (stay),
    so dc ≤ j → d_col_orig[k] ≤ j → dp_old[j+1] = dp_old[j] → both sides False ∎
-/

/-- The d_row invariant: d_row > j iff the new DP agrees with old DP at position j. -/
def DRowProp (b : List ℕ) (a_prev : List ℕ) (ch : ℕ)
    (k : ℕ) (d_row_k : ℕ) : Prop :=
  ∀ s w, s ≤ k → k < s + w → s + w ≤ b.length → w > 0 →
    let j := k - s
    let b_win := (b.drop s).take w
    let dp_old := lcsDpRow a_prev b_win
    let dp_new := lcsDpStep ch b_win dp_old
    (d_row_k > j ↔ dp_new.getD j 0 = dp_old.getD j 0)

/-- DRowProp is maintained through processRow. The invariant is carried alongside ColSimInv.
    Induction on k with three colStep sub-cases (match, swap, stay).
    Base (k=0): d_row = dr_init > 0, j=0, dpn[0]=dpo[0]=0.
    Step (k→k+1): Uses CombEncodes per-position, DP cell recurrence, and DP monotonicity bounds.
    Match/Swap: dpn[j] = dpo[j-1]+1 (match) or max(dpo[j], dpn[j-1]) (swap).
    Stay: case split on dpn[j-1] = dpo[j-1] vs not, using IH contrapositive + CombEncodes. -/
theorem drow_processRow (ch : ℕ) (b : List ℕ) (d_col : List ℕ)
    (a_prev : List ℕ) (dr_init : ℕ)
    (henc : CombEncodes d_col b a_prev)
    (hlen : d_col.length = b.length)
    (hdr_init : 0 < dr_init)
    (k : ℕ) (hk : k ≤ b.length) :
    DRowProp b a_prev ch k (processRowPartial ch b d_col dr_init k).2 := by
  induction k with
  | zero =>
    rw [processRowPartial_zero]
    unfold DRowProp
    intro s w hs hk hsw hw
    have hs0 : s = 0 := by omega
    subst hs0
    simp only [Nat.zero_sub]
    constructor
    · intro _; rw [lcsDpStep_zero, lcsDpRow_zero]
    · intro _; exact hdr_init
  | succ k' ih =>
    have ih' := ih (by omega)
    rw [processRowPartial_succ]
    simp only [colFoldStep, colStep]
    unfold DRowProp
    intro s w hs hk hsw hw
    set prp := processRowPartial ch b d_col dr_init k' with hprp_def
    set dc := prp.1.getD k' 0 with hdc_def
    set dr := prp.2 with hdr_def
    have hdc_eq : dc = d_col.getD k' 0 := by
      rw [hdc_def, processRowPartial_getD_ge ch b d_col dr_init k' k' (le_refl _) (by omega) hlen]
    simp only
    split_ifs with hmatch hswap
    · -- Match case: new d_row = dc + 1
      -- Goal: dc + 1 > k'+1-s ↔ dpn[k'+1-s] = dpo[k'+1-s]
      -- Chain: dc+1 > p+1 ↔ dc > p ↔ dpo[p+1] > dpo[p] ↔ dpo[p]+1 = dpo[p+1]
      --   ↔ dpo[p]+1 = dpn[p+1] (match: dpn[p+1] = dpo[p]+1)
      simp only
      by_cases hsj : s = k' + 1
      · subst hsj; simp only [Nat.sub_self]
        constructor
        · intro _; rw [lcsDpStep_zero, lcsDpRow_zero]
        · intro _; omega
      · set j := k' + 1 - s with hj_def
        set p := k' - s with hp_def
        have hpj : j = p + 1 := by omega
        have hsk'p : s + p = k' := by omega
        rw [hpj]
        set b_win := (b.drop s).take w with hbw_def
        have hbw_len : b_win.length = w := by
          rw [hbw_def, List.length_take, List.length_drop]; omega
        have hce2 : dc > p ↔ (lcsDpRow a_prev b_win).getD (p + 1) 0 >
            (lcsDpRow a_prev b_win).getD p 0 := by
          have hpfx1 : (lcsDpRow a_prev b_win).getD (p + 1) 0 =
              lcsDp a_prev (List.take (p + 1) (List.drop s b)) := by
            rw [hbw_def, lcsDpRow_getD_prefix a_prev _ (p + 1) (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have hpfx0 : (lcsDpRow a_prev b_win).getD p 0 =
              lcsDp a_prev (List.take p (List.drop s b)) := by
            rw [hbw_def, lcsDpRow_getD_prefix a_prev _ p (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have h := combEncodes_per_position d_col b a_prev henc s p (by omega) (by omega)
          rw [hsk'p] at h; rw [hdc_eq, hpfx1, hpfx0]; exact h
        have hdpo_nd := lcsDpRow_nondecreasing a_prev b_win p (by rw [hbw_len]; omega)
        have hdpo_unit := lcsDpRow_unit_increase a_prev b_win p (by rw [hbw_len]; omega)
        have hbwp : b_win.getD p 0 = b.getD k' 0 := by
          simp only [hbw_def, List.getD]
          rw [List.getElem?_eq_getElem (by rw [List.length_take, List.length_drop]; omega)]
          simp only [Option.getD_some, List.getElem_take, List.getElem_drop]
          rw [List.getElem?_eq_getElem (by omega : k' < b.length)]
          simp [hsk'p]
        have hmatch_bw : (ch == b_win.getD p 0) = true := by rw [hbwp]; exact hmatch
        have hcell : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD (p + 1) 0 =
            (lcsDpRow a_prev b_win).getD p 0 + 1 := by
          rw [lcsDpStep_eq_partial, hbw_len]
          by_cases hpw : p + 1 < w
          · rw [lcsDpStepPartial_getD_stable _ _ _ (p+1) w hpw, lcsDpStepPartial_prev_at,
                lcsDpStepPartial_last, if_pos hmatch_bw]
          · have hpeq : p + 1 = w := by omega
            rw [show w = p + 1 from hpeq.symm, lcsDpStepPartial_last, if_pos hmatch_bw]
        constructor
        · intro hgt
          have hdc_gt : dc > p := by omega
          have hdpo_inc := hce2.mp hdc_gt
          rw [hcell]; omega
        · intro heq
          rw [hcell] at heq
          have hdpo_inc : (lcsDpRow a_prev b_win).getD (p + 1) 0 >
              (lcsDpRow a_prev b_win).getD p 0 := by omega
          have hdc_gt := hce2.mpr hdpo_inc
          omega
    · -- Swap case: new d_row = dc + 1 (identical to match)
      simp only
      by_cases hsj : s = k' + 1
      · subst hsj; simp only [Nat.sub_self]
        constructor
        · intro _; rw [lcsDpStep_zero, lcsDpRow_zero]
        · intro _; omega
      · set j := k' + 1 - s with hj_def
        set p := k' - s with hp_def
        have hpj : j = p + 1 := by omega
        have hsk'p : s + p = k' := by omega
        rw [hpj]
        set b_win := (b.drop s).take w with hbw_def
        have hbw_len : b_win.length = w := by
          rw [hbw_def, List.length_take, List.length_drop]; omega
        have hce2 : dc > p ↔ (lcsDpRow a_prev b_win).getD (p + 1) 0 >
            (lcsDpRow a_prev b_win).getD p 0 := by
          have hpfx1 : (lcsDpRow a_prev b_win).getD (p + 1) 0 =
              lcsDp a_prev (List.take (p + 1) (List.drop s b)) := by
            rw [hbw_def, lcsDpRow_getD_prefix a_prev _ (p + 1) (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have hpfx0 : (lcsDpRow a_prev b_win).getD p 0 =
              lcsDp a_prev (List.take p (List.drop s b)) := by
            rw [hbw_def, lcsDpRow_getD_prefix a_prev _ p (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have h := combEncodes_per_position d_col b a_prev henc s p (by omega) (by omega)
          rw [hsk'p] at h; rw [hdc_eq, hpfx1, hpfx0]; exact h
        have hdpo_nd := lcsDpRow_nondecreasing a_prev b_win p (by rw [hbw_len]; omega)
        have hdpo_unit := lcsDpRow_unit_increase a_prev b_win p (by rw [hbw_len]; omega)
        -- Swap: mismatch, so DP cell = max(dpo[p+1], dpn[p])
        -- But the d_row is still dc + 1, same iff as match
        -- We show: dc > p ↔ dpo[p+1] > dpo[p] ↔ dpn[p+1] = dpo[p+1]
        -- using DRowProp IH (dr > p ↔ dpn[p] = dpo[p]) and bounds
        have hbwp : b_win.getD p 0 = b.getD k' 0 := by
          simp only [hbw_def, List.getD]
          rw [List.getElem?_eq_getElem (by rw [List.length_take, List.length_drop]; omega)]
          simp only [Option.getD_some, List.getElem_take, List.getElem_drop]
          rw [List.getElem?_eq_getElem (by omega : k' < b.length)]
          simp [hsk'p]
        have hmismatch_bw : ¬(ch == b_win.getD p 0) = true := by rw [hbwp]; exact hmatch
        -- dpn[p] bounds
        have hdom : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 ≥
            (lcsDpRow a_prev b_win).getD p 0 := by
          by_cases hp0 : p = 0
          · rw [hp0, lcsDpRow_zero a_prev b_win, lcsDpStep_zero]
          · rw [show p = (p - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
            rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
            exact (lcsDpStepPartial_properties ch _ _
              (fun i hi => lcsDpRow_nondecreasing a_prev _ i hi)
              (fun i hi => lcsDpRow_unit_increase a_prev _ i hi)
              (lcsDpRow_zero a_prev _) (p-1) (by omega)).2.2.1
        have hub : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 ≤
            (lcsDpRow a_prev b_win).getD p 0 + 1 := by
          by_cases hp0 : p = 0
          · rw [hp0, lcsDpRow_zero a_prev b_win, lcsDpStep_zero]; omega
          · rw [show p = (p - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
            rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
            exact (lcsDpStepPartial_properties ch _ _
              (fun i hi => lcsDpRow_nondecreasing a_prev _ i hi)
              (fun i hi => lcsDpRow_unit_increase a_prev _ i hi)
              (lcsDpRow_zero a_prev _) (p-1) (by omega)).2.2.2
        -- Mismatch cell: dpn[p+1] = max(dpo[p+1], dpn[p])
        have hstab_p : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 =
            (lcsDpStepPartial ch b_win (lcsDpRow a_prev b_win) p).getD p 0 := by
          rw [lcsDpStep_eq_partial, hbw_len]
          rw [lcsDpStepPartial_getD_stable _ _ _ p w (by omega), lcsDpStepPartial_prev_at]
        have hcell : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD (p + 1) 0 =
            Nat.max ((lcsDpRow a_prev b_win).getD (p + 1) 0)
              ((lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0) := by
          rw [hstab_p, lcsDpStep_eq_partial, hbw_len]
          by_cases hpw : p + 1 < w
          · rw [lcsDpStepPartial_getD_stable _ _ _ (p+1) w hpw, lcsDpStepPartial_prev_at,
                lcsDpStepPartial_last, if_neg hmismatch_bw]
          · have hpeq : p + 1 = w := by omega
            rw [show w = p + 1 from hpeq.symm, lcsDpStepPartial_last, if_neg hmismatch_bw]
        -- IH: dr > p ↔ dpn[p] = dpo[p]
        have hdr_spec := ih' s w (by omega) (by omega) hsw hw
        simp only [show k' - s = p from by omega] at hdr_spec
        change dr > p ↔ (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 =
            (lcsDpRow a_prev b_win).getD p 0 at hdr_spec
        -- Use DRowProp + CombEncodes + bounds to close
        constructor
        · intro hgt
          -- dc > p → dpo[p+1] > dpo[p] → dpo[p+1] = dpo[p]+1 ≥ dpn[p]
          have hdc_gt : dc > p := by omega
          have hdpo_inc := hce2.mp hdc_gt
          rw [hcell]; simp only [Nat.max_def]
          split
          · omega
          · rename_i hle; push_neg at hle; omega
        · intro heq
          rw [hcell] at heq
          -- max(dpo[p+1], dpn[p]) = dpo[p+1] means dpo[p+1] ≥ dpn[p]
          have hdpo_ge_dpn : (lcsDpRow a_prev b_win).getD (p + 1) 0 ≥
              (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 := by
            simp only [Nat.max_def] at heq; split at heq <;> omega
          -- Case split on dpn[p]
          by_cases hdpn_eq : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 =
              (lcsDpRow a_prev b_win).getD p 0
          · -- dpn[p] = dpo[p] → dr > p (IH) → dc > dr > p → dc > p
            have hdr_gt := hdr_spec.mpr hdpn_eq
            omega
          · -- dpn[p] = dpo[p]+1 → dpo[p+1] ≥ dpo[p]+1 → dpo[p+1] > dpo[p]
            have hne_val : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 =
                (lcsDpRow a_prev b_win).getD p 0 + 1 := by omega
            have hdpo_inc : (lcsDpRow a_prev b_win).getD (p + 1) 0 >
                (lcsDpRow a_prev b_win).getD p 0 := by omega
            have hdc_gt := hce2.mpr hdpo_inc; omega
    · -- Stay case: new d_row = dr + 1
      -- Goal: dr + 1 > k'+1-s ↔ dpn[k'+1-s] = dpo[k'+1-s]
      simp only
      by_cases hsj : s = k' + 1
      · subst hsj; simp only [Nat.sub_self]
        constructor
        · intro _; rw [lcsDpStep_zero, lcsDpRow_zero]
        · intro _; omega
      · set j := k' + 1 - s with hj_def
        set p := k' - s with hp_def
        have hpj : j = p + 1 := by omega
        have hsk'p : s + p = k' := by omega
        rw [hpj]
        set b_win := (b.drop s).take w with hbw_def
        have hbw_len : b_win.length = w := by
          rw [hbw_def, List.length_take, List.length_drop]; omega
        -- IH: dr > p ↔ dpn[p] = dpo[p]
        have hdr_spec := ih' s w (by omega) (by omega) hsw hw
        simp only [show k' - s = p from by omega] at hdr_spec
        change dr > p ↔ (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 =
            (lcsDpRow a_prev b_win).getD p 0 at hdr_spec
        -- Stay condition: dc ≤ dr, i.e., d_col[k'] ≤ dr
        have hdc_le_dr : dc ≤ dr := by omega
        -- CombEncodes: dc > p ↔ dpo[p+1] > dpo[p]
        have hce2 : dc > p ↔ (lcsDpRow a_prev b_win).getD (p + 1) 0 >
            (lcsDpRow a_prev b_win).getD p 0 := by
          have hpfx1 : (lcsDpRow a_prev b_win).getD (p + 1) 0 =
              lcsDp a_prev (List.take (p + 1) (List.drop s b)) := by
            rw [hbw_def, lcsDpRow_getD_prefix a_prev _ (p + 1) (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have hpfx0 : (lcsDpRow a_prev b_win).getD p 0 =
              lcsDp a_prev (List.take p (List.drop s b)) := by
            rw [hbw_def, lcsDpRow_getD_prefix a_prev _ p (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have h := combEncodes_per_position d_col b a_prev henc s p (by omega) (by omega)
          rw [hsk'p] at h; rw [hdc_eq, hpfx1, hpfx0]; exact h
        have hdpo_nd := lcsDpRow_nondecreasing a_prev b_win p (by rw [hbw_len]; omega)
        have hdpo_unit := lcsDpRow_unit_increase a_prev b_win p (by rw [hbw_len]; omega)
        have hbwp : b_win.getD p 0 = b.getD k' 0 := by
          simp only [hbw_def, List.getD]
          rw [List.getElem?_eq_getElem (by rw [List.length_take, List.length_drop]; omega)]
          simp only [Option.getD_some, List.getElem_take, List.getElem_drop]
          rw [List.getElem?_eq_getElem (by omega : k' < b.length)]
          simp [hsk'p]
        have hmismatch_bw : ¬(ch == b_win.getD p 0) = true := by rw [hbwp]; exact hmatch
        -- dpn[p] bounds
        have hdom : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 ≥
            (lcsDpRow a_prev b_win).getD p 0 := by
          by_cases hp0 : p = 0
          · rw [hp0, lcsDpRow_zero a_prev b_win, lcsDpStep_zero]
          · rw [show p = (p - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
            rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
            exact (lcsDpStepPartial_properties ch _ _
              (fun i hi => lcsDpRow_nondecreasing a_prev _ i hi)
              (fun i hi => lcsDpRow_unit_increase a_prev _ i hi)
              (lcsDpRow_zero a_prev _) (p-1) (by omega)).2.2.1
        have hub : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 ≤
            (lcsDpRow a_prev b_win).getD p 0 + 1 := by
          by_cases hp0 : p = 0
          · rw [hp0, lcsDpRow_zero a_prev b_win, lcsDpStep_zero]; omega
          · rw [show p = (p - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
            rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
            exact (lcsDpStepPartial_properties ch _ _
              (fun i hi => lcsDpRow_nondecreasing a_prev _ i hi)
              (fun i hi => lcsDpRow_unit_increase a_prev _ i hi)
              (lcsDpRow_zero a_prev _) (p-1) (by omega)).2.2.2
        -- Mismatch cell: dpn[p+1] = max(dpo[p+1], dpn[p])
        have hstab_p : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 =
            (lcsDpStepPartial ch b_win (lcsDpRow a_prev b_win) p).getD p 0 := by
          rw [lcsDpStep_eq_partial, hbw_len]
          rw [lcsDpStepPartial_getD_stable _ _ _ p w (by omega), lcsDpStepPartial_prev_at]
        have hcell : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD (p + 1) 0 =
            Nat.max ((lcsDpRow a_prev b_win).getD (p + 1) 0)
              ((lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0) := by
          rw [hstab_p, lcsDpStep_eq_partial, hbw_len]
          by_cases hpw : p + 1 < w
          · rw [lcsDpStepPartial_getD_stable _ _ _ (p+1) w hpw, lcsDpStepPartial_prev_at,
                lcsDpStepPartial_last, if_neg hmismatch_bw]
          · have hpeq : p + 1 = w := by omega
            rw [show w = p + 1 from hpeq.symm, lcsDpStepPartial_last, if_neg hmismatch_bw]
        -- Case split on dpn[p] = dpo[p] vs dpn[p] = dpo[p]+1
        by_cases hdpn_eq : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 =
            (lcsDpRow a_prev b_win).getD p 0
        · -- Case dpn[p] = dpo[p]: IH gives dr > p, so dr+1 > p+1
          -- dpn[p+1] = max(dpo[p+1], dpo[p]) = dpo[p+1]
          have hdr_gt : dr > p := hdr_spec.mpr hdpn_eq
          rw [hcell, hdpn_eq]
          simp only [Nat.max_def]
          split
          · -- dpo[p+1] ≤ dpo[p]: max = dpo[p]. dpo[p+1] = dpo[p] (by non-decreasing + ≤)
            rename_i hle; have hdpo_eq : (lcsDpRow a_prev b_win).getD (p + 1) 0 =
                (lcsDpRow a_prev b_win).getD p 0 := by omega
            constructor
            · intro _; omega
            · intro _; omega
          · -- dpo[p+1] > dpo[p]: max = dpo[p+1]
            constructor
            · intro _; rfl
            · intro _; omega
        · -- Case dpn[p] = dpo[p]+1: IH gives dr ≤ p (contrapositive)
          have hne_val : (lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD p 0 =
              (lcsDpRow a_prev b_win).getD p 0 + 1 := by omega
          have hdr_le : dr ≤ p := by
            by_contra h; push_neg at h; exact hdpn_eq (hdr_spec.mp h)
          -- dc ≤ dr ≤ p, so ¬(dc > p), so dpo[p+1] = dpo[p] (from hce2 contrapositive)
          have hdc_le : dc ≤ p := by omega
          have hno_ce : ¬(dc > p) := by omega
          have hdpo_eq : (lcsDpRow a_prev b_win).getD (p + 1) 0 =
              (lcsDpRow a_prev b_win).getD p 0 := by
            by_contra h; push_neg at h
            exact hno_ce (hce2.mpr (by omega))
          -- dpn[p+1] = max(dpo[p], dpn[p]) = max(dpo[p], dpo[p]+1) = dpo[p]+1
          -- So dpn[p+1] = dpo[p]+1 ≠ dpo[p] = dpo[p+1]
          -- Also dr+1 ≤ p+1, so ¬(dr+1 > p+1)
          have hno_lhs : ¬(dr + 1 > p + 1) := by omega
          have hno_rhs : ¬((lcsDpStep ch b_win (lcsDpRow a_prev b_win)).getD (p + 1) 0 =
              (lcsDpRow a_prev b_win).getD (p + 1) 0) := by
            rw [hcell, hne_val, hdpo_eq]
            simp only [Nat.max_def]; split <;> omega
          exact iff_of_false hno_lhs hno_rhs
  /-  Proof sketch: induction on k.
      Base (k=0): d_row = dr_init > 0, s must be 0, j=0, dpn[0]=dpo[0]=0 always.
      Step (k'+1): unfold processRowPartial_succ, colFoldStep/colStep, case split:
        s = k'+1 (j=0): trivial as base.
        s ≤ k' (j ≥ 1): Use IH at k' for same window. Three colStep sub-cases:
          Match/Swap (d_row = dc+1): dc = d_col[k'] via processRowPartial_getD_ge.
            Connect dc > (k'-s) ↔ dpo[j] > dpo[j-1] via combEncodes_per_position.
            Match cell: dpn[j] = dpo[j-1]+1, so dpn[j]=dpo[j] ↔ dpo[j]=dpo[j-1]+1 ↔ dpo[j]>dpo[j-1].
            Swap cell: dpn[j] = max(dpo[j], dpn[j-1]), use IH + combEncodes similarly.
          Stay (d_row = d_row_k'+1): d_row_k'+1 > j ↔ d_row_k' > j-1 ↔ dpn[j-1]=dpo[j-1] (IH).
            dpn[j]=max(dpo[j],dpn[j-1]). If dpn[j-1]=dpo[j-1]: max=dpo[j]. If not: use stay
            condition d_col[k']≤d_row_k' + IH contrapositive + combEncodes to get contradiction.
      Verified: 1,252,080 cases, 0 failures. -/
/-! ### The Column Invariant Base Case and Step -/

/-- Base case: ColSimInv holds at k = 0. -/
theorem colSimInv_base (d_col : List ℕ) (b : List ℕ) (a_prev : List ℕ)
    (ch : ℕ) :
    ColSimInv d_col d_col b a_prev ch 0 := by
  refine ⟨?_, ?_⟩
  · -- Part A: vacuously true (no j with s + j < 0)
    intro s w _ _ j _ hj; omega
  · -- Part C: trivially true (all j ≥ 0)
    intro j _; rfl

/-- Inductive step: if ColSimInv holds at k, then it holds at k+1
    (after one more colStep). This is the core cell-level argument.

    Processing column k:
    - colStep updates d_col[k] using (d_col_k[k], d_row_k, ch, b[k])
    - This produces new d_col value d_col_{k+1}[k] and new d_row_{k+1}

    For each window [s,s+w) containing position k (i.e., s ≤ k < s+w):
    - Let j = k - s (position within window)
    - colStep's match/mismatch/swap corresponds to lcsDpStep's cell at j
    - The crossing condition d_col[k] > j must match dp_new[j+1] > dp_new[j]

    NOTE: This is the deep content of Tiskin 2022, Theorem 4.10.
    DRowInv was removed from the signature because it was incorrectly formulated.
    Part A at the new position is proved directly using CombEncodes + DP recurrence. -/
theorem colSimInv_step (d_col_orig : List ℕ) (b : List ℕ) (a_prev : List ℕ)
    (ch : ℕ) (k : ℕ) (hk : k < b.length)
    (hlen : d_col_orig.length = b.length)
    (henc : CombEncodes d_col_orig b a_prev)
    (d_col_k : List ℕ) (d_row_k : ℕ)
    (hlen_k : d_col_k.length = b.length)
    (hinv : ColSimInv d_col_k d_col_orig b a_prev ch k)
    (hdr_pos : 0 < d_row_k)
    (hdr : DRowProp b a_prev ch k d_row_k) :
    let step := colFoldStep ch b (d_col_k, d_row_k) k
    ColSimInv step.1 d_col_orig b a_prev ch (k + 1) := by
  obtain ⟨hA_old, hC_old⟩ := hinv
  set dc := d_col_k.getD k 0 with hdc_def
  have hset_ne : ∀ v j, k ≠ j → (d_col_k.set k v).getD j 0 = d_col_k.getD j 0 :=
    fun v j h => getD_set_ne d_col_k k j v 0 h
  have hset_eq : ∀ v, (d_col_k.set k v).getD k 0 = v :=
    fun v => getD_set_eq d_col_k k v 0 (by omega)
  simp only [colFoldStep, colStep]
  split
  · -- Case 1: Match (ch == b.getD k 0)
    rename_i hmatch
    refine ⟨?_, ?_⟩
    · intro s w hsw hw j hj hsjk1
      by_cases hsjk : s + j < k
      · rw [hset_ne d_row_k (s + j) (by omega)]; exact hA_old s w hsw hw j hj hsjk
      · -- New position: s + j = k
        have hsjek : s + j = k := by omega
        rw [show (d_col_k.set k d_row_k).getD (s + j) 0 = d_row_k from by rw [hsjek]; exact hset_eq d_row_k]
        -- Match case: d_row_k > j ↔ dp_new[j+1] > dp_new[j]
        -- By DRowProp: d_row_k > j ↔ dp_new[j] = dp_old[j]
        -- Match DP: dp_new[j+1] = dp_old[j]+1
        -- So dp_new[j+1] > dp_new[j] ↔ dp_old[j]+1 > dp_new[j] ↔ dp_new[j] = dp_old[j]
        -- (since dp_old[j] ≤ dp_new[j] ≤ dp_old[j]+1 by prev dominance + upper bound)
        -- Proof uses DRowProp + lcsDpStepPartial_properties + match cell identity.
        -- Match case: d_row_k > j ↔ dp_new[j+1] > dp_new[j]
        -- By DRowProp: d_row_k > j ↔ dp_new[j] = dp_old[j]
        -- Match DP cell: dp_new[j+1] = dp_old[j]+1
        -- Bounds: dp_old[j] ≤ dp_new[j] ≤ dp_old[j]+1
        -- Chain: dp_new[j]=dp_old[j] ↔ dp_old[j]+1 > dp_new[j] ↔ dp_new[j+1] > dp_new[j]
        have hjeq : j = k - s := by omega
        subst hjeq
        have hdr_spec := hdr s w (by omega) (by omega) hsw hw
        have hbw_len : (List.take w (List.drop s b)).length = w := by
          rw [List.length_take, List.length_drop]; omega
        have hbwj : (List.take w (List.drop s b)).getD (k - s) 0 = b.getD k 0 := by
          simp only [List.getD]
          rw [List.getElem?_eq_getElem (by rw [hbw_len]; omega), List.getElem?_eq_getElem hk]
          simp only [Option.getD_some, List.getElem_take, List.getElem_drop]
          congr 1
        have hmatch_bw : (ch == (List.take w (List.drop s b)).getD (k - s) 0) = true := by
          rw [hbwj]; exact hmatch
        have hdpo_zero := lcsDpRow_zero a_prev (List.take w (List.drop s b))
        have hdpo_nd : ∀ i, i < w → (lcsDpRow a_prev (List.take w (List.drop s b))).getD (i + 1) 0 ≥
            (lcsDpRow a_prev (List.take w (List.drop s b))).getD i 0 :=
          fun i hi => lcsDpRow_nondecreasing a_prev _ i (by rw [hbw_len]; exact hi)
        have hdpo_unit : ∀ i, i < w → (lcsDpRow a_prev (List.take w (List.drop s b))).getD (i + 1) 0 ≤
            (lcsDpRow a_prev (List.take w (List.drop s b))).getD i 0 + 1 :=
          fun i hi => lcsDpRow_unit_increase a_prev _ i (by rw [hbw_len]; exact hi)
        -- dp_new[j+1] = dp_old[j] + 1 (match cell)
        have hcell : (lcsDpStep ch (List.take w (List.drop s b))
            (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s + 1) 0 =
            (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 + 1 := by
          rw [lcsDpStep_eq_partial, hbw_len]
          by_cases hjw : k - s + 1 < w
          · rw [lcsDpStepPartial_getD_stable _ _ _ (k-s+1) w hjw,
                lcsDpStepPartial_prev_at, lcsDpStepPartial_last, if_pos hmatch_bw]
          · have hjeq : k - s + 1 = w := by omega
            rw [show w = k - s + 1 from hjeq.symm, lcsDpStepPartial_last,
                show k - s + 1 = w from hjeq, if_pos hmatch_bw]
        -- Prev dominance: dp_new[j] >= dp_old[j]
        have hdom : (lcsDpStep ch (List.take w (List.drop s b))
            (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 ≥
            (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 := by
          by_cases hks0 : k - s = 0
          · rw [hks0, hdpo_zero, lcsDpStep_zero]
          · rw [show k - s = (k - s - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
            rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
            exact (lcsDpStepPartial_properties ch _ _
              (fun i hi => hdpo_nd i (by rw [← hbw_len]; exact hi))
              (fun i hi => hdpo_unit i (by rw [← hbw_len]; exact hi))
              hdpo_zero (k-s-1) (by omega)).2.2.1
        -- Upper bound: dp_new[j] ≤ dp_old[j] + 1
        have hub : (lcsDpStep ch (List.take w (List.drop s b))
            (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 ≤
            (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 + 1 := by
          by_cases hks0 : k - s = 0
          · rw [hks0, hdpo_zero, lcsDpStep_zero]; omega
          · rw [show k - s = (k - s - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
            rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
            exact (lcsDpStepPartial_properties ch _ _
              (fun i hi => hdpo_nd i (by rw [← hbw_len]; exact hi))
              (fun i hi => hdpo_unit i (by rw [← hbw_len]; exact hi))
              hdpo_zero (k-s-1) (by omega)).2.2.2
        simp only at hdr_spec
        rw [hdr_spec]
        constructor
        · intro heq; rw [hcell, heq]; omega
        · intro hgt; omega
    · intro j hj; rw [hset_ne d_row_k j (by omega)]; exact hC_old j (by omega)
  · split
    · -- Case 2: Mismatch + swap (dc > d_row_k)
      rename_i hmismatch hswap
      refine ⟨?_, ?_⟩
      · intro s w hsw hw j hj hsjk1
        by_cases hsjk : s + j < k
        · rw [hset_ne d_row_k (s + j) (by omega)]; exact hA_old s w hsw hw j hj hsjk
        · have hsjek : s + j = k := by omega
          rw [show (d_col_k.set k d_row_k).getD (s + j) 0 = d_row_k from by rw [hsjek]; exact hset_eq d_row_k]
          -- Swap case: mismatch DP cell dpn[j+1] = max(dpo[j+1], dpn[j])
          -- Forward: dpn[j]=dpo[j] → dpo[j+1]>dpo[j] (via combEncodes+swap) → dpn[j+1]>dpn[j]
          -- Backward: dpn[j+1]>dpn[j] → dpo[j+1]>dpn[j] → dpn[j]=dpo[j] (by unit increase)
          have hjeq : j = k - s := by omega
          subst hjeq
          have hdr_spec := hdr s w (by omega) (by omega) hsw hw
          simp only at hdr_spec
          have hbw_len : (List.take w (List.drop s b)).length = w := by
            rw [List.length_take, List.length_drop]; omega
          have hbwj : (List.take w (List.drop s b)).getD (k - s) 0 = b.getD k 0 := by
            simp only [List.getD]
            rw [List.getElem?_eq_getElem (by rw [hbw_len]; omega), List.getElem?_eq_getElem hk]
            simp only [Option.getD_some, List.getElem_take, List.getElem_drop]; congr 1
          have hmismatch_bw : ¬(ch == (List.take w (List.drop s b)).getD (k - s) 0) = true := by
            rw [hbwj]; exact hmismatch
          have hdpo_zero := lcsDpRow_zero a_prev (List.take w (List.drop s b))
          have hdpo_nd : ∀ i, i < w → (lcsDpRow a_prev (List.take w (List.drop s b))).getD (i + 1) 0 ≥
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD i 0 :=
            fun i hi => lcsDpRow_nondecreasing a_prev _ i (by rw [hbw_len]; exact hi)
          have hdpo_unit : ∀ i, i < w → (lcsDpRow a_prev (List.take w (List.drop s b))).getD (i + 1) 0 ≤
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD i 0 + 1 :=
            fun i hi => lcsDpRow_unit_increase a_prev _ i (by rw [hbw_len]; exact hi)
          -- dpn[j] bounds
          have hdom : (lcsDpStep ch (List.take w (List.drop s b))
              (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 ≥
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 := by
            by_cases hks0 : k - s = 0
            · rw [hks0, hdpo_zero, lcsDpStep_zero]
            · rw [show k - s = (k - s - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
              rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
              exact (lcsDpStepPartial_properties ch _ _
                (fun i hi => hdpo_nd i (by rw [← hbw_len]; exact hi))
                (fun i hi => hdpo_unit i (by rw [← hbw_len]; exact hi))
                hdpo_zero (k-s-1) (by omega)).2.2.1
          have hub : (lcsDpStep ch (List.take w (List.drop s b))
              (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 ≤
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 + 1 := by
            by_cases hks0 : k - s = 0
            · rw [hks0, hdpo_zero, lcsDpStep_zero]; omega
            · rw [show k - s = (k - s - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
              rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
              exact (lcsDpStepPartial_properties ch _ _
                (fun i hi => hdpo_nd i (by rw [← hbw_len]; exact hi))
                (fun i hi => hdpo_unit i (by rw [← hbw_len]; exact hi))
                hdpo_zero (k-s-1) (by omega)).2.2.2
          -- Mismatch cell: dpn[j+1] = max(dpo[j+1], dpn[j])
          have hstab_j : (lcsDpStep ch (List.take w (List.drop s b))
              (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 =
              (lcsDpStepPartial ch (List.take w (List.drop s b))
                (lcsDpRow a_prev (List.take w (List.drop s b))) (k - s)).getD (k - s) 0 := by
            rw [lcsDpStep_eq_partial, hbw_len]
            rw [lcsDpStepPartial_getD_stable _ _ _ (k-s) w (by omega), lcsDpStepPartial_prev_at]
          have hcell : (lcsDpStep ch (List.take w (List.drop s b))
              (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s + 1) 0 =
              Nat.max ((lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s + 1) 0)
                ((lcsDpStep ch (List.take w (List.drop s b))
                  (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0) := by
            rw [hstab_j, lcsDpStep_eq_partial, hbw_len]
            by_cases hjw : k - s + 1 < w
            · rw [lcsDpStepPartial_getD_stable _ _ _ (k-s+1) w hjw, lcsDpStepPartial_prev_at,
                  lcsDpStepPartial_last, if_neg hmismatch_bw]
            · have hjeq2 : k - s + 1 = w := by omega
              subst hjeq2
              rw [lcsDpStepPartial_last, if_neg hmismatch_bw]
          -- CombEncodes: d_col_orig[k] > j ↔ dpo[j+1] > dpo[j]
          have hsjk2 : s + (k - s) = k := by omega
          have hce := combEncodes_per_position d_col_orig b a_prev henc s (k - s) (by omega) (by omega)
          simp only [hsjk2] at hce
          have hpfx1 : (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s + 1) 0 =
              lcsDp a_prev (List.take (k - s + 1) (List.drop s b)) := by
            rw [lcsDpRow_getD_prefix a_prev _ (k-s+1) (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have hpfx0 : (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 =
              lcsDp a_prev (List.take (k - s) (List.drop s b)) := by
            rw [lcsDpRow_getD_prefix a_prev _ (k-s) (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have hce2 : d_col_orig.getD k 0 > (k - s) ↔
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s + 1) 0 >
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 := by
            rw [hpfx1, hpfx0]; exact hce
          have hdc_orig : d_col_k.getD k 0 = d_col_orig.getD k 0 := hC_old k (le_refl k)
          have hdc_gt_dr : d_col_orig.getD k 0 > d_row_k := by rw [← hdc_orig]; exact hswap
          simp only
          rw [hdr_spec]
          constructor
          · -- Forward: dpn[j] = dpo[j] → dpn[j+1] > dpn[j]
            intro heq
            have hdr_gt_j : d_row_k > (k - s) := hdr_spec.mpr heq
            have hdpo_inc := hce2.mp (by omega)
            -- dpn[j+1] = max(dpo[j+1], dpn[j]). Rewrite dpn[j] = dpo[j], get max(dpo[j+1], dpo[j])
            -- Since dpo non-decreasing, max = dpo[j+1]. Then dpo[j+1] > dpo[j] = dpn[j].
            rw [hcell, heq]
            simp only [Nat.max_def]
            split
            · rename_i hle; omega
            · exact hdpo_inc
          · -- Backward: dpn[j+1] > dpn[j] → dpn[j] = dpo[j]
            intro hgt
            -- dpn[j+1] = max(dpo[j+1], dpn[j]) > dpn[j] means dpo[j+1] > dpn[j]
            have hdpo_gt_dpn : (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s + 1) 0 >
                (lcsDpStep ch (List.take w (List.drop s b))
                  (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 := by
              rw [hcell] at hgt; simp only [Nat.max_def] at hgt; split at hgt <;> omega
            -- dpo[j+1] > dpn[j] and dpo[j+1] ≤ dpo[j]+1 and dpn[j] ≥ dpo[j]
            -- So dpo[j]+1 ≥ dpo[j+1] > dpn[j] ≥ dpo[j], giving dpn[j] = dpo[j]
            have := hdpo_unit (k-s) hj
            omega
      · intro j hj; rw [hset_ne d_row_k j (by omega)]; exact hC_old j (by omega)
    · -- Case 3: Mismatch + stay (dc ≤ d_row_k)
      rename_i hmismatch hstay
      refine ⟨?_, ?_⟩
      · intro s w hsw hw j hj hsjk1
        by_cases hsjk : s + j < k
        · rw [hset_ne dc (s + j) (by omega)]; exact hA_old s w hsw hw j hj hsjk
        · have hsjek : s + j = k := by omega
          rw [show (d_col_k.set k dc).getD (s + j) 0 = dc from by rw [hsjek]; exact hset_eq dc]
          rw [hdc_def, hC_old k (le_refl k)]
          -- Stay case: d_col_orig[k] > j ↔ dpn[j+1] > dpn[j]
          -- By CombEncodes + DRowProp + stay condition (dc ≤ d_row_k)
          have hjeq : j = k - s := by omega
          subst hjeq
          have hdr_spec := hdr s w (by omega) (by omega) hsw hw
          simp only at hdr_spec
          have hbw_len : (List.take w (List.drop s b)).length = w := by
            rw [List.length_take, List.length_drop]; omega
          have hbwj : (List.take w (List.drop s b)).getD (k - s) 0 = b.getD k 0 := by
            simp only [List.getD]
            rw [List.getElem?_eq_getElem (by rw [hbw_len]; omega), List.getElem?_eq_getElem hk]
            simp only [Option.getD_some, List.getElem_take, List.getElem_drop]; congr 1
          have hmismatch_bw : ¬(ch == (List.take w (List.drop s b)).getD (k - s) 0) = true := by
            rw [hbwj]; exact hmismatch
          have hdpo_zero := lcsDpRow_zero a_prev (List.take w (List.drop s b))
          have hdpo_nd : ∀ i, i < w → (lcsDpRow a_prev (List.take w (List.drop s b))).getD (i + 1) 0 ≥
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD i 0 :=
            fun i hi => lcsDpRow_nondecreasing a_prev _ i (by rw [hbw_len]; exact hi)
          have hdpo_unit : ∀ i, i < w → (lcsDpRow a_prev (List.take w (List.drop s b))).getD (i + 1) 0 ≤
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD i 0 + 1 :=
            fun i hi => lcsDpRow_unit_increase a_prev _ i (by rw [hbw_len]; exact hi)
          -- dpn[j] bounds
          have hdom : (lcsDpStep ch (List.take w (List.drop s b))
              (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 ≥
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 := by
            by_cases hks0 : k - s = 0
            · rw [hks0, hdpo_zero, lcsDpStep_zero]
            · rw [show k - s = (k - s - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
              rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
              exact (lcsDpStepPartial_properties ch _ _
                (fun i hi => hdpo_nd i (by rw [← hbw_len]; exact hi))
                (fun i hi => hdpo_unit i (by rw [← hbw_len]; exact hi))
                hdpo_zero (k-s-1) (by omega)).2.2.1
          have hub : (lcsDpStep ch (List.take w (List.drop s b))
              (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 ≤
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 + 1 := by
            by_cases hks0 : k - s = 0
            · rw [hks0, hdpo_zero, lcsDpStep_zero]; omega
            · rw [show k - s = (k - s - 1) + 1 from by omega, lcsDpStep_eq_partial, hbw_len]
              rw [lcsDpStepPartial_getD_stable _ _ _ _ w (by omega), lcsDpStepPartial_prev_at]
              exact (lcsDpStepPartial_properties ch _ _
                (fun i hi => hdpo_nd i (by rw [← hbw_len]; exact hi))
                (fun i hi => hdpo_unit i (by rw [← hbw_len]; exact hi))
                hdpo_zero (k-s-1) (by omega)).2.2.2
          -- Mismatch cell formula
          have hstab_j : (lcsDpStep ch (List.take w (List.drop s b))
              (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 =
              (lcsDpStepPartial ch (List.take w (List.drop s b))
                (lcsDpRow a_prev (List.take w (List.drop s b))) (k - s)).getD (k - s) 0 := by
            rw [lcsDpStep_eq_partial, hbw_len]
            rw [lcsDpStepPartial_getD_stable _ _ _ (k-s) w (by omega), lcsDpStepPartial_prev_at]
          have hcell : (lcsDpStep ch (List.take w (List.drop s b))
              (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s + 1) 0 =
              Nat.max ((lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s + 1) 0)
                ((lcsDpStep ch (List.take w (List.drop s b))
                  (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0) := by
            rw [hstab_j, lcsDpStep_eq_partial, hbw_len]
            by_cases hjw : k - s + 1 < w
            · rw [lcsDpStepPartial_getD_stable _ _ _ (k-s+1) w hjw, lcsDpStepPartial_prev_at,
                  lcsDpStepPartial_last, if_neg hmismatch_bw]
            · have hjeq2 : k - s + 1 = w := by omega
              subst hjeq2
              rw [lcsDpStepPartial_last, if_neg hmismatch_bw]
          -- CombEncodes: d_col_orig[k] > j ↔ dpo[j+1] > dpo[j]
          have hsjk2 : s + (k - s) = k := by omega
          have hce := combEncodes_per_position d_col_orig b a_prev henc s (k - s) (by omega) (by omega)
          simp only [hsjk2] at hce
          have hpfx1 : (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s + 1) 0 =
              lcsDp a_prev (List.take (k - s + 1) (List.drop s b)) := by
            rw [lcsDpRow_getD_prefix a_prev _ (k-s+1) (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have hpfx0 : (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 =
              lcsDp a_prev (List.take (k - s) (List.drop s b)) := by
            rw [lcsDpRow_getD_prefix a_prev _ (k-s) (by rw [hbw_len]; omega)]
            congr 1; rw [List.take_take, Nat.min_eq_left (by omega)]
          have hce2 : d_col_orig.getD k 0 > (k - s) ↔
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s + 1) 0 >
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 := by
            rw [hpfx1, hpfx0]; exact hce
          -- Stay condition: dc ≤ d_row_k, i.e., d_col_orig[k] ≤ d_row_k
          have hdc_le_dr : d_col_orig.getD k 0 ≤ d_row_k := by
            rw [← hC_old k (le_refl k)]; omega
          -- Case split on dpn[j] = dpo[j] vs dpn[j] = dpo[j]+1
          simp only
          by_cases heq_j : (lcsDpStep ch (List.take w (List.drop s b))
              (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 =
              (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0
          · -- Case dpn[j] = dpo[j]: both sides reduce to dpo[j+1] > dpo[j]
            rw [hcell, heq_j]
            simp only [Nat.max_def]
            split
            · -- dpo[j+1] ≤ dpo[j]: max = dpo[j]. Goal: d_col_orig[k] > j ↔ dpo[j] > dpo[j]
              rename_i hle
              constructor
              · intro h; exact absurd (hce2.mp h) (by omega)
              · intro h; omega
            · -- dpo[j+1] > dpo[j]: max = dpo[j+1]. Goal: d_col_orig[k] > j ↔ dpo[j+1] > dpo[j]
              exact hce2
          · -- Case dpn[j] = dpo[j]+1 (since dpo[j] ≤ dpn[j] ≤ dpo[j]+1 and dpn[j] ≠ dpo[j])
            have hne_val : (lcsDpStep ch (List.take w (List.drop s b))
                (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0 =
                (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 + 1 := by omega
            -- DRowProp contrapositive: dpn[j] ≠ dpo[j] → ¬(d_row_k > j), i.e., d_row_k ≤ j
            have hdr_le_j : d_row_k ≤ k - s := by
              by_contra h; push_neg at h; exact heq_j (hdr_spec.mp h)
            -- dc ≤ d_row_k ≤ j, so d_col_orig[k] ≤ j, i.e., ¬(d_col_orig[k] > j)
            have hdc_le_j : d_col_orig.getD k 0 ≤ k - s := by omega
            have hno_lhs : ¬(d_col_orig.getD k 0 > (k - s)) := by omega
            -- dpo[j+1] = dpo[j] (from CombEncodes contrapositive)
            have hdpo_eq : (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s + 1) 0 =
                (lcsDpRow a_prev (List.take w (List.drop s b))).getD (k - s) 0 := by
              by_contra h; push_neg at h
              have := hdpo_nd (k-s) (by omega)
              exact hno_lhs (hce2.mpr (by omega))
            -- dpn[j+1] = max(dpo[j], dpn[j]) = dpn[j] (since dpo[j] < dpn[j])
            have hno_rhs : ¬((lcsDpStep ch (List.take w (List.drop s b))
                (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s + 1) 0 >
                (lcsDpStep ch (List.take w (List.drop s b))
                  (lcsDpRow a_prev (List.take w (List.drop s b)))).getD (k - s) 0) := by
              rw [hcell, hne_val, hdpo_eq]
              simp only [Nat.max_def]
              split <;> omega
            exact iff_of_false hno_lhs hno_rhs
      · intro j hj; rw [hset_ne dc j (by omega)]; exact hC_old j (by omega)

/-! ### The Row Step Theorem -/

/-- d_row is always positive throughout processRow (given positive initial d_row). -/
private theorem processRowPartial_drow_pos (ch : ℕ) (b : List ℕ) (d_col : List ℕ)
    (dr_init : ℕ) (hdr_init : 0 < dr_init)
    (k : ℕ) (hk : k ≤ b.length) :
    0 < (processRowPartial ch b d_col dr_init k).2 := by
  induction k with
  | zero => rw [processRowPartial_zero]; exact hdr_init
  | succ k' ih =>
    rw [processRowPartial_succ]
    simp only [colFoldStep, colStep]
    split <;> (try split) <;> simp <;> omega

/-- The column invariant holds throughout processRow (DRowInv removed). -/
theorem colSimInv_processRow (ch : ℕ) (b : List ℕ) (d_col : List ℕ)
    (a_prev : List ℕ) (dr_init : ℕ)
    (henc : CombEncodes d_col b a_prev)
    (hlen : d_col.length = b.length)
    (hdr_init : 0 < dr_init)
    (k : ℕ) (hk : k ≤ b.length) :
    ColSimInv (processRowPartial ch b d_col dr_init k).1
              d_col b a_prev ch k := by
  induction k with
  | zero =>
    rw [processRowPartial_zero]
    exact colSimInv_base d_col b a_prev ch
  | succ k' ih =>
    rw [processRowPartial_succ]
    have hk' : k' < b.length := by omega
    have hlen_k' : (processRowPartial ch b d_col dr_init k').1.length = b.length :=
      processRowPartial_length ch b d_col dr_init k' (by omega) hlen
    have hinv_k := ih (by omega)
    have hdr_pos_k := processRowPartial_drow_pos ch b d_col dr_init hdr_init k' (by omega)
    have hdr_k := drow_processRow ch b d_col a_prev dr_init henc hlen hdr_init k' (by omega)
    exact colSimInv_step d_col b a_prev ch k' hk' hlen henc
      (processRowPartial ch b d_col dr_init k').1
      (processRowPartial ch b d_col dr_init k').2
      hlen_k'
      hinv_k
      hdr_pos_k
      hdr_k

/-- From the column invariant at k = b.length, extract the crossing count property.

    When k = b.length, Part A covers ALL positions in every window [s,s+w).
    For each window, the crossing count #{j : d_col[s+j] > j} equals
    #{j : dp_new[j+1] > dp_new[j]} = dp_new[w] - dp_new[0] = LCS. -/
theorem colSimInv_to_encodes (d_col_final : List ℕ) (d_col_orig : List ℕ)
    (b : List ℕ) (a_prev : List ℕ) (ch : ℕ)
    (hinv : ColSimInv d_col_final d_col_orig b a_prev ch b.length)
    (hlen : d_col_final.length = b.length) :
    CombEncodes d_col_final b (a_prev ++ [ch]) := by
  intro s w hsw hw
  obtain ⟨hA, _⟩ := hinv
  set b_win := (b.drop s).take w with hbw
  set dp_old := lcsDpRow a_prev b_win with hdpold
  set dp_new := lcsDpStep ch b_win dp_old with hdpnew
  have hbw_len : b_win.length = w := by
    simp [hbw, List.length_take, List.length_drop]; omega
  -- Step 1: crossing count = counting DP increases (by Part A)
  have hcc_eq : crossingCount' d_col_final s w =
      (List.range w).countP (fun j => decide (dp_new.getD (j + 1) 0 > dp_new.getD j 0)) := by
    unfold crossingCount'
    apply List.countP_congr
    intro j hj
    simp only [List.mem_range] at hj
    have := hA s w hsw hw j hj (by omega)
    simp only [decide_eq_true_eq]
    exact this
  -- Step 2: counting increases = dp_new[w] - dp_new[0] (telescoping)
  have hdp_nd : ∀ j, j < w → dp_new.getD (j + 1) 0 ≥ dp_new.getD j 0 := by
    intro j hj
    rw [hdpnew]
    exact lcsDpStep_nondecreasing ch b_win dp_old j (by omega)
      (by rw [hdpold, lcsDpRow_length, hbw_len])
      (by intro i hi; rw [hdpold]; exact lcsDpRow_nondecreasing a_prev b_win i (by omega))
      (by intro i hi; rw [hdpold]; exact lcsDpRow_unit_increase a_prev b_win i (by omega))
      (by rw [hdpold]; exact lcsDpRow_zero a_prev b_win)
  have hdp_step : ∀ j, j < w → dp_new.getD (j + 1) 0 ≤ dp_new.getD j 0 + 1 := by
    intro j hj
    rw [hdpnew]
    exact lcsDpStep_unit_increase ch b_win dp_old j (by omega)
      (by intro i hi; rw [hdpold]; exact lcsDpRow_nondecreasing a_prev b_win i (by omega))
      (by intro i hi; rw [hdpold]; exact lcsDpRow_unit_increase a_prev b_win i (by omega))
      (by rw [hdpold]; exact lcsDpRow_zero a_prev b_win)
  have htelescope := countP_increases_eq_final dp_new w
    (by rw [hdpnew, lcsDpStep_length, hbw_len]) hdp_nd hdp_step
  have hdp0 : dp_new.getD 0 0 = 0 := by rw [hdpnew]; exact lcsDpStep_zero ch b_win dp_old
  -- Step 3: dp_new[w] = lcsDp(a_prev ++ [ch], b_win)
  rw [hcc_eq, htelescope, hdp0, Nat.sub_zero]
  rw [hdpnew, hdpold, ← lcsDpRow_append_singleton, ← lcsDpRow_getD_eq_lcsDp, hbw_len]

/-- **Row Step Lemma**: If d_col encodes `a_prev` vs `b`, then after
    processing one row (character `ch`), the result encodes `a_prev ++ [ch]` vs `b`.

    This is the mechanistic content of Tiskin 2022, Theorem 4.10. -/
theorem row_step_encodes (ch : ℕ) (b : List ℕ) (d_col : List ℕ) (a_prev : List ℕ)
    (offset : ℕ) (henc : CombEncodes d_col b a_prev)
    (hlen : d_col.length = b.length) :
    CombEncodes (processRow ch b d_col (offset + 1)) b (a_prev ++ [ch]) := by
  rw [processRow_eq_partial]
  have hinv := colSimInv_processRow ch b d_col a_prev (offset + 1)
    henc hlen (by omega) b.length (le_refl _)
  have hlen_final : (processRowPartial ch b d_col (offset + 1) b.length).1.length =
      b.length :=
    processRowPartial_length ch b d_col (offset + 1) b.length (le_refl _) hlen
  exact colSimInv_to_encodes
    (processRowPartial ch b d_col (offset + 1) b.length).1
    d_col b a_prev ch
    hinv hlen_final

/-- The generalized inductive theorem:
    combFold preserves the CombEncodes property. -/
theorem combFold_encodes (a_new : List ℕ) (b : List ℕ) (init : RowAcc)
    (a_prev : List ℕ) (henc : CombEncodes init.1 b a_prev)
    (hlen : init.1.length = b.length) :
    CombEncodes (combFold a_new b init).1 b (a_prev ++ a_new) := by
  induction a_new generalizing init a_prev with
  | nil =>
    simp only [combFold, List.append_nil]
    exact henc
  | cons ch rest ih =>
    simp only [combFold, List.foldl]
    have hfold : (List.foldl (rowFoldStep b) (rowFoldStep b init ch) rest) =
        combFold rest b (rowFoldStep b init ch) := rfl
    rw [hfold]
    have hlen' : (rowFoldStep b init ch).1.length = b.length := by
      simp [rowFoldStep]
      exact processRow_length ch b init.1 (init.2 + 1) hlen
    have henc' : CombEncodes (rowFoldStep b init ch).1 b (a_prev ++ [ch]) := by
      simp [rowFoldStep]
      exact row_step_encodes ch b init.1 a_prev init.2 henc hlen
    rw [show a_prev ++ ch :: rest = (a_prev ++ [ch]) ++ rest from by simp]
    exact ih (rowFoldStep b init ch) (a_prev ++ [ch]) henc' hlen'

/-! ## The Main Theorem -/

/-- **Crossing Count = LCS Theorem**: the crossing count from the Krusche
    comb's d_col equals the LCS computed by dynamic programming, for ALL windows.

    This is the fundamental result of the Tiskin/Krusche framework (Theorem 4.10).

    **Proof**: By the generalized induction theorem `combFold_encodes`.
    Starting from combInit (all zeros, which encodes the empty query by
    `combEncodes_nil`), processing the full query `a` yields a d_col that
    encodes `[] ++ a = a`.

    The key unsolved component is `row_step_encodes`, which establishes
    that processing one row of the seaweed comb preserves the encoding.

    Verified exhaustively for binary strings |A| ≤ 4, |B| ≤ 6 (61,380 cases)
    and randomly for |A| ≤ 10, |B| ≤ 15 (456,756 cases), 0 failures.
    See dev/comb_properties_study.py, Property 2. -/
theorem crossing_count_eq_lcs (a : List ℕ) (b : List ℕ) (s w : ℕ)
    (hs : s + w ≤ b.length) (hw : w > 0) :
    crossingCount' (combDcol a b) s w =
    lcsDp a (b.drop s |>.take w) := by
  have henc := combFold_encodes a b (combInit b.length) []
    (combEncodes_nil b) (by simp [combInit])
  simp at henc
  exact henc s w hs hw

/-! ## Summary

The crossing count = LCS theorem, together with:
- CombComposition.lean (comb is a fold → splits at boundaries)
- LCDCorrectness.lean (single-character base case)
- CombCorrectness.lean (cell mechanics, conservation law)

...provides the complete formal foundation for the semi-local string
comparison framework:

  Build comb: O(mn) → d_col
  Query any window: O(1) via crossing count
  Correctness: crossing count = LCS (this theorem)
  Incrementality: comb splits at character boundaries (composition)
  Base case: single character → LCD (verified)
-/
