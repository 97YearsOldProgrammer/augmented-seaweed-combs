/-
  FlashAlignment/ScoreDetermination.lean

  Score Determination Theorem (Theorem 1 of the augmented seaweed paper)

  The augmented comb output (d_col, depth_col) determines the affine gap
  alignment score at every window position. The correction formula
  extracts the score from LCS and diagonal match count:

    epsilon = LCS - diag
    If epsilon <= go: score = diag  (Tiers 1 and 2)
    If epsilon > go:  score = banded Gotoh DP  (Tier 3)

  Main results:
  - gotohGlobalScore: Gotoh DP score H[m][n]
  - correctionScoreDP: score via the three-tier correction formula
  - score_determination: the two agree (structured proof with bridge lemmas)
  - semi_local_score_det: windowed version (verified on all windows)

  Proof structure:
  - score_determination splits into eps > go (rfl) and eps <= go (bridge lemmas)
  - gotoh_ge_diag: Gotoh DP >= diagCount (diagonal path is feasible)
  - gotoh_le_diag_when_eps_small: when eps <= go, Gotoh DP <= diagCount
  - Both bridge lemmas are proved modulo gotohCellH_eq_processRow
    (equivalence between column-recursive and fold-based Gotoh DP computation)

  SORRY STATUS (2 remaining):
  1. gotohCellH_eq_processRow: column-recursive H = fold-based H
     Mathematical proof: by induction on col, the fold step produces the same
     values as the recursive definition (same recurrence, same base case).
     Formalization blocked by List.foldl decomposition infrastructure.
  2. gotoh_le_diag_when_eps_small: when eps <= go, Gotoh score <= diagCount
     Mathematical proof: any non-diagonal path opens >= 1 gap (costing >= go);
     max extra matches = eps <= go; net benefit <= 0; so score <= diag.
     Formalization requires alignment path decomposition of Gotoh DP fold.

  Both statements are verified on 17+ concrete test cases via native_decide.

  Paper reference: Theorem 1 (Score Determination)
-/
import Mathlib.Tactic
import AugmentedSeaweed.Basic
import AugmentedSeaweed.Observer
import AugmentedSeaweed.PathSeparation
import AugmentedSeaweed.CombComposition
import AugmentedSeaweed.CorrectionFormula

/-! ## Gotoh DP Score Extraction -/

/-- The Gotoh DP score at the last column: H[m][n].
    For equal-length alignment (|a| = |b|), this is the optimal
    affine gap alignment score. -/
def gotohGlobalScore (a b : List ℕ) (go ge : ℤ) : ℤ :=
  let row := gotohFinalRow a b go ge
  row.h.getD b.length NEG_INF

/-- The maximum H value across all columns of the Gotoh DP final row.
    For semi-global alignment (end-free in reference), this is the score. -/
def gotohMaxScore (a b : List ℕ) (go ge : ℤ) : ℤ :=
  let row := gotohFinalRow a b go ge
  row.h.foldl max NEG_INF

/-! ## LCS via Dynamic Programming -/

/-- Standard LCS DP: compute LCS length of two lists via O(mn) DP. -/
def lcsDP (a : List ℕ) (b : List ℕ) : ℕ :=
  let n := b.length
  let init := List.replicate (n + 1) 0
  let final := a.foldl (fun (prev : List ℕ) ai =>
    (List.range n).foldl (fun (curr : List ℕ) j =>
      let bj := b.getD j 0
      let val :=
        if ai == bj then prev.getD j 0 + 1
        else max (prev.getD (j + 1) 0) (curr.getD j 0)
      curr ++ [val]
    ) [0]
  ) init
  final.getD n 0

/-! ## Diagonal Match Count -/

/-- Count diagonal matches: #{i : a[i] = b[i]} for aligned positions. -/
def diagCount (a b : List ℕ) : ℕ :=
  (List.range (min a.length b.length)).countP
    (fun i => a.getD i 0 == b.getD i 0)

/-! ## The Correction Formula Score

The three-tier model from CorrectionFormula.lean, made computable:
  - Compute LCS via DP (or equivalently, from comb's d_col)
  - Compute diagonal match count from sequences
  - epsilon = LCS - diag
  - Tier 1 (epsilon = 0): score = LCS = diag
  - Tier 2 (0 < epsilon <= go): score = diag
  - Tier 3 (epsilon > go): score = Gotoh DP (banded by epsilon)

For Tiers 1-2, no DP is needed. For Tier 3, the Gotoh DP is used
as fallback (in practice, this is epsilon-banded for O(m*epsilon) cost).
-/

/-- Correction formula score for aligning `a` against `b`.
    Uses LCS DP and diagonal match count to classify into tiers.
    Falls back to Gotoh DP for Tier 3. -/
def correctionScoreDP (a b : List ℕ) (go ge : ℤ) : ℤ :=
  let lcs := (lcsDP a b : ℤ)
  let diag := (diagCount a b : ℤ)
  let epsilon := lcs - diag
  if epsilon ≤ go then diag
  else gotohGlobalScore a b go ge

/-! ## Concrete Verification: Equal-Length Cases

For equal-length strings (|a| = |b|), the correction formula score
should equal the Gotoh DP global score H[m][n]. We verify this on
12 test cases covering exact matches, substitutions, shifts, rotations,
and multi-letter alphabets. -/

/-- Test 1: exact match, epsilon = 0, score = 3. -/
theorem score_det_test1 :
    correctionScoreDP [0,1,0] [0,1,0] 2 1 =
    gotohGlobalScore [0,1,0] [0,1,0] 2 1 := by native_decide

/-- Test 2: exact match, epsilon = 0, score = 4. -/
theorem score_det_test2 :
    correctionScoreDP [0,1,0,1] [0,1,0,1] 1 1 =
    gotohGlobalScore [0,1,0,1] [0,1,0,1] 1 1 := by native_decide

/-- Test 3: 1 substitution, LCS = diag = 2, epsilon = 0. -/
theorem score_det_test3 :
    correctionScoreDP [0,1,0] [0,0,0] 2 1 =
    gotohGlobalScore [0,1,0] [0,0,0] 2 1 := by native_decide

/-- Test 4: shifted pattern (ABAB vs BABA), diag = 0, LCS = 3, epsilon = 3. -/
theorem score_det_test4 :
    correctionScoreDP [0,1,0,1] [1,0,1,0] 1 1 =
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 1 1 := by native_decide

/-- Test 5: rotated pattern (AAAB vs BAAA), diag = 2, LCS = 3, epsilon = 1. -/
theorem score_det_test5 :
    correctionScoreDP [0,0,0,1] [1,0,0,0] 1 1 =
    gotohGlobalScore [0,0,0,1] [1,0,0,0] 1 1 := by native_decide

/-- Test 6: 3-letter alphabet, swapped middle. -/
theorem score_det_test6 :
    correctionScoreDP [0,1,2,0] [0,2,1,0] 2 1 =
    gotohGlobalScore [0,1,2,0] [0,2,1,0] 2 1 := by native_decide

/-- Test 7: longer exact match (5 chars). -/
theorem score_det_test7 :
    correctionScoreDP [0,1,0,1,0] [0,1,0,1,0] 2 1 =
    gotohGlobalScore [0,1,0,1,0] [0,1,0,1,0] 2 1 := by native_decide

/-- Test 8: 1 substitution in longer string. -/
theorem score_det_test8 :
    correctionScoreDP [0,1,0,1,0] [0,1,1,1,0] 2 1 =
    gotohGlobalScore [0,1,0,1,0] [0,1,1,1,0] 2 1 := by native_decide

/-- Test 9: all mismatches (score = 0). -/
theorem score_det_test9 :
    correctionScoreDP [0,0,0] [1,1,1] 1 1 =
    gotohGlobalScore [0,0,0] [1,1,1] 1 1 := by native_decide

/-- Test 10: single character match. -/
theorem score_det_test10 :
    correctionScoreDP [0] [0] 1 1 =
    gotohGlobalScore [0] [0] 1 1 := by native_decide

/-- Test 11: single character mismatch. -/
theorem score_det_test11 :
    correctionScoreDP [0] [1] 1 1 =
    gotohGlobalScore [0] [1] 1 1 := by native_decide

/-- Test 12: two chars, one match. -/
theorem score_det_test12 :
    correctionScoreDP [0,1] [0,0] 1 1 =
    gotohGlobalScore [0,1] [0,0] 1 1 := by native_decide

/-! ## Additional Verification: Various Gap Penalties -/

/-- Same input, different gap penalties: go=1. -/
theorem score_det_gap1 :
    correctionScoreDP [0,1,0,1] [1,0,1,0] 1 1 =
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 1 1 := by native_decide

/-- Same input, different gap penalties: go=2. -/
theorem score_det_gap2 :
    correctionScoreDP [0,1,0,1] [1,0,1,0] 2 1 =
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 2 1 := by native_decide

/-- Same input, different gap penalties: go=3. -/
theorem score_det_gap3 :
    correctionScoreDP [0,1,0,1] [1,0,1,0] 3 1 =
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 3 1 := by native_decide

/-- Same input, go=1, ge=2 (high extension penalty). -/
theorem score_det_gap4 :
    correctionScoreDP [0,1,0,1] [1,0,1,0] 1 2 =
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 1 2 := by native_decide

/-- Same input, go=2, ge=2. -/
theorem score_det_gap5 :
    correctionScoreDP [0,1,0,1] [1,0,1,0] 2 2 =
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 2 2 := by native_decide

/-! ## Semi-Local Score Determination

The correction formula extends to semi-local alignment: for any window
[s, s+w) of the reference, the score is determined by running the
correction formula on a vs b[s:s+w].

This is what makes the framework useful for seed-and-extend:
after computing LCS for all windows (one O(mn) comb pass), the affine
gap score at each window is available via the correction formula. -/

/-- Semi-local score: Gotoh DP of a vs b[s:s+m] (equal-length window). -/
def gotohWindowScore (a b : List ℕ) (go ge : ℤ) (s : ℕ) : ℤ :=
  gotohGlobalScore a (b.drop s |>.take a.length) go ge

/-- Semi-local correction score: correction formula at window [s, s+m). -/
def correctionWindowScore (a b : List ℕ) (go ge : ℤ) (s : ℕ) : ℤ :=
  correctionScoreDP a (b.drop s |>.take a.length) go ge

/-- Semi-local: a=[0,1] (m=2), b=[1,0,1,0] (n=4), go=1, ge=1.
    All 3 valid windows of width 2. -/
theorem semi_local_test1 :
    ∀ (s : Fin 4),
      s.val + 2 ≤ 4 →
      correctionWindowScore [0,1] [1,0,1,0] 1 1 s.val =
      gotohWindowScore [0,1] [1,0,1,0] 1 1 s.val := by
  native_decide

/-- Semi-local: a=[0,0,1] (m=3), b=[1,0,0,1,0] (n=5), go=2, ge=1.
    All 3 valid windows of width 3. -/
theorem semi_local_test2 :
    ∀ (s : Fin 4),
      s.val + 3 ≤ 5 →
      correctionWindowScore [0,0,1] [1,0,0,1,0] 2 1 s.val =
      gotohWindowScore [0,0,1] [1,0,0,1,0] 2 1 s.val := by
  native_decide

/-- Semi-local: a=[0,1,0] (m=3), b=[1,0,1,0,1] (n=5), go=2, ge=1.
    All 3 valid windows of width 3. -/
theorem semi_local_test3 :
    ∀ (s : Fin 4),
      s.val + 3 ≤ 5 →
      correctionWindowScore [0,1,0] [1,0,1,0,1] 2 1 s.val =
      gotohWindowScore [0,1,0] [1,0,1,0,1] 2 1 s.val := by
  native_decide

/-! ## LCS >= diag (Well-Definedness)

The correction formula requires LCS >= diag (so epsilon >= 0).
This holds because diagonal matches form a common subsequence. -/

/-- LCS >= diag verified on all test inputs. -/
theorem lcs_ge_diag_test1 : lcsDP [0,1,0] [0,1,0] ≥ diagCount [0,1,0] [0,1,0] := by native_decide
theorem lcs_ge_diag_test2 : lcsDP [0,1,0,1] [1,0,1,0] ≥ diagCount [0,1,0,1] [1,0,1,0] := by native_decide
theorem lcs_ge_diag_test3 : lcsDP [0,0,0] [1,1,1] ≥ diagCount [0,0,0] [1,1,1] := by native_decide
theorem lcs_ge_diag_test4 : lcsDP [0,1,2,0] [0,2,1,0] ≥ diagCount [0,1,2,0] [0,2,1,0] := by native_decide
theorem lcs_ge_diag_test5 : lcsDP [0,0,0,1] [1,0,0,0] ≥ diagCount [0,0,0,1] [1,0,0,0] := by native_decide

/-! ## Bridge Lemmas for Score Determination

Two bridge lemmas connect the abstract correction formula to the concrete Gotoh DP:
1. gotoh_ge_diag: Gotoh DP score >= diagonal match count (diagonal path is feasible)
2. gotoh_le_diag_when_eps_small: when epsilon <= go, Gotoh DP score <= diag

Together they prove: when epsilon <= go, gotohGlobalScore = diagCount. -/

/-- Recursive definition of Gotoh DP row after processing k query characters.
    Equivalent to the fold in gotohFinalRow, but amenable to induction. -/
def gotohAfterK (a b : List ℕ) (go ge : ℤ) : ℕ → GotohRow
  | 0 => gotohInitRow b.length
  | k + 1 => gotohProcessRow (gotohAfterK a b go ge k) (a.getD k 0) b go ge (k + 1)

/-- gotohAfterK at full length equals gotohFinalRow. -/
theorem gotohAfterK_full (a b : List ℕ) (go ge : ℤ) :
    gotohAfterK a b go ge a.length = gotohFinalRow a b go ge := by
  unfold gotohFinalRow
  have key : ∀ k : ℕ, k ≤ a.length →
      (List.range k).foldl (fun prevRow iIdx =>
        gotohProcessRow prevRow (a.getD iIdx 0) b go ge (iIdx + 1)
      ) (gotohInitRow b.length) = gotohAfterK a b go ge k := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [gotohAfterK]
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih (Nat.le_of_succ_le hn)]
      rfl
  exact (key a.length le_rfl).symm

/-! ### Helper: List.getD default irrelevance for valid indices -/

/-- When index is within bounds, getD returns the same value regardless of default. -/
theorem List.getD_default_irrel {α : Type*} (l : List α) (n : ℕ) (d₁ d₂ : α)
    (hn : n < l.length) : l.getD n d₁ = l.getD n d₂ := by
  unfold List.getD
  have : l[n]? = some l[n] := List.getElem?_eq_getElem hn
  rw [this]; rfl

/-! ### Helper: gotohProcessRow H list length and diagonal cell bound

The key step lemma: the H value at column col in the output of gotohProcessRow
is at least H_prev[col-1] + match_score. This follows from the definition:
H[row][col] = max(diagonal, E, F) >= diagonal = H_prev[col-1] + match. -/

/-- The H list output of gotohProcessRow has length b.length + 1. -/
theorem gotohProcessRow_h_length (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row : ℕ) :
    (gotohProcessRow prev ai b go ge row).h.length = b.length + 1 := by
  -- The fold in gotohProcessRow starts with [h0] (length 1) and at each step
  -- prepends one element, giving length n+1 after n steps. After reverse: same length.
  unfold gotohProcessRow
  simp only [List.length_reverse]
  -- Prove by showing the fold step always adds one element to the first component.
  -- We use a general lemma: for any fold that prepends to lists,
  -- the length after k steps is (initial length) + k.
  -- The key insight: at each fold step, hij :: acc.1 has length acc.1.length + 1.
  set n := b.length
  set f := fun (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) =>
    let j := jIdx + 1
    let bChar := b.getD jIdx 0
    let h_prev_j := prev.h.getD j 0
    let h_prev_j1 := prev.h.getD (j - 1) 0
    let h_curr_j1 := acc.1.head!
    let f_curr_j1 := acc.2.2.head!
    let matchScore : ℤ := if ai == bChar then 1 else 0
    let diag := h_prev_j1 + matchScore
    let e_prev_j := prev.e.getD j NEG_INF
    let eij := max (h_prev_j - go) (e_prev_j - ge)
    let fij := max (h_curr_j1 - go) (f_curr_j1 - ge)
    let hij := max diag (max eij fij)
    (hij :: acc.1, eij :: acc.2.1, fij :: acc.2.2)
  -- The fold step always adds exactly one element to the H list
  have h_step : ∀ acc jIdx, (f acc jIdx).1.length = acc.1.length + 1 := by
    intro acc jIdx; simp only [f, List.length_cons]
  -- By induction: after k steps, length = initial + k
  suffices ∀ (init : List ℤ × List ℤ × List ℤ) (k : ℕ),
      ((List.range k).foldl f init).1.length = init.1.length + k by
    have := this ([-(go + ge * ((row : ℤ) - 1))],
                  [-(go + ge * ((row : ℤ) - 1))],
                  [NEG_INF]) n
    simp only [List.length_cons, List.length_nil] at this
    omega
  intro init k
  induction k generalizing init with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [h_step, ih]
    omega

/-- The H list output of gotohAfterK has length b.length + 1. -/
theorem gotohAfterK_h_length (a b : List ℕ) (go ge : ℤ) (k : ℕ)
    (hk : k ≤ a.length) :
    (gotohAfterK a b go ge k).h.length = b.length + 1 := by
  induction k with
  | zero => simp [gotohAfterK, gotohInitRow, List.replicate]
  | succ n ih =>
    simp only [gotohAfterK]
    exact gotohProcessRow_h_length _ _ _ _ _ _

/-! ### Column-recursive Gotoh DP cell computation
Column-recursive H and F values, equivalent to gotohProcessRow but amenable to induction.
H and F are mutually recursive: F[j+1] depends on H[j], and H[j+1] depends on F[j+1]. -/

mutual
/-- H value at column j of a Gotoh DP row, computed column-recursively. -/
def gotohCellH (prev : GotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ) (row : ℕ) : ℕ → ℤ
  | 0 => -(go + ge * ((row : ℤ) - 1))
  | j + 1 =>
    let bChar := b.getD j 0
    let matchScore : ℤ := if ai == bChar then 1 else 0
    let diag := prev.h.getD j 0 + matchScore
    let eij := max (prev.h.getD (j + 1) 0 - go) (prev.e.getD (j + 1) NEG_INF - ge)
    let fij := max (gotohCellH prev ai b go ge row j - go)
                   (gotohCellF prev ai b go ge row j - ge)
    max diag (max eij fij)

def gotohCellF (prev : GotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ) (row : ℕ) : ℕ → ℤ
  | 0 => NEG_INF
  | j + 1 =>
    max (gotohCellH prev ai b go ge row j - go)
        (gotohCellF prev ai b go ge row j - ge)
end

/-- The column-recursive H value at column col >= 1 is >= the diagonal contribution.
    This follows directly from the recursive definition: H = max(diag, E, F) >= diag. -/
theorem gotohCellH_ge_diag (prev : GotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ) (row col : ℕ)
    (hcol : col ≥ 1) :
    gotohCellH prev ai b go ge row col ≥
    prev.h.getD (col - 1) 0 + (if ai == b.getD (col - 1) 0 then 1 else 0) := by
  -- For col = k + 1 (since col >= 1): gotohCellH prev ai b go ge row (k+1) =
  --   max(prev.h.getD k 0 + matchScore, max(eij, fij)) >= prev.h.getD k 0 + matchScore
  obtain ⟨k, rfl⟩ : ∃ k, col = k + 1 := ⟨col - 1, by omega⟩
  simp only [gotohCellH, Nat.add_sub_cancel]
  exact le_max_left _ _

/-- The column-recursive H values equal the gotohProcessRow output. -/
theorem gotohCellH_eq_processRow (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol : col ≤ b.length) :
    gotohCellH prev ai b go ge row col =
    (gotohProcessRow prev ai b go ge row).h.getD col NEG_INF := by
  sorry

theorem gotohProcessRow_diag_ge (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ)
    (hcol_ge : col ≥ 1) (hcol_le : col ≤ b.length) :
    (gotohProcessRow prev ai b go ge row).h.getD col NEG_INF ≥
    prev.h.getD (col - 1) 0 + (if ai == b.getD (col - 1) 0 then 1 else 0) := by
  rw [← gotohCellH_eq_processRow prev ai b go ge row col hcol_le]
  exact gotohCellH_ge_diag prev ai b go ge row col hcol_ge

/-- **Bridge Lemma 1 (gotoh_ge_diag)**: Gotoh DP score >= diagonal match count.

    The diagonal alignment path (no gaps) scores diagCount matches.
    Since the Gotoh DP maximizes over all paths, H[m][m] >= diagCount.

    Proof by induction on m using gotohAfterK:
    - Base: H[0][0] = 0 >= 0 = diagCount([], [])
    - Step: H[k+1][k+1] >= H[k][k] + match(a[k], b[k]) by gotohProcessRow_diag_ge
            >= diagCount(a[0..k], b[0..k]) + match(a[k], b[k]) by IH
            = diagCount(a[0..k+1], b[0..k+1]) -/
theorem gotoh_ge_diag (a b : List ℕ) (go ge : ℤ)
    (h_go : go ≥ 1) (h_ge : ge ≥ 1)
    (h_len : a.length = b.length) :
    gotohGlobalScore a b go ge ≥ (diagCount a b : ℤ) := by
  -- Key inductive invariant: H[k][k] >= partial diagonal match count at step k
  suffices h_inv : ∀ k : ℕ, k ≤ a.length →
      (gotohAfterK a b go ge k).h.getD k NEG_INF ≥
      ((List.range k).countP (fun i => a.getD i 0 == b.getD i 0) : ℤ) by
    -- Apply invariant at k = a.length
    have hm := h_inv a.length le_rfl
    -- Connect gotohAfterK to gotohGlobalScore
    show gotohGlobalScore a b go ge ≥ ↑(diagCount a b)
    unfold gotohGlobalScore diagCount
    have h_min : min a.length b.length = a.length := by omega
    rw [h_min]
    -- Now need: (gotohFinalRow a b go ge).h.getD b.length NEG_INF >= countP ...
    -- Use h_len to replace b.length with a.length
    conv_lhs => rw [show b.length = a.length from h_len.symm ▸ rfl]
    rw [← gotohAfterK_full]
    exact hm
  intro k
  induction k with
  | zero =>
    intro _
    simp [gotohAfterK, gotohInitRow]
  | succ n ih =>
    intro hn
    simp only [gotohAfterK]
    -- Use the step lemma: H[n+1][n+1] >= H_prev[n] + match(a[n], b[n])
    have h_n_le : n ≤ a.length := Nat.le_of_succ_le hn
    have h_n1_le_blen : n + 1 ≤ b.length := by omega
    have h_step := gotohProcessRow_diag_ge
      (gotohAfterK a b go ge n) (a.getD n 0) b go ge (n + 1) (n + 1)
      (by omega) h_n1_le_blen
    -- h_step: H[n+1][n+1] >= (gotohAfterK n).h.getD n 0 + matchScore
    -- IH: (gotohAfterK n).h.getD n NEG_INF >= countP n
    have h_ih := ih h_n_le
    -- countP (n+1) = countP n + (1 if match else 0)
    have h_countP : (List.range (n + 1)).countP (fun i => a.getD i 0 == b.getD i 0) =
        (List.range n).countP (fun i => a.getD i 0 == b.getD i 0) +
        if (a.getD n 0 == b.getD n 0) = true then 1 else 0 := by
      rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
      omega
    -- Bridge the getD defaults: h_step uses default 0, h_ih uses default NEG_INF
    -- The H list has length b.length + 1, and n < b.length + 1, so both defaults are irrelevant
    have h_hlen := gotohAfterK_h_length a b go ge n h_n_le
    have h_n_valid : n < (gotohAfterK a b go ge n).h.length := by rw [h_hlen]; omega
    rw [List.getD_default_irrel _ _ NEG_INF 0 h_n_valid] at h_ih
    -- Now h_ih: (gotohAfterK n).h.getD n 0 >= countP n
    -- h_step: H[n+1][n+1] >= (gotohAfterK n).h.getD n 0 + matchScore
    -- h_countP: countP(n+1) = countP(n) + if match then 1 else 0
    rw [h_countP]
    push_cast
    calc (gotohProcessRow (gotohAfterK a b go ge n) (a.getD n 0) b go ge (n + 1)).h.getD
            (n + 1) NEG_INF
        ≥ (gotohAfterK a b go ge n).h.getD n 0 +
          (if a.getD n 0 == b.getD n 0 then 1 else 0) := h_step
      _ ≥ ↑((List.range n).countP fun i => a.getD i 0 == b.getD i 0) +
          ↑(if (a.getD n 0 == b.getD n 0) = true then 1 else 0) := by
          have : (if a.getD n 0 == b.getD n 0 then (1 : ℤ) else 0) =
                 ↑(if (a.getD n 0 == b.getD n 0) = true then 1 else 0) := by
            split <;> simp_all
          linarith [this]

/-- **Bridge Lemma 2 (gotoh_le_diag_when_eps_small)**: When epsilon <= go,
    Gotoh DP score <= diagonal match count.

    Any alignment path with >= 1 gap opening scores at most LCS - go <= diag.
    The gap-free path scores diagCount. So gotohGlobalScore <= diag. -/
theorem gotoh_le_diag_when_eps_small (a b : List ℕ) (go ge : ℤ)
    (h_go : go ≥ 1) (h_ge : ge ≥ 1)
    (h_len : a.length = b.length)
    (h_eps : (lcsDP a b : ℤ) - (diagCount a b : ℤ) ≤ go) :
    gotohGlobalScore a b go ge ≤ (diagCount a b : ℤ) := by
  sorry

/-! ## The Score Determination Theorem (Statement)

**Theorem 1 (Score Determination)**: The correction formula score
equals the Gotoh DP score for equal-length alignment.

For any query `a` and reference `b` with `|a| = |b|`, gap open `go >= 1`,
and gap extension `ge >= 1`:

  correctionScoreDP a b go ge = gotohGlobalScore a b go ge

The correction formula works as follows:
1. Compute LCS via DP (or equivalently from comb d_col crossing count)
2. Compute diag (diagonal match count) from sequences
3. epsilon = LCS - diag (the excess)
4. If epsilon <= go: score = diag (Tier 1 or 2)
5. If epsilon > go: score = Gotoh DP (Tier 3, banded by epsilon)

For Tiers 1-2, the augmented comb output alone determines the score
(no DP needed). This covers ~99% of windows in practice.

For Tier 3, the augmented comb provides the band width epsilon,
reducing the DP from O(m^2) to O(m*epsilon).

The full Gotoh DP state (H, E, F vectors) is NOT determined by the
comb boundary alone (proved in PathSeparation.lean), but the scalar
SCORE is.
-/

/-- **Score Determination Theorem**: The correction formula score
    equals the Gotoh DP score for equal-length alignment.

    Verified concretely on 17+ test cases above. The general proof
    requires showing:
    1. LCS >= diag always (diagonal matches form a common subsequence)
    2. When epsilon <= go: no alignment can beat diagonal (CorrectionFormula.lean)
    3. When epsilon > go: the fallback IS the Gotoh DP (definitional)

    The non-trivial content is point (2), which is proved abstractly in
    CorrectionFormula.lean (correction_tier2) but requires connecting
    the abstract "crossing count" model to the concrete Gotoh DP. -/
theorem score_determination (a b : List ℕ) (go ge : ℤ)
    (h_go_pos : go ≥ 1) (h_ge_pos : ge ≥ 1)
    (h_same_len : a.length = b.length) :
    correctionScoreDP a b go ge = gotohGlobalScore a b go ge := by
  unfold correctionScoreDP
  simp only
  split
  · -- Case: epsilon <= go. Need: (diagCount a b : Z) = gotohGlobalScore a b go ge.
    -- By the two bridge lemmas: gotoh_ge_diag gives >=, gotoh_le_diag_when_eps_small gives <=.
    rename_i h_eps
    have h_ge_dir := gotoh_ge_diag a b go ge h_go_pos h_ge_pos h_same_len
    have h_le_dir := gotoh_le_diag_when_eps_small a b go ge h_go_pos h_ge_pos h_same_len h_eps
    linarith
  · -- Case: epsilon > go. Correction formula falls through to gotohGlobalScore.
    rfl

/-! ## Corollaries -/

/-- **Tier 1 Corollary**: When LCS = diag (epsilon = 0), score = diag.
    This is the most common case: ~78% for DNA, ~38-83% for RNA. -/
theorem score_det_tier1 (a b : List ℕ) (go ge : ℤ)
    (h_go_pos : go ≥ 1)
    (h_eps_zero : lcsDP a b = diagCount a b) :
    correctionScoreDP a b go ge = (diagCount a b : ℤ) := by
  unfold correctionScoreDP
  simp only
  have h_eps : (lcsDP a b : ℤ) - (diagCount a b : ℤ) = 0 := by
    rw [h_eps_zero]; simp
  simp only [h_eps]
  have h0 : (0 : ℤ) ≤ go := by omega
  simp [h0]

/-- **Tier 3 Corollary**: When epsilon > go, correction falls back to Gotoh DP.
    This is definitionally true (by the if-then-else in correctionScoreDP). -/
theorem score_det_tier3 (a b : List ℕ) (go ge : ℤ)
    (h_tier3 : (lcsDP a b : ℤ) - (diagCount a b : ℤ) > go) :
    correctionScoreDP a b go ge = gotohGlobalScore a b go ge := by
  unfold correctionScoreDP
  simp only
  split
  · omega
  · rfl

/-! ## Summary

The Score Determination theorem establishes:

1. The correction formula (LCS, diag, three-tier model) gives the same
   score as the Gotoh DP for equal-length alignment
2. For Tiers 1-2 (epsilon <= go): score = diag, no DP needed (~99% of cases)
3. For Tier 3 (epsilon > go): epsilon-banded DP suffices, band from LCS
4. The composition boundary (d_col, depth_col) does NOT determine the DP
   state vectors H, E, F (PathSeparation.lean), but it DOES determine
   the scalar score

Connected theorems:
- CorrectionFormula.lean: Tiers 1-2 proofs (epsilon <= go implies score = diag)
- BandSufficiency.lean: Tier 3 (epsilon-banded DP is exact)
- PathSeparation.lean: boundary does not determine DP state (score-path separation)
- CrossingCountLCS.lean: d_col crossing count = LCS
- Observer.lean: augmented comb labels = standard comb labels

This is the formal foundation for the skip-comb optimization:
- DNA pipeline: skip the comb entirely (seed -> diag -> skip-comb tier)
- RNA pipeline: comb for junction detection, correction formula for scoring
-/
