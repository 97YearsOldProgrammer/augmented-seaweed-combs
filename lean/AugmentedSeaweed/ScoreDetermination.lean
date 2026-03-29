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
  - gotoh_ge_diag: Gotoh DP >= diagCount (diagonal path is feasible) -- PROVED
  - gotoh_le_diag_when_eps_small: when eps <= go, Gotoh DP <= diagCount -- DECOMPOSED
    Proof body is sorry-free; depends on 12 helper lemma sorrys (LCS infrastructure).
  - gotohCellH_eq_processRow: column-recursive H = fold-based H -- PROVED
    (proved via fold decomposition infrastructure: gotohRowFoldStep, gotohRowFoldAfterK,
     head_eq invariant, getD on unreversed list, getD_reverse to connect to reversed output)

  SORRY STATUS (0 remaining — updated 2026-03-28):
  All 12 original helper sorrys proved. lcsCellDP_unit_col deleted (dead code).
  lcsAfterK_mono_row proved via joint unit_col/mono_row induction.
  gotoh_HEF_le_lcs proved via 2D fold induction (mutual H/E/F ≤ LCS bound).
  gotoh_diag_le_diagCount proved via diagonal induction + eps chain + cell decomposition.

  Paper reference: Theorem 1 (Score Determination)
-/
import Mathlib.Tactic
import Mathlib.Data.List.GetD
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

/-! ## Empirical Verification: gotoh_le_diag_when_eps_small

Direct verification that when epsilon <= go, gotohGlobalScore <= diagCount.
Tests cover: eps=0, eps=go (boundary), eps=go-1, various alphabets,
high extension penalties, all-mismatch, and longer strings. -/

/-- eps=0, exact match: score=3, diag=3 -/
theorem gotoh_le_diag_test1 :
    gotohGlobalScore [0,1,0] [0,1,0] 2 1 ≤ (diagCount [0,1,0] [0,1,0] : ℤ) := by native_decide

/-- eps=0, all mismatch: score=0, diag=0 -/
theorem gotoh_le_diag_test2 :
    gotohGlobalScore [0,0,0] [1,1,1] 1 1 ≤ (diagCount [0,0,0] [1,1,1] : ℤ) := by native_decide

/-- eps=3=go (boundary): score=0, diag=0 -/
theorem gotoh_le_diag_test3 :
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 3 1 ≤ (diagCount [0,1,0,1] [1,0,1,0] : ℤ) := by native_decide

/-- eps=3 < go=4: score=0, diag=0 -/
theorem gotoh_le_diag_test4 :
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 4 1 ≤ (diagCount [0,1,0,1] [1,0,1,0] : ℤ) := by native_decide

/-- eps=1=go, rotation: score=2, diag=2 -/
theorem gotoh_le_diag_test5 :
    gotohGlobalScore [0,0,0,1] [1,0,0,0] 1 1 ≤ (diagCount [0,0,0,1] [1,0,0,0] : ℤ) := by native_decide

/-- eps=1 < go=2: score=2, diag=2 -/
theorem gotoh_le_diag_test6 :
    gotohGlobalScore [0,0,0,1] [1,0,0,0] 2 1 ≤ (diagCount [0,0,0,1] [1,0,0,0] : ℤ) := by native_decide

/-- 3-letter alphabet, eps=1 <= go=2: score=2, diag=2 -/
theorem gotoh_le_diag_test7 :
    gotohGlobalScore [0,1,2,0] [0,2,1,0] 2 1 ≤ (diagCount [0,1,2,0] [0,2,1,0] : ℤ) := by native_decide

/-- high ge penalty, eps=3=go: score=0, diag=0 -/
theorem gotoh_le_diag_test8 :
    gotohGlobalScore [0,1,0,1] [1,0,1,0] 3 5 ≤ (diagCount [0,1,0,1] [1,0,1,0] : ℤ) := by native_decide

/-- longer strings, eps=5=go: score=0, diag=0 -/
theorem gotoh_le_diag_test9 :
    gotohGlobalScore [0,1,0,1,0,1] [1,0,1,0,1,0] 5 1 ≤
    (diagCount [0,1,0,1,0,1] [1,0,1,0,1,0] : ℤ) := by native_decide

/-- 5-char exact match, eps=0: score=5, diag=5 -/
theorem gotoh_le_diag_test10 :
    gotohGlobalScore [0,1,0,1,0] [0,1,0,1,0] 2 1 ≤
    (diagCount [0,1,0,1,0] [0,1,0,1,0] : ℤ) := by native_decide

/-- single char match, eps=0: score=1, diag=1 -/
theorem gotoh_le_diag_test11 :
    gotohGlobalScore [0] [0] 1 1 ≤ (diagCount [0] [0] : ℤ) := by native_decide

/-- single char mismatch, eps=0: score=0, diag=0 -/
theorem gotoh_le_diag_test12 :
    gotohGlobalScore [0] [1] 1 1 ≤ (diagCount [0] [1] : ℤ) := by native_decide

/-- empty strings: score=0, diag=0 -/
theorem gotoh_le_diag_test13 :
    gotohGlobalScore [] [] 1 1 ≤ (diagCount [] [] : ℤ) := by native_decide

/-- go=2, ge=2, eps=3>go=2: NOT in scope (eps > go), included for contrast -/
theorem gotoh_le_diag_test14_outofscope :
    -- When eps > go, the bound may not hold (this is Tier 3)
    (lcsDP [0,1,0,1] [1,0,1,0] : ℤ) - (diagCount [0,1,0,1] [1,0,1,0] : ℤ) > 2 := by native_decide

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

/-! ### Fold infrastructure for gotohCellH_eq_processRow

The fold in gotohProcessRow builds lists by prepending, then reverses.
We define the fold step and state after k steps, then prove the invariant:
after k fold steps, the head of the H list equals gotohCellH at column k. -/

/-- The fold step function used in gotohProcessRow, extracted for reasoning. -/
def gotohRowFoldStep (prev : GotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ)
    (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) : List ℤ × List ℤ × List ℤ :=
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

/-- The fold state after k steps of gotohProcessRow. -/
def gotohRowFoldAfterK (prev : GotohRow) (ai : ℕ) (b : List ℕ) (go ge : ℤ) (row : ℕ)
    (k : ℕ) : List ℤ × List ℤ × List ℤ :=
  let h0 : ℤ := -(go + ge * ((row : ℤ) - 1))
  let e0 : ℤ := h0
  let f0 : ℤ := NEG_INF
  let init : List ℤ × List ℤ × List ℤ := ([h0], [e0], [f0])
  (List.range k).foldl (gotohRowFoldStep prev ai b go ge) init

/-- gotohProcessRow result equals fold-after-n with reversal. -/
theorem gotohProcessRow_eq_foldAfterN (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row : ℕ) :
    (gotohProcessRow prev ai b go ge row).h =
    (gotohRowFoldAfterK prev ai b go ge row b.length).1.reverse := by
  unfold gotohProcessRow gotohRowFoldAfterK gotohRowFoldStep
  rfl

/-- The fold step adds exactly one element to the H list. -/
theorem gotohRowFoldStep_h_length (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) :
    (gotohRowFoldStep prev ai b go ge acc jIdx).1.length = acc.1.length + 1 := by
  simp [gotohRowFoldStep, List.length_cons]

/-- The fold step adds exactly one element to the F list. -/
theorem gotohRowFoldStep_f_length (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) :
    (gotohRowFoldStep prev ai b go ge acc jIdx).2.2.length = acc.2.2.length + 1 := by
  simp [gotohRowFoldStep, List.length_cons]

/-- After k fold steps, the H list has length k + 1. -/
theorem gotohRowFoldAfterK_h_length (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    (gotohRowFoldAfterK prev ai b go ge row k).1.length = k + 1 := by
  induction k with
  | zero => simp [gotohRowFoldAfterK]
  | succ n ih =>
    -- Rewrite in terms of the step
    have h_eq : gotohRowFoldAfterK prev ai b go ge row (n + 1) =
        gotohRowFoldStep prev ai b go ge (gotohRowFoldAfterK prev ai b go ge row n) n := by
      unfold gotohRowFoldAfterK
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [h_eq, gotohRowFoldStep_h_length, ih]

/-- After k fold steps, the F list has length k + 1. -/
theorem gotohRowFoldAfterK_f_length (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    (gotohRowFoldAfterK prev ai b go ge row k).2.2.length = k + 1 := by
  induction k with
  | zero => simp [gotohRowFoldAfterK, NEG_INF]
  | succ n ih =>
    have h_eq : gotohRowFoldAfterK prev ai b go ge row (n + 1) =
        gotohRowFoldStep prev ai b go ge (gotohRowFoldAfterK prev ai b go ge row n) n := by
      unfold gotohRowFoldAfterK
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [h_eq, gotohRowFoldStep_f_length, ih]

/-- The fold step relation: fold-after-(k+1) = foldStep applied to fold-after-k. -/
theorem gotohRowFoldAfterK_step (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    gotohRowFoldAfterK prev ai b go ge row (k + 1) =
    gotohRowFoldStep prev ai b go ge (gotohRowFoldAfterK prev ai b go ge row k) k := by
  unfold gotohRowFoldAfterK
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Key invariant: after k fold steps, the head of the H list is gotohCellH at column k,
    and the head of the F list is gotohCellF at column k.
    Both proved simultaneously since H and F are mutually recursive. -/
theorem gotohRowFoldAfterK_head_eq (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    (gotohRowFoldAfterK prev ai b go ge row k).1.head! = gotohCellH prev ai b go ge row k ∧
    (gotohRowFoldAfterK prev ai b go ge row k).2.2.head! = gotohCellF prev ai b go ge row k := by
  induction k with
  | zero =>
    constructor
    · simp [gotohRowFoldAfterK, gotohCellH]
    · simp [gotohRowFoldAfterK, gotohCellF, NEG_INF]
  | succ n ih =>
    obtain ⟨ih_h, ih_f⟩ := ih
    rw [gotohRowFoldAfterK_step prev ai b go ge row n]
    constructor
    · -- Head of H list after step n: fold step prepends hij, so head! = hij
      simp only [gotohRowFoldStep, List.head!_cons]
      -- Need to show the fold step computation = gotohCellH (n+1)
      -- The fold step at jIdx=n computes:
      --   hij = max(diag, max(eij, fij))
      -- where diag uses prev.h.getD n 0, fij uses head! of H and F lists
      -- gotohCellH (n+1) expands to the same computation with gotohCellH n and gotohCellF n
      -- By IH: head! H = gotohCellH n, head! F = gotohCellF n
      conv_rhs => rw [gotohCellH]
      simp only [Nat.add_sub_cancel]
      rw [← ih_h, ← ih_f]
    · -- Head of F list after step n
      simp only [gotohRowFoldStep, List.head!_cons]
      conv_rhs => rw [gotohCellF]
      rw [← ih_h, ← ih_f]

/-- The fold accumulator at position (k - col) in the unreversed list equals gotohCellH col.
    Equivalently: after reversal, position col gives gotohCellH col.
    We prove the unreversed version and use List.getD_reverse to connect. -/
theorem gotohRowFoldAfterK_getD (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k col : ℕ) (hcol : col ≤ k) :
    (gotohRowFoldAfterK prev ai b go ge row k).1.getD (k - col) NEG_INF =
    gotohCellH prev ai b go ge row col := by
  -- The fold accumulator after k steps has the form [H_k, H_{k-1}, ..., H_0].
  -- Position (k - col) gives H_col = gotohCellH col.
  -- Prove by induction on k.
  induction k with
  | zero =>
    have hcol0 : col = 0 := by omega
    subst hcol0
    simp [gotohRowFoldAfterK, gotohCellH]
  | succ n ih =>
    rw [gotohRowFoldAfterK_step]
    -- After step: (newH :: old.1), so position 0 is newH, position (j+1) is old[j]
    by_cases hcol_eq : col = n + 1
    · -- col = n + 1: position 0 in the prepended list = gotohCellH (n+1)
      subst hcol_eq
      -- The goal is: (gotohRowFoldStep ... n).1.getD 0 NEG_INF = gotohCellH ... (n+1)
      -- Position 0 after prepending = the prepended value = gotohCellH (n+1)
      -- Use unfold to expose both sides equally
      simp only [Nat.sub_self]
      -- Unfold both sides to their computational content
      unfold gotohRowFoldStep gotohCellH
      simp only [Nat.add_sub_cancel, List.getD, List.getElem?_cons_zero, Option.getD_some]
      -- Now both sides should use the same form; connect head! via IH
      have ⟨ih_h, ih_f⟩ := gotohRowFoldAfterK_head_eq prev ai b go ge row n
      rw [← ih_h, ← ih_f]
    · -- col ≤ n: position (n+1-col) in the prepended list = position (n-col) in old
      have hcol_le_n : col ≤ n := by omega
      have h_pos : n + 1 - col = (n - col) + 1 := by omega
      rw [h_pos]
      simp only [gotohRowFoldStep, List.getD, List.getElem?_cons_succ]
      exact ih hcol_le_n

/-- For the fold accumulator, reverse.getD col = gotohCellH col. -/
theorem gotohRowFoldAfterK_reverse_getD (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k col : ℕ) (hcol : col ≤ k) :
    (gotohRowFoldAfterK prev ai b go ge row k).1.reverse.getD col NEG_INF =
    gotohCellH prev ai b go ge row col := by
  -- Use getD_reverse to convert to unreversed access
  have h_len := gotohRowFoldAfterK_h_length prev ai b go ge row k
  have h_col_lt : col < (gotohRowFoldAfterK prev ai b go ge row k).1.length := by
    rw [h_len]; omega
  rw [List.getD_reverse col h_col_lt]
  -- Now goal: getD (foldAfterK k).1 ((foldAfterK k).1.length - 1 - col) NEG_INF = gotohCellH col
  rw [h_len]
  -- goal: getD (foldAfterK k).1 (k + 1 - 1 - col) NEG_INF = gotohCellH col
  have : k + 1 - 1 - col = k - col := by omega
  rw [this]
  exact gotohRowFoldAfterK_getD prev ai b go ge row k col hcol

/-- The column-recursive H values equal the gotohProcessRow output. -/
theorem gotohCellH_eq_processRow (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol : col ≤ b.length) :
    gotohCellH prev ai b go ge row col =
    (gotohProcessRow prev ai b go ge row).h.getD col NEG_INF := by
  rw [gotohProcessRow_eq_foldAfterN]
  exact (gotohRowFoldAfterK_reverse_getD prev ai b go ge row b.length col hcol).symm

/-- The fold accumulator F list at position (k - col) equals gotohCellF col.
    Analogous to gotohRowFoldAfterK_getD but for the F component. -/
theorem gotohRowFoldAfterK_f_getD (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k col : ℕ) (hcol : col ≤ k) :
    (gotohRowFoldAfterK prev ai b go ge row k).2.2.getD (k - col) NEG_INF =
    gotohCellF prev ai b go ge row col := by
  induction k with
  | zero =>
    have hcol0 : col = 0 := by omega
    subst hcol0
    simp [gotohRowFoldAfterK, gotohCellF]
  | succ n ih =>
    rw [gotohRowFoldAfterK_step]
    by_cases hcol_eq : col = n + 1
    · subst hcol_eq
      simp only [Nat.sub_self]
      unfold gotohRowFoldStep gotohCellF
      simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
      have ⟨ih_h, ih_f⟩ := gotohRowFoldAfterK_head_eq prev ai b go ge row n
      rw [← ih_h, ← ih_f]
    · have hcol_le_n : col ≤ n := by omega
      have h_pos : n + 1 - col = (n - col) + 1 := by omega
      rw [h_pos]
      simp only [gotohRowFoldStep, List.getD, List.getElem?_cons_succ]
      exact ih hcol_le_n

/-- For the fold accumulator, reverse.getD col for F = gotohCellF col. -/
theorem gotohRowFoldAfterK_f_reverse_getD (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k col : ℕ) (hcol : col ≤ k) :
    (gotohRowFoldAfterK prev ai b go ge row k).2.2.reverse.getD col NEG_INF =
    gotohCellF prev ai b go ge row col := by
  have h_len := gotohRowFoldAfterK_f_length prev ai b go ge row k
  have h_col_lt : col < (gotohRowFoldAfterK prev ai b go ge row k).2.2.length := by
    rw [h_len]; omega
  rw [List.getD_reverse col h_col_lt, h_len]
  have : k + 1 - 1 - col = k - col := by omega
  rw [this]
  exact gotohRowFoldAfterK_f_getD prev ai b go ge row k col hcol

/-- The column-recursive F values equal the gotohProcessRow F output. -/
theorem gotohCellF_eq_processRow (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row col : ℕ) (hcol : col ≤ b.length) :
    gotohCellF prev ai b go ge row col =
    (gotohProcessRow prev ai b go ge row).f.getD col NEG_INF := by
  have : (gotohProcessRow prev ai b go ge row).f =
      (gotohRowFoldAfterK prev ai b go ge row b.length).2.2.reverse := by
    unfold gotohProcessRow gotohRowFoldAfterK gotohRowFoldStep; rfl
  rw [this]
  exact (gotohRowFoldAfterK_f_reverse_getD prev ai b go ge row b.length col hcol).symm

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

/-! ### LCS DP infrastructure for upper bound proof

The proof of gotoh_le_diag_when_eps_small requires:
1. A mutual H/E/F upper bound: H[i][j] <= lcsDP(take i, take j),
   E[i][j] <= lcsDP(take i, take j) - go, F[i][j] <= lcsDP(take i, take j) - go
2. The eps-non-decreasing property: eps(prefix k) <= eps(full) for diagonal prefixes
3. Diagonal induction: H[k][k] <= diagCount(take k, take k)

Key insight: eps = lcsDP - diagCount is non-decreasing along the diagonal because
at a match, lcsDP increases by exactly 1 and diagCount increases by 1 (eps unchanged);
at a mismatch, lcsDP increases by 0 or 1 and diagCount stays (eps non-decreasing).
This means eps(prefix) <= eps(full) <= go for ALL prefixes, unblocking Option B.

The previous SORRY STATUS incorrectly claimed "eps(prefix) <= go does NOT follow from
eps(full) <= go". It DOES follow from the monotonicity of eps along the diagonal. -/

/-- Recursive LCS DP row after processing k characters of a.
    lcsAfterK a b k = [dp[k][0], dp[k][1], ..., dp[k][b.length]]. -/
def lcsAfterK (a b : List ℕ) : ℕ → List ℕ
  | 0 => List.replicate (b.length + 1) 0
  | k + 1 =>
    let prev := lcsAfterK a b k
    let ai := a.getD k 0
    (List.range b.length).foldl (fun (curr : List ℕ) (j : ℕ) =>
      let bj := b.getD j 0
      let val := if ai == bj then prev.getD j 0 + 1
                 else max (prev.getD (j + 1) 0) (curr.getD j 0)
      curr ++ [val]
    ) [0]

/-- lcsAfterK has the correct length. -/
theorem lcsAfterK_length (a b : List ℕ) (k : ℕ) :
    (lcsAfterK a b k).length = b.length + 1 := by
  induction k with
  | zero => simp [lcsAfterK]
  | succ k ih =>
    simp only [lcsAfterK]
    have key : ∀ (n : ℕ) (init : List ℕ) (f : List ℕ → ℕ → ℕ),
      ((List.range n).foldl (fun curr j => curr ++ [f curr j]) init).length = init.length + n := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        intro init f
        rw [List.range_succ, List.foldl_concat]
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [ihn]
        omega
    simp [key]; omega

/-- lcsDP equals lcsAfterK at full length. -/
theorem lcsDP_eq_lcsAfterK (a b : List ℕ) :
    lcsDP a b = (lcsAfterK a b a.length).getD b.length 0 := by
  simp only [lcsDP]
  congr 1
  -- Prove: a.foldl g init = lcsAfterK a b a.length
  -- by induction on k via take
  have h : ∀ k, k ≤ a.length →
      (a.take k).foldl (fun (prev : List ℕ) (ai : ℕ) =>
        (List.range b.length).foldl (fun (curr : List ℕ) (j : ℕ) =>
          let bj := b.getD j 0
          let val := if ai == bj then prev.getD j 0 + 1
                     else max (prev.getD (j + 1) 0) (curr.getD j 0)
          curr ++ [val]) [0]) (List.replicate (b.length + 1) 0) = lcsAfterK a b k := by
    intro k; induction k with
    | zero => intro _; simp [lcsAfterK]
    | succ k ih =>
      intro hk
      have hklt : k < a.length := by omega
      rw [List.take_succ_eq_append_getElem hklt, List.foldl_concat, ih (by omega)]
      simp only [lcsAfterK]
      apply List.foldl_ext; intro curr j _
      simp [List.getElem?_eq_getElem hklt]
  have h₀ := h a.length le_rfl
  rw [List.take_length] at h₀
  exact h₀

/-! ### Infrastructure: getD of foldl-with-append -/

private theorem foldl_append_length {f : List ℕ → ℕ → ℕ} {init : ℕ} (n : ℕ) :
    ((List.range n).foldl (fun curr j => curr ++ [f curr j]) [init]).length = n + 1 := by
  induction n with
  | zero => simp
  | succ n ihn =>
    rw [List.range_succ, List.foldl_concat, List.length_append, List.length_cons,
        List.length_nil, ihn]

/-- Stability: getD i of partial fold at step k = getD i at step n, for i ≤ k ≤ n. -/
private theorem foldl_append_stable {f : List ℕ → ℕ → ℕ} {init : ℕ} {n : ℕ}
    (i k : ℕ) (hi : i ≤ k) (hk : k ≤ n) :
    ((List.range k).foldl (fun curr j => curr ++ [f curr j]) [init]).getD i 0 =
    ((List.range n).foldl (fun curr j => curr ++ [f curr j]) [init]).getD i 0 := by
  induction n with
  | zero => have := Nat.le_zero.mp hk; subst this; rfl
  | succ n ihn =>
    by_cases hkn : k ≤ n
    · rw [ihn hkn, List.range_succ, List.foldl_concat,
          List.getD_append _ _ _ _ (by rw [foldl_append_length]; omega)]
    · have hkeq : k = n + 1 := by omega
      rw [hkeq]

/-- getD (j+1) of the full fold = the value appended at step j. -/
private theorem foldl_append_getD_succ {f : List ℕ → ℕ → ℕ} {init : ℕ} {n : ℕ}
    (j : ℕ) (hj : j < n) :
    ((List.range n).foldl (fun curr j => curr ++ [f curr j]) [init]).getD (j + 1) 0 =
    f ((List.range j).foldl (fun curr j => curr ++ [f curr j]) [init]) j := by
  rw [← foldl_append_stable (j + 1) (j + 1) le_rfl (by omega)]
  rw [show List.range (j + 1) = List.range j ++ [j] from List.range_succ]
  rw [List.foldl_concat,
      List.getD_append_right _ _ _ _ (by rw [foldl_append_length])]
  simp [foldl_append_length]

/-- lcsAfterK DP recurrence: the value at cell (k+1, j+1). -/
theorem lcsAfterK_recurrence (a b : List ℕ) (k j : ℕ)
    (_hk : k < a.length) (hj : j < b.length) :
    (lcsAfterK a b (k + 1)).getD (j + 1) 0 =
      if a.getD k 0 == b.getD j 0 then (lcsAfterK a b k).getD j 0 + 1
      else max ((lcsAfterK a b k).getD (j + 1) 0) ((lcsAfterK a b (k + 1)).getD j 0) := by
  simp only [lcsAfterK]
  rw [foldl_append_getD_succ j hj]
  congr 1
  rw [foldl_append_stable j j le_rfl (by omega : j ≤ b.length)]

/-- lcsAfterK zero column is always 0. -/
theorem lcsAfterK_zero_col (a b : List ℕ) (k : ℕ) :
    (lcsAfterK a b k).getD 0 0 = 0 := by
  induction k with
  | zero => simp [lcsAfterK]
  | succ k _ =>
    simp only [lcsAfterK]
    rw [← foldl_append_stable 0 0 le_rfl (by omega : 0 ≤ b.length)]
    simp

/-- Joint proof of mono_col and unit_row by outer induction on k, inner induction on j.
    For each k ≤ a.length and j < b.length:
    - mono_col: dp[k][j+1] ≥ dp[k][j]
    - unit_row: dp[k+1][j+1] ≤ dp[k][j+1] + 1  (when k < a.length) -/
private theorem lcsAfterK_col_row_props (a b : List ℕ) (k : ℕ) (hk : k ≤ a.length) :
    (∀ j, j < b.length →
      (lcsAfterK a b k).getD (j + 1) 0 ≥ (lcsAfterK a b k).getD j 0) ∧
    (∀ j, j ≤ b.length → k > 0 →
      (lcsAfterK a b k).getD j 0 ≤ (lcsAfterK a b (k - 1)).getD j 0 + 1) := by
  induction k with
  | zero =>
    exact ⟨fun _ _ => by simp [lcsAfterK], fun _ _ hk0 => absurd hk0 (by omega)⟩
  | succ k ih =>
    have ⟨mono_col_k, _⟩ := ih (by omega)
    -- Inner joint induction: for each j < b.length, prove
    --   unit_row(k+1, j+1): result[j+1] ≤ prev[j+1] + 1
    --   mono_col(k+1, j):   result[j+1] ≥ result[j]
    -- where result = lcsAfterK a b (k+1), prev = lcsAfterK a b k
    have inner : ∀ j, j < b.length →
        ((lcsAfterK a b (k + 1)).getD (j + 1) 0 ≤ (lcsAfterK a b k).getD (j + 1) 0 + 1) ∧
        ((lcsAfterK a b (k + 1)).getD (j + 1) 0 ≥ (lcsAfterK a b (k + 1)).getD j 0) := by
      intro j hj
      induction j with
      | zero =>
        rw [lcsAfterK_recurrence a b k 0 (by omega) (by omega)]
        constructor
        · split
          · exact Nat.succ_le_succ (mono_col_k 0 (by omega))
          · exact Nat.max_le.mpr ⟨by omega, by rw [lcsAfterK_zero_col]; omega⟩
        · -- mono_col at j=0: result[1] ≥ result[0] = 0
          simp only [lcsAfterK_zero_col]
          split <;> omega
      | succ j' ihj =>
        have ⟨unit_j', _⟩ := ihj (by omega)
        rw [lcsAfterK_recurrence a b k (j' + 1) (by omega) (by omega)]
        constructor
        · -- unit_row at j'+2: result[j'+2] ≤ prev[j'+2] + 1
          split
          · -- match: prev[j'+1]+1 ≤ prev[j'+2]+1
            exact Nat.succ_le_succ (mono_col_k (j' + 1) (by omega))
          · -- mismatch: max(prev[j'+2], result[j'+1]) ≤ prev[j'+2]+1
            apply Nat.max_le.mpr
            constructor
            · omega
            · -- result[j'+1] ≤ prev[j'+2]+1: by unit_j' and mono_col_k
              calc (lcsAfterK a b (k + 1)).getD (j' + 1) 0
                  ≤ (lcsAfterK a b k).getD (j' + 1) 0 + 1 := unit_j'
                _ ≤ (lcsAfterK a b k).getD (j' + 2) 0 + 1 :=
                    Nat.add_le_add_right (mono_col_k (j' + 1) (by omega)) 1
        · -- mono_col at j'+1: result[j'+2] ≥ result[j'+1]
          split
          · -- match: prev[j'+1]+1 ≥ result[j'+1], by unit_row at j'+1
            exact unit_j'
          · -- mismatch: max(...) ≥ result[j'+1]
            exact le_max_right _ _
    constructor
    · -- mono_col(k+1)
      intro j hj
      by_cases hj' : j = 0
      · subst hj'; rw [lcsAfterK_zero_col]; omega
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj'
        -- j = j'+1, need result[j'+2] ≥ result[j'+1], which is inner at j'+1
        exact (inner (j' + 1) hj).2
    · -- unit_row(k+1)
      intro j hj _
      simp only [Nat.succ_sub_one]
      by_cases hj0 : j = 0
      · subst hj0; rw [lcsAfterK_zero_col]; omega
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        -- j = j'+1, need result[j'+1] ≤ prev[j'+1]+1, which is inner at j'
        exact (inner j' (by omega)).1

/-- Unit column increase: dp[k][j+1] ≤ dp[k][j] + 1.
    Adding one more character of b increases LCS by at most 1.
    Proved jointly with row monotonicity by induction on k. -/
private theorem lcsAfterK_unit_col (a b : List ℕ) :
    ∀ k, k ≤ a.length → ∀ j, j < b.length →
      (lcsAfterK a b k).getD (j + 1) 0 ≤ (lcsAfterK a b k).getD j 0 + 1 := by
  intro k
  induction k with
  | zero =>
    intro _ j _
    simp [lcsAfterK]
  | succ k ih =>
    intro hk j hj
    have unit_col_k := ih (by omega)
    -- Derive mono_row(k) from unit_col(k)
    have mono_row_k : ∀ j', j' ≤ b.length →
        (lcsAfterK a b (k + 1)).getD j' 0 ≥ (lcsAfterK a b k).getD j' 0 := by
      intro j' hj'
      induction j' with
      | zero =>
        have h1 := lcsAfterK_zero_col a b k
        have h2 := lcsAfterK_zero_col a b (k + 1)
        omega
      | succ j' _ =>
        rw [lcsAfterK_recurrence a b k j' (by omega) (by omega)]
        split
        · exact unit_col_k j' (by omega)
        · exact le_max_left _ _
    rw [lcsAfterK_recurrence a b k j (by omega) hj]
    split
    · -- match: dp[k][j]+1 ≤ dp[k+1][j]+1
      exact Nat.succ_le_succ (mono_row_k j (by omega))
    · -- mismatch: max(dp[k][j+1], dp[k+1][j]) ≤ dp[k+1][j]+1
      apply Nat.max_le.mpr
      constructor
      · calc (lcsAfterK a b k).getD (j + 1) 0
            ≤ (lcsAfterK a b k).getD j 0 + 1 := unit_col_k j hj
          _ ≤ (lcsAfterK a b (k + 1)).getD j 0 + 1 :=
              Nat.add_le_add_right (mono_row_k j (by omega)) 1
      · omega

/-- LCS monotonicity in rows: dp[i+1][j] >= dp[i][j].
    Processing more characters of a can only increase LCS. -/
theorem lcsAfterK_mono_row (a b : List ℕ) (k j : ℕ) (hk : k < a.length)
    (hj : j ≤ b.length) :
    (lcsAfterK a b (k + 1)).getD j 0 ≥ (lcsAfterK a b k).getD j 0 := by
  have unit_col_k := lcsAfterK_unit_col a b k (by omega)
  induction j with
  | zero =>
    have h1 := lcsAfterK_zero_col a b k
    have h2 := lcsAfterK_zero_col a b (k + 1)
    omega
  | succ j _ =>
    rw [lcsAfterK_recurrence a b k j hk (by omega)]
    split
    · exact unit_col_k j (by omega)
    · exact le_max_left _ _

/-- LCS monotonicity in columns: dp[i][j+1] >= dp[i][j]. -/
theorem lcsAfterK_mono_col (a b : List ℕ) (k j : ℕ) (hk : k ≤ a.length)
    (hj : j < b.length) :
    (lcsAfterK a b k).getD (j + 1) 0 ≥ (lcsAfterK a b k).getD j 0 :=
  (lcsAfterK_col_row_props a b k hk).1 j hj

/-- LCS match extension: if a[k] = b[j], dp[k+1][j+1] >= dp[k][j] + 1. -/
theorem lcsAfterK_match_extend (a b : List ℕ) (k j : ℕ) (hk : k < a.length)
    (hj : j < b.length) (hmatch : a.getD k 0 == b.getD j 0) :
    (lcsAfterK a b (k + 1)).getD (j + 1) 0 ≥ (lcsAfterK a b k).getD j 0 + 1 := by
  rw [lcsAfterK_recurrence a b k j hk hj, if_pos hmatch]

/-- LCS unit increase in rows: dp[k+1][j] <= dp[k][j] + 1. -/
theorem lcsAfterK_unit_row (a b : List ℕ) (k j : ℕ) (hk : k < a.length)
    (hj : j ≤ b.length) :
    (lcsAfterK a b (k + 1)).getD j 0 ≤ (lcsAfterK a b k).getD j 0 + 1 := by
  have h := (lcsAfterK_col_row_props a b (k + 1) (by omega)).2 j hj (by omega)
  simp at h; exact h

/-! ### Mutual H/E/F upper bound by LCS

Key invariant: for all rows i and columns j:
  H[i][j] <= lcsDP(a.take i, b.take j)      (Z cast)
  E[i][j] <= lcsDP(a.take i, b.take j) - go  (gapped paths pay >= go)
  F[i][j] <= lcsDP(a.take i, b.take j) - go -/

/-- The Gotoh E value at cell (i, j), extracted from gotohAfterK. -/
def gotohE_at (a b : List ℕ) (go ge : ℤ) (i j : ℕ) : ℤ :=
  (gotohAfterK a b go ge i).e.getD j NEG_INF

/-- The Gotoh F value at cell (i, j), extracted from gotohAfterK. -/
def gotohF_at (a b : List ℕ) (go ge : ℤ) (i j : ℕ) : ℤ :=
  (gotohAfterK a b go ge i).f.getD j NEG_INF

/-- The Gotoh H value at cell (i, j), extracted from gotohAfterK. -/
def gotohH_at (a b : List ℕ) (go ge : ℤ) (i j : ℕ) : ℤ :=
  (gotohAfterK a b go ge i).h.getD j NEG_INF

/-- Normalize getElem? form back to getD form (definitionally equal). -/
private theorem getD_unfold {α : Type*} (l : List α) (i : ℕ) (d : α) :
    (l[i]?).getD d = l.getD i d := rfl

private theorem cons_getD_zero {α : Type*} (x : α) (l : List α) (d : α) :
    (x :: l).getD 0 d = x := by simp [List.getD]

private theorem cons_getD_succ {α : Type*} (x : α) (l : List α) (n : ℕ) (d : α) :
    (x :: l).getD (n + 1) d = l.getD n d := by simp [List.getD]

/-- For a non-empty ℤ list, head! equals getD 0 with any default. -/
private theorem head!_eq_getD (l : List ℤ) (d : ℤ) (h : l.length > 0) :
    l.head! = l.getD 0 d := by
  match l, h with
  | x :: _, _ => simp [List.head!, List.getD]

/-- gotohProcessRow E list equals fold-after-n with reversal. -/
theorem gotohProcessRow_e_eq_foldAfterN (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row : ℕ) :
    (gotohProcessRow prev ai b go ge row).e =
    (gotohRowFoldAfterK prev ai b go ge row b.length).2.1.reverse := by
  unfold gotohProcessRow gotohRowFoldAfterK gotohRowFoldStep; rfl

/-- gotohProcessRow F list equals fold-after-n with reversal. -/
theorem gotohProcessRow_f_eq_foldAfterN (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row : ℕ) :
    (gotohProcessRow prev ai b go ge row).f =
    (gotohRowFoldAfterK prev ai b go ge row b.length).2.2.reverse := by
  unfold gotohProcessRow gotohRowFoldAfterK gotohRowFoldStep; rfl

/-- The fold step adds exactly one element to the E list. -/
theorem gotohRowFoldStep_e_length (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (acc : List ℤ × List ℤ × List ℤ) (jIdx : ℕ) :
    (gotohRowFoldStep prev ai b go ge acc jIdx).2.1.length = acc.2.1.length + 1 := by
  simp [gotohRowFoldStep, List.length_cons]

/-- After k fold steps, the E list has length k + 1. -/
theorem gotohRowFoldAfterK_e_length (prev : GotohRow) (ai : ℕ) (b : List ℕ)
    (go ge : ℤ) (row k : ℕ) :
    (gotohRowFoldAfterK prev ai b go ge row k).2.1.length = k + 1 := by
  induction k with
  | zero => simp [gotohRowFoldAfterK]
  | succ n ih =>
    rw [gotohRowFoldAfterK_step, gotohRowFoldStep_e_length, ih]

/-- Mutual bound: H[i][j] <= lcsAfterK(i, j) (as integers).
    E[i][j] <= lcsAfterK(i, j) - go.
    F[i][j] <= lcsAfterK(i, j) - go.
    This is the core inductive invariant for the upper bound proof.

    Proof by outer induction on i (row), inner fold invariant on j (column).
    The fold invariant tracks bounds at all processed columns simultaneously. -/
theorem gotoh_HEF_le_lcs (a b : List ℕ) (go ge : ℤ)
    (h_go : go ≥ 1) (h_ge : ge ≥ 1)
    (h_neg : NEG_INF ≤ -go)  -- sentinel bound: go ≤ 999999
    (i j : ℕ)
    (hi : i ≤ a.length) (hj : j ≤ b.length) :
    gotohH_at a b go ge i j ≤ ((lcsAfterK a b i).getD j 0 : ℤ) ∧
    gotohE_at a b go ge i j ≤ ((lcsAfterK a b i).getD j 0 : ℤ) - go ∧
    gotohF_at a b go ge i j ≤ ((lcsAfterK a b i).getD j 0 : ℤ) - go := by
  -- Reformulate: prove for all rows and columns
  suffices main : ∀ i, i ≤ a.length → ∀ j, j ≤ b.length →
      (gotohAfterK a b go ge i).h.getD j NEG_INF ≤ ↑((lcsAfterK a b i).getD j 0) ∧
      (gotohAfterK a b go ge i).e.getD j NEG_INF ≤ ↑((lcsAfterK a b i).getD j 0) - go ∧
      (gotohAfterK a b go ge i).f.getD j NEG_INF ≤ ↑((lcsAfterK a b i).getD j 0) - go by
    exact main i hi j hj
  intro i
  induction i with
  | zero =>
    -- Row 0: gotohInitRow — H[0][j] = 0, E[0][j] = F[0][j] = NEG_INF
    intro _ j hj
    simp only [gotohAfterK, gotohInitRow, lcsAfterK]
    have hj_lt : j < b.length + 1 := by omega
    have hH : (List.replicate (b.length + 1) (0 : ℤ)).getD j NEG_INF = 0 :=
      List.getD_replicate 0 hj_lt
    have hLCS : (List.replicate (b.length + 1) (0 : ℕ)).getD j 0 = 0 :=
      List.getD_replicate 0 hj_lt
    have hNI : (List.replicate (b.length + 1) NEG_INF).getD j NEG_INF = NEG_INF :=
      List.getD_replicate NEG_INF hj_lt
    refine ⟨by rw [hH, hLCS]; simp, by rw [hNI, hLCS]; simp; linarith, by rw [hNI, hLCS]; simp; linarith⟩
  | succ i ih =>
    intro hi j hj
    -- Row i+1: gotohProcessRow applied to prev = gotohAfterK(i)
    set prev := gotohAfterK a b go ge i with h_prev
    set ai := a.getD i 0 with h_ai
    have ih_all := ih (by omega)
    -- gotohAfterK(i+1) = gotohProcessRow(prev, ai, b, go, ge, i+1)
    have h_row : gotohAfterK a b go ge (i + 1) = gotohProcessRow prev ai b go ge (i + 1) := by
      simp [gotohAfterK, h_prev, h_ai]
    -- The fold invariant: after k fold steps, for all col ≤ k, bounds hold
    -- at position (k - col) in the fold state
    suffices fold_inv : ∀ k, k ≤ b.length → ∀ col, col ≤ k →
        let st := gotohRowFoldAfterK prev ai b go ge (i + 1) k
        st.1.getD (k - col) NEG_INF ≤ ↑((lcsAfterK a b (i + 1)).getD col 0) ∧
        st.2.1.getD (k - col) NEG_INF ≤ ↑((lcsAfterK a b (i + 1)).getD col 0) - go ∧
        st.2.2.getD (k - col) NEG_INF ≤ ↑((lcsAfterK a b (i + 1)).getD col 0) - go by
      -- Connect fold invariant at k=b.length, col=j to gotohAfterK(i+1) via reverse
      have fi := fold_inv b.length le_rfl j hj
      rw [h_row]
      -- H component
      have h_hlen := gotohRowFoldAfterK_h_length prev ai b go ge (i + 1) b.length
      have h_elen := gotohRowFoldAfterK_e_length prev ai b go ge (i + 1) b.length
      have h_flen := gotohRowFoldAfterK_f_length prev ai b go ge (i + 1) b.length
      rw [gotohProcessRow_eq_foldAfterN, gotohProcessRow_e_eq_foldAfterN,
          gotohProcessRow_f_eq_foldAfterN]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.getD_reverse j (by rw [h_hlen]; omega), h_hlen,
            show b.length + 1 - 1 - j = b.length - j from by omega]; exact fi.1
      · rw [List.getD_reverse j (by rw [h_elen]; omega), h_elen,
            show b.length + 1 - 1 - j = b.length - j from by omega]; exact fi.2.1
      · rw [List.getD_reverse j (by rw [h_flen]; omega), h_flen,
            show b.length + 1 - 1 - j = b.length - j from by omega]; exact fi.2.2
    -- Prove the fold invariant by induction on k
    intro k
    induction k with
    | zero =>
      intro _ col hcol
      have : col = 0 := by omega
      subst this
      simp only [Nat.sub_zero, gotohRowFoldAfterK, List.range_zero, List.foldl_nil, getD_unfold]
      have hzero := lcsAfterK_zero_col a b (i + 1)
      have sgD : ∀ (x d : ℤ), [x].getD 0 d = x := fun x d => by simp [List.getD]
      have hi_cast : (↑i : ℤ) ≥ 0 := Int.ofNat_nonneg i
      have h_prod : ge * ((↑i : ℤ) + 1 - 1) ≥ 0 := by nlinarith
      refine ⟨?_, ?_, ?_⟩ <;> { simp only [sgD, hzero]; push_cast; linarith }
    | succ k ihk =>
      intro hk col hcol
      rw [gotohRowFoldAfterK_step]
      by_cases hcol_new : col = k + 1
      · -- New column (col = k+1): bound the head values of the fold step
        subst hcol_new; simp only [Nat.sub_self]
        -- Get bounds from invariant at col=k (getD 0 of state_k)
        have ihk_at_k := ihk (by omega) k le_rfl
        simp only [Nat.sub_self] at ihk_at_k
        -- Get prev row bounds at col k+1 and col k
        have ih_prev := ih_all (k + 1) (by omega)
        have ih_diag := ih_all k (by omega)
        -- Length bounds for non-emptiness
        have hh_len := gotohRowFoldAfterK_h_length prev ai b go ge (i + 1) k
        have hf_len := gotohRowFoldAfterK_f_length prev ai b go ge (i + 1) k
        -- Default correction: prev.h.getD j 0 = prev.h.getD j NEG_INF for valid j
        have h_hlen_prev := gotohAfterK_h_length a b go ge i (by omega)
        -- Connect head! to getD 0 NEG_INF (for non-empty fold state lists)
        set st := gotohRowFoldAfterK prev ai b go ge (i + 1) k with h_st
        have hd_h := head!_eq_getD st.1 NEG_INF (by rw [hh_len]; omega)
        have hd_f := head!_eq_getD st.2.2 NEG_INF (by rw [hf_len]; omega)
        -- The fold step produces (hij :: st.1, eij :: st.2.1, fij :: st.2.2)
        -- After the fold step, getD 0 of the new list is the prepended value
        simp only [gotohRowFoldStep, cons_getD_zero, getD_unfold]
        -- Monotonicity bounds
        have hmr := lcsAfterK_mono_row a b i (k + 1) (by omega) (by omega)
        have hmc := lcsAfterK_mono_col a b (i + 1) k (by omega) (by omega)
        have hmrk := lcsAfterK_mono_row a b i k (by omega) (by omega)
        -- Default correction for prev.h in gotohRowFoldStep
        have h_def_h : prev.h.getD (k + 1) 0 = prev.h.getD (k + 1) NEG_INF :=
          List.getD_default_irrel prev.h (k + 1) 0 NEG_INF (by rw [h_hlen_prev]; omega)
        have h_def_hk : prev.h.getD k 0 = prev.h.getD k NEG_INF :=
          List.getD_default_irrel prev.h k 0 NEG_INF (by rw [h_hlen_prev]; omega)
        -- E bound: max(prev.h[k+1] - go, prev.e[k+1] - ge) ≤ lcs(i+1, k+1) - go
        have h_eij : max (prev.h.getD (k + 1) 0 - go) (prev.e.getD (k + 1) NEG_INF - ge)
            ≤ ↑((lcsAfterK a b (i + 1)).getD (k + 1) 0) - go := by
          apply max_le
          · rw [h_def_h]; linarith [ih_prev.1, Int.ofNat_le.mpr hmr]
          · linarith [ih_prev.2.1, Int.ofNat_le.mpr hmr]
        -- F bound: max(st.H_head - go, st.F_head - ge) ≤ lcs(i+1, k+1) - go
        have h_fij : max (st.1.head! - go) (st.2.2.head! - ge)
            ≤ ↑((lcsAfterK a b (i + 1)).getD (k + 1) 0) - go := by
          rw [hd_h, hd_f]
          apply max_le
          · linarith [ihk_at_k.1, Int.ofNat_le.mpr hmc]
          · linarith [ihk_at_k.2.2, Int.ofNat_le.mpr hmc]
        refine ⟨?_, h_eij, h_fij⟩
        -- H bound: max(diag, max(eij, fij)) ≤ lcs(i+1, k+1)
        apply max_le
        · -- Diagonal: prev.h[k] + matchScore ≤ lcs(i+1, k+1)
          simp only [getD_unfold, show k + 1 - 1 = k from by omega]
          rw [h_def_hk]
          by_cases hmatch : (ai == b.getD k 0)
          · simp only [hmatch, ite_true]
            have hme := lcsAfterK_match_extend a b i k (by omega) (by omega) hmatch
            linarith [ih_diag.1, Int.ofNat_le.mpr hme]
          · simp only [hmatch, Bool.false_eq_true, ite_false]
            linarith [ih_diag.1, Int.ofNat_le.mpr hmrk, Int.ofNat_le.mpr hmc]
        · apply max_le <;> linarith
      · -- Old column: preserved by prepend
        have hcol_le : col ≤ k := by omega
        have h_shift : k + 1 - col = (k - col) + 1 := by omega
        simp only [show gotohRowFoldAfterK prev ai b go ge (i + 1) (k + 1) =
          gotohRowFoldStep prev ai b go ge (gotohRowFoldAfterK prev ai b go ge (i + 1) k) k
          from gotohRowFoldAfterK_step ..]
        simp only [gotohRowFoldStep, h_shift, cons_getD_succ]
        exact ihk (by omega) col hcol_le

/-! ### Epsilon non-decreasing along diagonal

Key property: eps(k) = lcsDP(take k, take k) - diagCount(take k, take k)
is non-decreasing in k. This means eps(prefix) <= eps(full) <= go. -/

/-- diagCount prefix: count matches in first k positions. -/
def diagCountPrefix (a b : List ℕ) (k : ℕ) : ℕ :=
  (List.range k).countP (fun i => a.getD i 0 == b.getD i 0)

/-- diagCountPrefix at full length equals diagCount. -/
theorem diagCountPrefix_full (a b : List ℕ) (h_len : a.length = b.length) :
    diagCountPrefix a b a.length = diagCount a b := by
  unfold diagCountPrefix diagCount
  have : min a.length b.length = a.length := by omega
  rw [this]

/-- diagCount prefix step: diagCountPrefix(k+1) = diagCountPrefix(k) + match(k). -/
theorem diagCountPrefix_step (a b : List ℕ) (k : ℕ) :
    diagCountPrefix a b (k + 1) = diagCountPrefix a b k +
    if (a.getD k 0 == b.getD k 0) = true then 1 else 0 := by
  unfold diagCountPrefix
  rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
  omega

/-- LCS on diagonal prefix: lcsAfterK at the diagonal. -/
def lcsDiag (a b : List ℕ) (k : ℕ) : ℕ :=
  (lcsAfterK a b k).getD k 0

/-- Epsilon at diagonal prefix k. -/
def epsDiag (a b : List ℕ) (k : ℕ) : ℤ :=
  (lcsDiag a b k : ℤ) - (diagCountPrefix a b k : ℤ)

/-- LCS on diagonal is non-decreasing by exactly 1 at match. -/
theorem lcsDiag_match_step (a b : List ℕ) (k : ℕ)
    (hk : k < a.length) (hkb : k < b.length)
    (hmatch : a.getD k 0 == b.getD k 0) :
    lcsDiag a b (k + 1) = lcsDiag a b k + 1 := by
  unfold lcsDiag; rw [lcsAfterK_recurrence a b k k hk hkb, if_pos hmatch]

/-- LCS on diagonal is non-decreasing at mismatch. -/
theorem lcsDiag_mismatch_step (a b : List ℕ) (k : ℕ)
    (hk : k < a.length) (hkb : k < b.length)
    (hmismatch : ¬(a.getD k 0 == b.getD k 0)) :
    lcsDiag a b (k + 1) ≥ lcsDiag a b k := by
  unfold lcsDiag
  rw [lcsAfterK_recurrence a b k k hk hkb, if_neg hmismatch]
  exact le_trans (lcsAfterK_mono_col a b k k (by omega) hkb) (le_max_left _ _)

/-- **Epsilon is non-decreasing along the diagonal.**
    This is the key insight that unblocks Option B. -/
theorem eps_nondecreasing (a b : List ℕ) (k : ℕ)
    (hk : k < a.length) (hkb : k < b.length) :
    epsDiag a b (k + 1) ≥ epsDiag a b k := by
  unfold epsDiag
  rw [diagCountPrefix_step]
  by_cases hmatch : (a.getD k 0 == b.getD k 0) = true
  · -- match: lcsDiag +1, diagCount +1 → eps unchanged
    rw [lcsDiag_match_step a b k hk hkb hmatch, if_pos hmatch]; push_cast; omega
  · -- mismatch: lcsDiag non-decreasing, diagCount unchanged → eps non-decreasing
    have h := lcsDiag_mismatch_step a b k hk hkb hmatch
    rw [if_neg hmatch]; push_cast; omega

/-- **Epsilon at prefix <= epsilon at full length.** -/
theorem eps_prefix_le_full (a b : List ℕ) (k : ℕ)
    (h_len : a.length = b.length) (hk : k ≤ a.length) :
    epsDiag a b k ≤ epsDiag a b a.length := by
  -- Prove by strong induction: eps is non-decreasing, so eps(k) <= eps(m) for k <= m
  -- We induct on the gap (a.length - k)
  suffices h : ∀ gap : ℕ, ∀ j : ℕ, j + gap = a.length → j ≤ a.length →
      epsDiag a b j ≤ epsDiag a b a.length by
    exact h (a.length - k) k (by omega) hk
  intro gap
  induction gap with
  | zero =>
    intro j hj _
    have : j = a.length := by omega
    rw [this]
  | succ g ih =>
    intro j hj hj_le
    have hj_lt : j < a.length := by omega
    have hj_ltb : j < b.length := by omega
    have h_step : epsDiag a b j ≤ epsDiag a b (j + 1) :=
      eps_nondecreasing a b j hj_lt hj_ltb
    have h_rest : epsDiag a b (j + 1) ≤ epsDiag a b a.length :=
      ih (j + 1) (by omega) (by omega)
    linarith

/-! ### Diagonal induction: H[k][k] <= diagCount(prefix k)

Combining:
- Diagonal term: H[k][k] + match <= diagCount(k+1) by IH
- E/F terms: E[k+1][k+1] <= lcsDP(prefix k+1) - go
                           <= diagCount(prefix k+1) + eps(prefix k+1) - go
                           <= diagCount(prefix k+1) (since eps(prefix) <= go) -/

/-- **Diagonal H bound**: H[k][k] <= diagCount(prefix k) when eps(full) <= go. -/
theorem gotoh_diag_le_diagCount (a b : List ℕ) (go ge : ℤ)
    (h_go : go ≥ 1) (h_ge : ge ≥ 1)
    (h_neg : NEG_INF ≤ -go)
    (h_len : a.length = b.length)
    (h_eps : (lcsDP a b : ℤ) - (diagCount a b : ℤ) ≤ go) :
    ∀ k : ℕ, k ≤ a.length →
    (gotohAfterK a b go ge k).h.getD k NEG_INF ≤ (diagCountPrefix a b k : ℤ) := by
  -- By induction on k.
  -- Base: H[0][0] = 0 ≤ 0 = diagCountPrefix(0).
  -- Step: H[k+1][k+1] = max(diag, max(E, F)) where
  --   diag ≤ diagCountPrefix(k+1) by IH + diagCountPrefix_step
  --   E, F ≤ lcs(k+1,k+1) - go ≤ diagCountPrefix(k+1) since eps ≤ go
  intro k hk
  induction k with
  | zero => simp [gotohAfterK, gotohInitRow, diagCountPrefix]
  | succ n ih =>
    have h_n_le : n ≤ a.length := Nat.le_of_succ_le hk
    have h_n1_le_blen : n + 1 ≤ b.length := by omega
    have h_ih := ih h_n_le
    -- Epsilon bound: epsDiag(n+1) ≤ epsDiag(full) ≤ go
    have h_eps_full : epsDiag a b a.length ≤ go := by
      simp only [epsDiag, lcsDiag]; rw [diagCountPrefix_full a b h_len]
      have h1 := lcsDP_eq_lcsAfterK a b
      rw [show a.length = b.length from h_len] at *; linarith
    have h_eps_k : epsDiag a b (n + 1) ≤ go :=
      le_trans (eps_prefix_le_full a b (n + 1) h_len hk) h_eps_full
    -- Key bound: lcs(n+1,n+1) - go ≤ diagCountPrefix(n+1)
    have h_lcs_go : ((lcsAfterK a b (n + 1)).getD (n + 1) 0 : ℤ) - go ≤
        (diagCountPrefix a b (n + 1) : ℤ) := by
      have := show epsDiag a b (n + 1) =
          (lcsDiag a b (n + 1) : ℤ) - (diagCountPrefix a b (n + 1) : ℤ) from rfl
      simp only [lcsDiag] at this; omega
    -- Bounds on H, E, F at (n+1, n+1) from gotoh_HEF_le_lcs
    have hef_n1 := gotoh_HEF_le_lcs a b go ge h_go h_ge h_neg (n + 1) (n + 1) hk (by omega)
    -- Bounds on H, E, F at (n, n+1) for E_raw constituents
    have hef_prev := gotoh_HEF_le_lcs a b go ge h_go h_ge h_neg n (n + 1) h_n_le (by omega)
    -- Bounds at (n+1, n) for F_raw constituents
    have hef_col := gotoh_HEF_le_lcs a b go ge h_go h_ge h_neg (n + 1) n hk (by omega)
    -- Unfold to max(diag, max(E_raw, F_raw))
    simp only [gotohAfterK]
    rw [← gotohCellH_eq_processRow (gotohAfterK a b go ge n) (a.getD n 0) b go ge
        (n + 1) (n + 1) h_n1_le_blen]
    show gotohCellH (gotohAfterK a b go ge n) (a.getD n 0) b go ge (n + 1) (n + 1) ≤ _
    simp only [gotohCellH]
    -- Goal: max(diag, max(E_raw, F_raw)) ≤ diagCountPrefix(n+1)
    apply max_le
    · -- Diagonal: prev.h.getD n 0 + matchScore ≤ diagCountPrefix(n+1)
      -- IH gives prev.h.getD n NEG_INF ≤ diagCountPrefix(n)
      -- diagCountPrefix_step: diagCountPrefix(n+1) = diagCountPrefix(n) + match
      have h_hlen := gotohAfterK_h_length a b go ge n h_n_le
      have h_n_valid : n < (gotohAfterK a b go ge n).h.length := by rw [h_hlen]; omega
      rw [List.getD_default_irrel _ _ NEG_INF 0 h_n_valid] at h_ih
      rw [diagCountPrefix_step]; push_cast
      have : (if a.getD n 0 == b.getD n 0 then (1 : ℤ) else 0) =
             ↑(if (a.getD n 0 == b.getD n 0) = true then 1 else 0) := by
        split <;> simp_all
      linarith [this]
    · apply max_le
      · -- E_raw: max(prev.h[n+1] - go, prev.e[n+1] - ge) ≤ diagCountPrefix(n+1)
        -- prev.h[n+1] ≤ lcs(n, n+1) from hef_prev.1 (after default conversion)
        -- prev.e[n+1] ≤ lcs(n, n+1) - go from hef_prev.2.1
        unfold gotohH_at at hef_prev
        unfold gotohE_at at hef_prev
        have h_hlen := gotohAfterK_h_length a b go ge n h_n_le
        have h_n1_valid : n + 1 < (gotohAfterK a b go ge n).h.length := by
          rw [h_hlen]; omega
        have h_def : (gotohAfterK a b go ge n).h.getD (n + 1) 0 =
            (gotohAfterK a b go ge n).h.getD (n + 1) NEG_INF :=
          List.getD_default_irrel _ _ 0 NEG_INF h_n1_valid
        -- lcs(n, n+1) ≤ lcs(n+1, n+1) by mono_row
        have h_mono := Int.ofNat_le.mpr (lcsAfterK_mono_row a b n (n + 1) (by omega) (by omega))
        apply max_le <;> [rw [h_def]; skip] <;> linarith [hef_prev.1, hef_prev.2.1]
      · -- F_raw: max(gotohCellH ... n - go, gotohCellF ... n - ge) ≤ diagCountPrefix(n+1)
        -- gotohCellH ... n = H[n+1][n] by gotohCellH_eq_processRow
        -- gotohCellF ... n = F[n+1][n] by gotohCellF_eq_processRow
        -- Both bounded by gotoh_HEF_le_lcs at (n+1, n)
        have h_cellH := gotohCellH_eq_processRow (gotohAfterK a b go ge n) (a.getD n 0) b go ge
            (n + 1) n (by omega)
        have h_cellF := gotohCellF_eq_processRow (gotohAfterK a b go ge n) (a.getD n 0) b go ge
            (n + 1) n (by omega)
        -- (gotohProcessRow prev ai b go ge (n+1)) = gotohAfterK ... (n+1)
        have h_row : gotohProcessRow (gotohAfterK a b go ge n) (a.getD n 0) b go ge (n + 1) =
            gotohAfterK a b go ge (n + 1) := by simp [gotohAfterK]
        rw [h_row] at h_cellH h_cellF
        -- Now gotohCellH ... n = gotohH_at (n+1) n, gotohCellF ... n = gotohF_at (n+1) n
        unfold gotohH_at at hef_col
        unfold gotohF_at at hef_col
        rw [h_cellH, h_cellF]
        -- lcs(n+1, n) ≤ lcs(n+1, n+1) by mono_col
        have h_mono := Int.ofNat_le.mpr (lcsAfterK_mono_col a b (n + 1) n (by omega) (by omega))
        apply max_le <;> linarith [hef_col.1, hef_col.2.2]

/-- **Bridge Lemma 2 (gotoh_le_diag_when_eps_small)**: When epsilon <= go,
    Gotoh DP score <= diagonal match count.

    Proof strategy (Option B, unblocked by eps-non-decreasing):
    1. Mutual H/E/F upper bound via LCS (gotoh_HEF_le_lcs)
    2. eps(prefix k) <= eps(full) <= go (eps_prefix_le_full)
    3. Diagonal induction: H[k][k] <= diagCount(prefix k) (gotoh_diag_le_diagCount)
    4. At k = m: H[m][m] <= diagCount(a, b) -/
theorem gotoh_le_diag_when_eps_small (a b : List ℕ) (go ge : ℤ)
    (h_go : go ≥ 1) (h_ge : ge ≥ 1)
    (h_neg : NEG_INF ≤ -go)
    (h_len : a.length = b.length)
    (h_eps : (lcsDP a b : ℤ) - (diagCount a b : ℤ) ≤ go) :
    gotohGlobalScore a b go ge ≤ (diagCount a b : ℤ) := by
  -- Apply diagonal bound at k = a.length
  have h_diag := gotoh_diag_le_diagCount a b go ge h_go h_ge h_neg h_len h_eps a.length le_rfl
  -- Connect diagCountPrefix to diagCount
  rw [diagCountPrefix_full a b h_len] at h_diag
  -- Connect gotohAfterK to gotohGlobalScore
  show gotohGlobalScore a b go ge ≤ ↑(diagCount a b)
  unfold gotohGlobalScore
  conv_lhs => rw [show b.length = a.length from h_len.symm ▸ rfl]
  rw [← gotohAfterK_full]
  exact h_diag

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
    (h_neg : NEG_INF ≤ -go)
    (h_same_len : a.length = b.length) :
    correctionScoreDP a b go ge = gotohGlobalScore a b go ge := by
  unfold correctionScoreDP
  simp only
  split
  · -- Case: epsilon <= go. Need: (diagCount a b : Z) = gotohGlobalScore a b go ge.
    -- By the two bridge lemmas: gotoh_ge_diag gives >=, gotoh_le_diag_when_eps_small gives <=.
    rename_i h_eps
    have h_ge_dir := gotoh_ge_diag a b go ge h_go_pos h_ge_pos h_same_len
    have h_le_dir := gotoh_le_diag_when_eps_small a b go ge h_go_pos h_ge_pos h_neg h_same_len h_eps
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
