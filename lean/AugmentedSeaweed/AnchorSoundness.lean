/-
  AugmentedSeaweed/AnchorSoundness.lean

  Spec 04: Anchor Soundness — LCS path stays on diagonal through long MEMs.

  Main results:
  - lcsAfterK_unit_col': dp[k][j+1] ≤ dp[k][j] + 1 (column unit step)
  - lcsAfterK_diag_unit: dp[k+1][j+1] ≤ dp[k][j] + 1 (diagonal unit step)
  - lcsDiag_mem_exact: lcsDiag(s+M) = lcsDiag(s) + M during a MEM
  - anchor_soundness_boundary: Spec 04 boundary case (sorry: exchange argument)

  Sorry status: 1 sorry (anchor_soundness_boundary)
-/
import Mathlib.Tactic
import AugmentedSeaweed.ScoreDetermination
import AugmentedSeaweed.AdditivityBound
import AugmentedSeaweed.AnchorDecomposition

/-! ## Concrete Tests -/

example : lcsDP [0,1,0] [0,1,0] = 3 := by native_decide
example : lcsDP [0,1,1,1,0] [1,1,1,1,1] = 3 := by native_decide
example : epsilon [0,1,1,1,0] [1,1,1,1,1] =
    epsilon [0] [1] + epsilon [0] [1] := by native_decide

/-! ## Part 1: Column Unit Step

dp[k][j+1] ≤ dp[k][j] + 1: adding one column increases LCS by at most 1.
Proof by induction on k:
- k=0: both sides are 0.
- k+1: match case uses mono_row; mismatch uses IH + mono_row. -/

private theorem lcsAfterK_zero_row (a b : List ℕ) (j : ℕ) :
    (lcsAfterK a b 0).getD j 0 = 0 := by
  simp only [lcsAfterK, List.getD, List.getElem?_replicate]
  split <;> rfl

theorem lcsAfterK_unit_col' (a b : List ℕ) :
    ∀ k, k ≤ a.length → ∀ j, j < b.length →
    (lcsAfterK a b k).getD (j + 1) 0 ≤ (lcsAfterK a b k).getD j 0 + 1 := by
  intro k
  induction k with
  | zero =>
    intro _ j _
    rw [lcsAfterK_zero_row, lcsAfterK_zero_row]; omega
  | succ k ihk =>
    intro hk j hj
    have hk' : k < a.length := by omega
    rw [lcsAfterK_recurrence a b k j hk' hj]
    split
    · -- Match (a[k] = b[j]): dp[k+1][j+1] = dp[k][j]+1
      -- Need: dp[k][j]+1 ≤ dp[k+1][j]+1, i.e., dp[k][j] ≤ dp[k+1][j]
      have := lcsAfterK_mono_row a b k j hk' (by omega)
      omega
    · -- Mismatch: dp[k+1][j+1] = max(dp[k][j+1], dp[k+1][j])
      -- Need: max ≤ dp[k+1][j]+1
      apply Nat.max_le.mpr; constructor
      · -- dp[k][j+1] ≤ dp[k+1][j]+1
        -- dp[k][j+1] ≤ dp[k][j]+1 (IH) and dp[k][j] ≤ dp[k+1][j] (mono_row)
        have h_uc := ihk (by omega) j hj
        have h_mr := lcsAfterK_mono_row a b k j hk' (by omega)
        omega
      · omega -- dp[k+1][j] ≤ dp[k+1][j]+1

/-! ## Part 2: Diagonal Unit Step -/

/-- dp[k+1][j+1] ≤ dp[k][j] + 1: diagonal step is at most +1. -/
theorem lcsAfterK_diag_unit (a b : List ℕ) (k j : ℕ)
    (hk : k < a.length) (hj : j < b.length) :
    (lcsAfterK a b (k + 1)).getD (j + 1) 0 ≤ (lcsAfterK a b k).getD j 0 + 1 := by
  rw [lcsAfterK_recurrence a b k j hk hj]
  split
  · omega  -- Match: dp[k][j]+1 ≤ dp[k][j]+1
  · -- Mismatch: max(dp[k][j+1], dp[k+1][j]) ≤ dp[k][j]+1
    apply Nat.max_le.mpr
    exact ⟨lcsAfterK_unit_col' a b k (by omega) j hj,
           lcsAfterK_unit_row a b k j hk (by omega)⟩

/-- Multi-step diagonal bound: dp[k+n][j+n] ≤ dp[k][j] + n. -/
theorem lcsAfterK_diag_unit_multi (a b : List ℕ) (k j n : ℕ)
    (hk : k + n ≤ a.length) (hj : j + n ≤ b.length) :
    (lcsAfterK a b (k + n)).getD (j + n) 0 ≤ (lcsAfterK a b k).getD j 0 + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (lcsAfterK a b (k + (n + 1))).getD (j + (n + 1)) 0
        = (lcsAfterK a b ((k + n) + 1)).getD ((j + n) + 1) 0 := by ring_nf
      _ ≤ (lcsAfterK a b (k + n)).getD (j + n) 0 + 1 :=
          lcsAfterK_diag_unit a b (k + n) (j + n) (by omega) (by omega)
      _ ≤ (lcsAfterK a b k).getD j 0 + n + 1 := by linarith [ih (by omega) (by omega)]
      _ = (lcsAfterK a b k).getD j 0 + (n + 1) := by ring

/-! ## Part 3: MEM Region Exactness -/

/-- Over a MEM region [s, s+M): lcsDiag(s+M) = lcsDiag(s) + M. -/
theorem lcsDiag_mem_exact (a b : List ℕ) (s M : ℕ)
    (h_bound : s + M ≤ min a.length b.length)
    (h_mem : ∀ i, s ≤ i → i < s + M → a.getD i 0 = b.getD i 0) :
    lcsDiag a b (s + M) = lcsDiag a b s + M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show s + (M + 1) = (s + M) + 1 from by omega]
    rw [lcsDiag_match_step a b (s + M) (by omega) (by omega)
        (beq_iff_eq.mpr (h_mem (s + M) (by omega) (by omega)))]
    rw [ih (by omega) (fun i hi1 hi2 => h_mem i hi1 (by omega))]
    omega

/-! ## Part 4: Exchange Argument Infrastructure

The exchange argument shows lcsDP(a, b) ≤ M + lcsDP(a[M:], b[M:]):
no LCS matching can extract more than M matches from the first M rows/columns
plus whatever the suffix contributes. Combined with lcsDP_split (≥ direction)
and diagCount decomposition, this gives epsilon(a,b) = epsilon(a[M:], b[M:])
when positions [0, M) form a MEM longer than the dark region. -/

/-- Multi-step unit row bound: dp[k+n][j] ≤ dp[k][j] + n. -/
private theorem lcsAfterK_unit_row_multi (a b : List ℕ) (k n j : ℕ)
    (hk : k + n ≤ a.length) (hj : j ≤ b.length) :
    (lcsAfterK a b (k + n)).getD j 0 ≤ (lcsAfterK a b k).getD j 0 + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (lcsAfterK a b (k + (n + 1))).getD j 0
        = (lcsAfterK a b ((k + n) + 1)).getD j 0 := by ring_nf
      _ ≤ (lcsAfterK a b (k + n)).getD j 0 + 1 :=
          lcsAfterK_unit_row a b (k + n) j (by omega) hj
      _ ≤ (lcsAfterK a b k).getD j 0 + n + 1 := by linarith [ih (by omega)]
      _ = (lcsAfterK a b k).getD j 0 + (n + 1) := by ring

/-- Multi-step unit column bound: dp[k][j+n] ≤ dp[k][j] + n. -/
private theorem lcsAfterK_unit_col_multi (a b : List ℕ) (k j n : ℕ)
    (hk : k ≤ a.length) (hj : j + n ≤ b.length) :
    (lcsAfterK a b k).getD (j + n) 0 ≤ (lcsAfterK a b k).getD j 0 + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (lcsAfterK a b k).getD (j + (n + 1)) 0
        = (lcsAfterK a b k).getD ((j + n) + 1) 0 := by ring_nf
      _ ≤ (lcsAfterK a b k).getD (j + n) 0 + 1 :=
          lcsAfterK_unit_col' a b k hk (j + n) (by omega)
      _ ≤ (lcsAfterK a b k).getD j 0 + n + 1 := by linarith [ih (by omega)]
      _ = (lcsAfterK a b k).getD j 0 + (n + 1) := by ring

/-- Row bound: dp[k][j] ≤ k (LCS of first k chars of a with any prefix of b). -/
private theorem lcsAfterK_le_row (a b : List ℕ) (k j : ℕ)
    (hk : k ≤ a.length) (hj : j ≤ b.length) :
    (lcsAfterK a b k).getD j 0 ≤ k := by
  have h := lcsAfterK_unit_row_multi a b 0 k j (by omega) hj
  rw [Nat.zero_add, lcsAfterK_zero_row, Nat.zero_add] at h
  exact h

/-- Column bound: dp[k][j] ≤ j (LCS of any prefix of a with first j chars of b). -/
private theorem lcsAfterK_le_col (a b : List ℕ) (k j : ℕ)
    (hk : k ≤ a.length) (hj : j ≤ b.length) :
    (lcsAfterK a b k).getD j 0 ≤ j := by
  have h := lcsAfterK_unit_col_multi a b k 0 j hk (by omega)
  rw [Nat.zero_add, lcsAfterK_zero_col, Nat.zero_add] at h
  exact h

/-- Core shifted DP comparison: the full DP at offset (M+d, M+j) is bounded
    by M plus the suffix DP at (d, j). This is because the "head start" from
    the MEM region is at most M, and the remaining computation mirrors the suffix. -/
private theorem lcsAfterK_shifted_le (a b : List ℕ) (M : ℕ)
    (hM : M ≤ a.length) (hMb : M ≤ b.length) :
    ∀ d, M + d ≤ a.length → ∀ j, M + j ≤ b.length →
    (lcsAfterK a b (M + d)).getD (M + j) 0 ≤
    M + (lcsAfterK (a.drop M) (b.drop M) d).getD j 0 := by
  intro d
  induction d with
  | zero =>
    intro _ j _
    simp only [Nat.add_zero]
    have h1 := lcsAfterK_le_row a b M (M + j) hM (by omega)
    have h2 := lcsAfterK_zero_row (a.drop M) (b.drop M) j
    omega
  | succ d ihd =>
    intro hd j
    induction j with
    | zero =>
      intro _
      simp only [Nat.add_zero]
      have h1 := lcsAfterK_le_col a b (M + (d + 1)) M (by omega) hMb
      have h2 := lcsAfterK_zero_col (a.drop M) (b.drop M) (d + 1)
      omega
    | succ j ihj =>
      intro hj
      -- Characters align between full and suffix DPs
      have h_char : (a.getD (M + d) 0 == b.getD (M + j) 0) =
          ((a.drop M).getD d 0 == (b.drop M).getD j 0) := by
        congr 1 <;> simp [List.getD, List.getElem?_drop]
      -- Rewrite to expose recurrence form
      rw [show M + (d + 1) = (M + d) + 1 from by omega,
          show M + (j + 1) = (M + j) + 1 from by omega]
      -- Apply full DP recurrence on LHS
      rw [lcsAfterK_recurrence a b (M + d) (M + j) (by omega) (by omega)]
      -- Apply suffix DP recurrence on RHS
      have h_suff := lcsAfterK_recurrence (a.drop M) (b.drop M) d j
        (by simp; omega) (by simp; omega)
      rw [h_suff, h_char]
      -- Now both sides split on the same condition
      split
      · -- Match: dp_full[M+d][M+j]+1 ≤ M + (dp_suffix[d][j]+1)
        have := ihd (by omega) j (by omega)
        omega
      · -- Mismatch: max(dp_full[M+d][(M+j)+1], dp_full[(M+d)+1][M+j])
        --         ≤ M + max(dp_suffix[d][j+1], dp_suffix[d+1][j])
        have h_up := ihd (by omega) (j + 1) (by omega)
        rw [show M + (j + 1) = (M + j) + 1 from by omega] at h_up
        have h_left := ihj (by omega)
        rw [show M + (d + 1) = (M + d) + 1 from by omega] at h_left
        apply Nat.max_le.mpr
        constructor
        · have := le_max_left
            ((lcsAfterK (a.drop M) (b.drop M) d).getD (j + 1) 0)
            ((lcsAfterK (a.drop M) (b.drop M) (d + 1)).getD j 0)
          linarith
        · have := le_max_right
            ((lcsAfterK (a.drop M) (b.drop M) d).getD (j + 1) 0)
            ((lcsAfterK (a.drop M) (b.drop M) (d + 1)).getD j 0)
          linarith

/-- Exchange bound: lcsDP(a, b) ≤ M + lcsDP(a[M:], b[M:]). Any common
    subsequence uses at most M matches from the first M row/column indices. -/
theorem lcsDP_le_prefix_plus_suffix (a b : List ℕ) (M : ℕ)
    (hlen : a.length = b.length) (hM : M ≤ a.length) :
    lcsDP a b ≤ M + lcsDP (a.drop M) (b.drop M) := by
  rw [lcsDP_eq_lcsAfterK, lcsDP_eq_lcsAfterK]
  simp only [List.length_drop]
  have hMb : M ≤ b.length := by omega
  have key := lcsAfterK_shifted_le a b M hM hMb
    (a.length - M) (by omega) (b.length - M) (by omega)
  rwa [show M + (a.length - M) = a.length from by omega,
       show M + (b.length - M) = b.length from by omega] at key

/-- diagCount of a MEM prefix equals M: all M positions match on diagonal. -/
private theorem diagCount_mem_prefix (a b : List ℕ) (M : ℕ)
    (hMa : M ≤ a.length) (hMb : M ≤ b.length)
    (h_mem : ∀ i, i < M → a.getD i 0 = b.getD i 0) :
    (diagCount (a.take M) (b.take M) : ℤ) = (M : ℤ) := by
  suffices h : diagCount (a.take M) (b.take M) = M by exact_mod_cast h
  unfold diagCount
  have hmin : min (a.take M).length (b.take M).length = M := by
    simp [List.length_take]; omega
  rw [hmin]
  -- Goal: (List.range M).countP (fun i => ...) = M
  conv_rhs => rw [← List.length_range (n := M)]
  apply List.countP_eq_length.mpr
  intro i hi
  have hi' : i < M := List.mem_range.mp hi
  have ha : (a.take M).getD i 0 = a.getD i 0 := by
    simp only [List.getD, List.getElem?_take, if_pos hi']
  have hb : (b.take M).getD i 0 = b.getD i 0 := by
    simp only [List.getD, List.getElem?_take, if_pos hi']
  rw [ha, hb, beq_iff_eq]
  exact h_mem i hi'

/-! ## Part 5: Spec 04 — Anchor Soundness -/

/-- Spec 04 boundary case: MEM at [0, M), dark at [M, n).
    When the MEM is longer than the dark region, epsilon = dark epsilon.
    Proved by the exchange argument: lcsDP(a,b) ≤ M + lcsDP(a[M:],b[M:]). -/
theorem anchor_soundness_boundary (a b : List ℕ) (M : ℕ)
    (hlen : a.length = b.length) (hM : M ≤ a.length)
    (h_mem : ∀ i, i < M → a.getD i 0 = b.getD i 0)
    (h_long : M > a.length - M) :
    epsilon a b = epsilon (a.drop M) (b.drop M) := by
  -- ≥ direction: from epsilon_drop_le (AdditivityBound.lean)
  have h_ge := epsilon_drop_le a b M hlen hM
  -- ≤ direction: exchange bound + diagCount decomposition
  have h_le : epsilon a b ≤ epsilon (a.drop M) (b.drop M) := by
    simp only [epsilon]
    have h_dc := diagCount_take_drop a b M hlen hM
    have h_mc := diagCount_mem_prefix a b M hM (by omega) h_mem
    have h_ub : (lcsDP a b : ℤ) ≤ ↑M + ↑(lcsDP (a.drop M) (b.drop M)) := by
      exact_mod_cast lcsDP_le_prefix_plus_suffix a b M hlen hM
    linarith
  linarith

/-! ## Part 6: Spec 05 — Tier Classifier Correctness

Crown theorem: when the character-frequency bound certifies epsilon ≤ go,
the correction formula gives score = diag exactly. No alignment DP needed.

Two versions:
- Global: charfreq on whole sequence ≤ go → score = diag
- Boundary: MEM at [0,M) with charfreq on dark suffix ≤ go → score = diag -/

/-- Spec 05 (global): if offDiagMatchable(a, b) ≤ go, then score = diag.
    Chain: epsilon ≤ offDiagMatchable (Spec 03) ≤ go (hypothesis) → correctionScore = diag. -/
theorem global_charfreq_tier1 (a b : List ℕ) (go ge : ℤ)
    (h_charfreq : (offDiagMatchable a b : ℤ) ≤ go) :
    correctionScoreDP a b go ge = (diagCount a b : ℤ) := by
  unfold correctionScoreDP
  simp only
  have h_eps : (lcsDP a b : ℤ) - (diagCount a b : ℤ) ≤ go := by
    have := epsilon_le_offDiagMatchable a b
    unfold epsilon at this
    linarith
  rw [if_pos h_eps]

-- Verified computationally
example : correctionScoreDP [0,1,2,3] [0,1,2,3] 2 1 =
    (diagCount [0,1,2,3] [0,1,2,3] : ℤ) := by native_decide
example : correctionScoreDP [0,1,0,0] [0,1,1,0] 2 1 =
    (diagCount [0,1,0,0] [0,1,1,0] : ℤ) := by native_decide

/-- Spec 05 (boundary MEM): MEM at [0, M) with charfreq on dark suffix ≤ go → score = diag.
    Chain: epsilon = dark epsilon (Spec 04) ≤ offDiagMatchable (Spec 03) ≤ go → score = diag. -/
theorem charfreq_tier_boundary (a b : List ℕ) (go ge : ℤ) (M : ℕ)
    (hlen : a.length = b.length) (hM : M ≤ a.length)
    (h_mem : ∀ i, i < M → a.getD i 0 = b.getD i 0)
    (h_long : M > a.length - M)
    (h_charfreq : (offDiagMatchable (a.drop M) (b.drop M) : ℤ) ≤ go) :
    correctionScoreDP a b go ge = (diagCount a b : ℤ) := by
  unfold correctionScoreDP
  simp only
  have h_eps : (lcsDP a b : ℤ) - (diagCount a b : ℤ) ≤ go := by
    have h_anchor := anchor_soundness_boundary a b M hlen hM h_mem h_long
    have h_spec3 := epsilon_le_offDiagMatchable (a.drop M) (b.drop M)
    unfold epsilon at h_anchor h_spec3
    linarith
  rw [if_pos h_eps]

-- MEM [0,3), dark [3,5): charfreq on dark = offDiagMatchable [1,0] [0,1]
example : correctionScoreDP [0,1,0,1,0] [0,1,0,0,1] 2 1 =
    (diagCount [0,1,0,1,0] [0,1,0,0,1] : ℤ) := by native_decide
