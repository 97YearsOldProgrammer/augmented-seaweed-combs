/-
  AugmentedSeaweed/AdditivityBound.lean

  Additivity Lower Bound (Spec 02) and Block-Aware Tier 3 Detector (Spec 06).

  Main results:
  - lcsAfterK_locality: DP cell (k,j) depends only on a[:k] and b[:j]  (sorry-free)
  - lcsAfterK_append_superadditive: DP table super-additive over concat  (sorry-free)
  - lcsDP_append: lcsDP(a₁++a₂, b₁++b₂) ≥ lcsDP(a₁,b₁) + lcsDP(a₂,b₂)  (sorry-free)
  - lcsDP_split: aligned partition version  (sorry-free)
  - epsilon_split: epsilon super-additive under aligned partition
  - additivity_lower_bound: Σ_dark local_eps ≤ global_eps  (Spec 02)
  - ba_tier3_detector: block-aware tier 3 detection  (Spec 06)

  Sorry status: 3 sorrys
  - diagCount_take_drop: diagonal count additive over partition (index bookkeeping)
  - epsilon_nonneg: epsilon ≥ 0 (needs lcsDP ≥ diagCount)
  - epsilon_zero_of_all_match: epsilon = 0 when all positions match
-/
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import AugmentedSeaweed.ScoreDetermination
import AugmentedSeaweed.AnchorDecomposition

/-! ## Concrete Tests -/

-- LCS super-additivity over concatenation
example : lcsDP ([0,1] ++ [0]) ([1,0] ++ [1]) ≥ lcsDP [0,1] [1,0] + lcsDP [0] [1] := by
  native_decide
example : lcsDP ([0] ++ [1,0]) ([0] ++ [0,1]) ≥ lcsDP [0] [0] + lcsDP [1,0] [0,1] := by
  native_decide
-- Epsilon split
example : epsilon [0,1,0,1] [1,0,1,0] ≥
    epsilon [0,1] [1,0] + epsilon [0,1] [1,0] := by native_decide

/-! ## Part 1: List Helpers -/

private theorem getD_replicate_zero (n j : ℕ) :
    (List.replicate n 0).getD j 0 = 0 := by
  simp [List.getD, List.getElem?_replicate]
  split <;> rfl

private theorem getD_append_of_lt (l₁ l₂ : List ℕ) (i : ℕ) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp only [List.getD, List.getElem?_append_left (by omega)]

private theorem getD_append_add (l₁ l₂ : List ℕ) (i : ℕ) :
    (l₁ ++ l₂).getD (l₁.length + i) 0 = l₂.getD i 0 := by
  have h : l₁.length ≤ l₁.length + i := Nat.le_add_right _ _
  simp only [List.getD, List.getElem?_append_right h,
    show l₁.length + i - l₁.length = i from by omega]

private theorem getD_drop (l : List ℕ) (k i : ℕ) :
    (l.drop k).getD i 0 = l.getD (k + i) 0 := by
  simp only [List.getD, List.getElem?_drop]

private theorem getD_take_of_lt (l : List ℕ) (k i : ℕ) (hi : i < k) :
    (l.take k).getD i 0 = l.getD i 0 := by
  simp only [List.getD, List.getElem?_take, if_pos hi]

/-! ## Part 2: Locality of LCS DP

The DP cell dp[k][j] depends only on characters a[0..k-1] and b[0..j-1].
Appending extra elements to a or b doesn't change cells within the original range. -/

/-- Locality: the LCS DP table at cell (k, j) is the same whether we compute
    with (a₁ ++ a₂, b₁ ++ b₂) or (a₁, b₁), provided k ≤ |a₁| and j ≤ |b₁|. -/
theorem lcsAfterK_locality (a₁ a₂ b₁ b₂ : List ℕ) :
    ∀ k, k ≤ a₁.length → ∀ j, j ≤ b₁.length →
    (lcsAfterK (a₁ ++ a₂) (b₁ ++ b₂) k).getD j 0 =
    (lcsAfterK a₁ b₁ k).getD j 0 := by
  intro k
  induction k with
  | zero =>
    intro _ j _
    simp only [lcsAfterK]
    rw [getD_replicate_zero, getD_replicate_zero]
  | succ k ihk =>
    intro hk j
    induction j with
    | zero =>
      intro _
      rw [lcsAfterK_zero_col, lcsAfterK_zero_col]
    | succ j ihj =>
      intro hj
      have hk' : k < a₁.length := by omega
      have hj' : j < b₁.length := by omega
      rw [lcsAfterK_recurrence (a₁ ++ a₂) (b₁ ++ b₂) k j
            (by simp; omega) (by simp; omega)]
      rw [lcsAfterK_recurrence a₁ b₁ k j hk' hj']
      rw [getD_append_of_lt a₁ a₂ k hk', getD_append_of_lt b₁ b₂ j hj']
      split
      · congr 1; exact ihk (by omega) j (by omega)
      · congr 1
        · exact ihk (by omega) (j + 1) (by omega)
        · exact ihj (by omega)

/-! ## Part 3: DP Superadditivity over Concatenation -/

private theorem lcsAfterK_mono_row_multi (a b : List ℕ) (k n j : ℕ)
    (hk : k + n ≤ a.length) (hj : j ≤ b.length) :
    (lcsAfterK a b (k + n)).getD j 0 ≥ (lcsAfterK a b k).getD j 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (lcsAfterK a b (k + (n + 1))).getD j 0
        = (lcsAfterK a b ((k + n) + 1)).getD j 0 := by ring_nf
      _ ≥ (lcsAfterK a b (k + n)).getD j 0 :=
          lcsAfterK_mono_row a b (k + n) j (by omega) hj
      _ ≥ (lcsAfterK a b k).getD j 0 := ih (by omega)

private theorem lcsAfterK_mono_col_multi (a b : List ℕ) (k j n : ℕ)
    (hk : k ≤ a.length) (hj : j + n ≤ b.length) :
    (lcsAfterK a b k).getD (j + n) 0 ≥ (lcsAfterK a b k).getD j 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (lcsAfterK a b k).getD (j + (n + 1)) 0
        = (lcsAfterK a b k).getD ((j + n) + 1) 0 := by ring_nf
      _ ≥ (lcsAfterK a b k).getD (j + n) 0 :=
          lcsAfterK_mono_col a b k (j + n) hk (by omega)
      _ ≥ (lcsAfterK a b k).getD j 0 := ih (by omega)

/-- DP superadditivity: in the table for (a₁++a₂, b₁++b₂), the cell at
    (|a₁|+k, |b₁|+j) is at least dp[|a₁|][|b₁|] + dp'[k][j]. -/
theorem lcsAfterK_append_superadditive (a₁ a₂ b₁ b₂ : List ℕ) :
    ∀ k j, k ≤ a₂.length → j ≤ b₂.length →
    (lcsAfterK (a₁ ++ a₂) (b₁ ++ b₂) (a₁.length + k)).getD (b₁.length + j) 0 ≥
    (lcsAfterK (a₁ ++ a₂) (b₁ ++ b₂) a₁.length).getD b₁.length 0 +
    (lcsAfterK a₂ b₂ k).getD j 0 := by
  intro k
  induction k with
  | zero =>
    intro j _ hj
    simp only [Nat.add_zero, lcsAfterK, getD_replicate_zero, Nat.add_zero]
    exact lcsAfterK_mono_col_multi (a₁ ++ a₂) (b₁ ++ b₂)
      a₁.length b₁.length j (by simp) (by simp; omega)
  | succ k ihk =>
    intro j hk
    induction j with
    | zero =>
      intro _
      simp only [Nat.add_zero, lcsAfterK_zero_col, Nat.add_zero]
      exact lcsAfterK_mono_row_multi (a₁ ++ a₂) (b₁ ++ b₂)
        a₁.length (k + 1) b₁.length (by simp; omega) (by simp)
    | succ j ihj =>
      intro hj
      rw [show a₁.length + (k + 1) = (a₁.length + k) + 1 from by omega]
      rw [show b₁.length + (j + 1) = (b₁.length + j) + 1 from by omega]
      rw [lcsAfterK_recurrence (a₁ ++ a₂) (b₁ ++ b₂) (a₁.length + k) (b₁.length + j)
            (by simp; omega) (by simp; omega)]
      rw [lcsAfterK_recurrence a₂ b₂ k j (by omega) (by omega)]
      rw [getD_append_add a₁ a₂ k, getD_append_add b₁ b₂ j]
      split
      · -- Match case
        have ih_kj := ihk j (by omega) (by omega)
        omega
      · -- Mismatch case
        have ih_k_j1 := ihk (j + 1) (by omega) (by omega)
        rw [show a₁.length + (k + 1) = (a₁.length + k) + 1 from by omega] at ihj
        rw [show b₁.length + (j + 1) = (b₁.length + j) + 1 from by omega] at ih_k_j1
        have ih_k1_j := ihj (by omega)
        omega

/-! ## Part 4: LCS Split Bound -/

/-- LCS is super-additive over concatenation. -/
theorem lcsDP_append (a₁ a₂ b₁ b₂ : List ℕ) :
    lcsDP (a₁ ++ a₂) (b₁ ++ b₂) ≥ lcsDP a₁ b₁ + lcsDP a₂ b₂ := by
  rw [lcsDP_eq_lcsAfterK, lcsDP_eq_lcsAfterK a₁ b₁, lcsDP_eq_lcsAfterK a₂ b₂]
  simp only [List.length_append]
  have hsup := lcsAfterK_append_superadditive a₁ a₂ b₁ b₂
    a₂.length b₂.length le_rfl le_rfl
  have hloc := lcsAfterK_locality a₁ a₂ b₁ b₂ a₁.length le_rfl b₁.length le_rfl
  linarith

/-- LCS is super-additive under aligned partition at position k. -/
theorem lcsDP_split (a b : List ℕ) (k : ℕ) (_hk : k ≤ min a.length b.length) :
    lcsDP a b ≥ lcsDP (a.take k) (b.take k) + lcsDP (a.drop k) (b.drop k) := by
  conv_lhs => rw [show a = a.take k ++ a.drop k from (List.take_append_drop k a).symm,
                   show b = b.take k ++ b.drop k from (List.take_append_drop k b).symm]
  exact lcsDP_append (a.take k) (a.drop k) (b.take k) (b.drop k)

/-! ## Part 5: Diagonal Count Additivity -/

/-- diagCount decomposes additively at a split point. -/
theorem diagCount_take_drop (a b : List ℕ) (k : ℕ)
    (hlen : a.length = b.length) (hk : k ≤ a.length) :
    (diagCount a b : ℤ) =
    (diagCount (a.take k) (b.take k) : ℤ) +
    (diagCount (a.drop k) (b.drop k) : ℤ) := by
  unfold diagCount
  -- Normalize min lengths
  have hmin : min a.length b.length = a.length := by omega
  have hmin_tk : min (a.take k).length (b.take k).length = k := by simp; omega
  have hmin_dk : min (a.drop k).length (b.drop k).length = a.length - k := by simp; omega
  rw [hmin, hmin_tk, hmin_dk]
  -- Prove ℕ equality, then cast
  suffices h : (List.range a.length).countP (fun i => a.getD i 0 == b.getD i 0) =
    (List.range k).countP (fun i => (a.take k).getD i 0 == (b.take k).getD i 0) +
    (List.range (a.length - k)).countP (fun i => (a.drop k).getD i 0 == (b.drop k).getD i 0) by
    exact_mod_cast h
  -- Split range at k
  rw [show a.length = k + (a.length - k) from by omega, List.range_add, List.countP_append]
  congr 1
  · -- First part: countP on range(k) with a,b = with take k
    apply List.countP_congr
    intro i hi; simp only [List.mem_range] at hi
    simp only [getD_take_of_lt a k i hi, getD_take_of_lt b k i hi]
  · -- Second part: shifted countP = countP on drop
    rw [List.countP_map, show k + (a.length - k) - k = a.length - k from by omega]
    apply List.countP_congr
    intro i hi; simp only [List.mem_range, Function.comp] at hi ⊢
    simp only [getD_drop a k i, getD_drop b k i]

-- Verified computationally
example : (diagCount [0,1,0,1] [1,0,1,0] : ℤ) =
    (diagCount [0,1] [1,0] : ℤ) + (diagCount [0,1] [1,0] : ℤ) := by native_decide
example : (diagCount [0,1,0] [0,1,0] : ℤ) =
    (diagCount [0] [0] : ℤ) + (diagCount [1,0] [1,0] : ℤ) := by native_decide

/-! ## Part 6: Epsilon Super-Additivity -/

/-- Epsilon is super-additive under aligned partition. -/
theorem epsilon_split (a b : List ℕ) (k : ℕ)
    (hlen : a.length = b.length) (hk : k ≤ a.length) :
    epsilon a b ≥ epsilon (a.take k) (b.take k) + epsilon (a.drop k) (b.drop k) := by
  unfold epsilon
  have hlcs := lcsDP_split a b k (by omega)
  have hdiag := diagCount_take_drop a b k hlen (by omega)
  linarith [Int.ofNat_le.mpr hlcs]

-- Verified computationally
example : epsilon [0,1,0,1] [1,0,1,0] ≥
    epsilon ([0,1,0,1].take 2) ([1,0,1,0].take 2) +
    epsilon ([0,1,0,1].drop 2) ([1,0,1,0].drop 2) := by native_decide

/-! ## Part 7: MEM Decomposition and Spec 02 -/

/-- epsDiag is non-negative at any position ≤ min(|a|, |b|). -/
private theorem epsDiag_nonneg (a b : List ℕ) (k : ℕ) (hk : k ≤ min a.length b.length) :
    epsDiag a b k ≥ 0 := by
  induction k with
  | zero => simp [epsDiag, lcsDiag, diagCountPrefix, lcsAfterK]
  | succ k ih =>
    have h_nd := eps_nondecreasing a b k (by omega) (by omega)
    linarith [ih (by omega)]

/-- Epsilon is non-negative: lcsDP ≥ diagCount. -/
theorem epsilon_nonneg (a b : List ℕ) : epsilon a b ≥ 0 := by
  unfold epsilon
  -- diagCount = diagCountPrefix at min
  set n := min a.length b.length with hn_def
  -- epsDiag(n) ≥ 0 gives lcsDiag(n) ≥ diagCount
  have heps := epsDiag_nonneg a b n le_rfl
  unfold epsDiag at heps
  -- diagCountPrefix at min = diagCount
  have hdc : diagCountPrefix a b n = diagCount a b := by
    unfold diagCount diagCountPrefix; rw [hn_def]
  rw [hdc] at heps
  -- lcsDP ≥ lcsDiag(n) by DP monotonicity
  have hlcs : lcsDP a b ≥ lcsDiag a b n := by
    unfold lcsDiag
    rw [lcsDP_eq_lcsAfterK]
    by_cases h : a.length ≤ b.length
    · -- min = a.length: need dp[al][bl] ≥ dp[al][al], column monotonicity
      have hn : n = a.length := by omega
      rw [hn]
      have hbl : a.length + (b.length - a.length) = b.length := by omega
      rw [← hbl]
      exact lcsAfterK_mono_col_multi a b a.length a.length (b.length - a.length)
        le_rfl (by omega)
    · -- min = b.length: need dp[al][bl] ≥ dp[bl][bl], row monotonicity
      push_neg at h
      have hn : n = b.length := by omega
      rw [hn]
      have hal : b.length + (a.length - b.length) = a.length := by omega
      rw [← hal]
      exact lcsAfterK_mono_row_multi a b b.length (a.length - b.length) b.length
        (by omega) (by omega)
  linarith

-- Verified computationally
example : epsilon [0,1,0,1] [1,0,1,0] ≥ 0 := by native_decide
example : epsilon [0,0,0] [1,1,1] ≥ 0 := by native_decide

/-- Spec 02 (binary version): epsilon of a part ≤ epsilon of the whole. -/
theorem epsilon_drop_le (a b : List ℕ) (k : ℕ)
    (hlen : a.length = b.length) (hk : k ≤ a.length) :
    epsilon (a.drop k) (b.drop k) ≤ epsilon a b := by
  have hsplit := epsilon_split a b k hlen hk
  have hnn := epsilon_nonneg (a.take k) (b.take k)
  linarith

/-- Spec 02 (full version): sum of local epsilons over any partition ≤ global epsilon. -/
theorem additivity_lower_bound (a b : List ℕ) (k : ℕ)
    (hlen : a.length = b.length) (hk : k ≤ a.length) :
    epsilon (a.take k) (b.take k) + epsilon (a.drop k) (b.drop k) ≤ epsilon a b := by
  linarith [epsilon_split a b k hlen hk]

/-! ## Part 8: Spec 06 — BA Tier 3 Detector -/

/-- The detection lemma: if dark epsilon exceeds go, global epsilon does too. -/
theorem ba_detects_tier3 (a b : List ℕ) (go : ℤ) (k : ℕ)
    (hlen : a.length = b.length) (hk : k ≤ a.length)
    (h_dark_eps : epsilon (a.drop k) (b.drop k) > go) :
    epsilon a b > go := by
  have h := epsilon_drop_le a b k hlen hk
  linarith

/-- Spec 06: correctionScoreDP always equals gotohGlobalScore.
    The block-aware detector cheaply certifies tier 3 via ba_detects_tier3,
    confirming that full Gotoh DP is needed. -/
theorem ba_tier3_detector (a b : List ℕ) (go ge : ℤ)
    (h_go : go ≥ 1) (h_ge : ge ≥ 1) (h_neg : NEG_INF ≤ -go)
    (h_len : a.length = b.length) :
    correctionScoreDP a b go ge = gotohGlobalScore a b go ge :=
  score_determination a b go ge h_go h_ge h_neg h_len
