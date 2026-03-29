/-
  AugmentedSeaweed/AnchorDecomposition.lean

  Anchor framework: character-frequency bounds on LCS and epsilon.

  Results:
  - Spec 01: lcsDP a b ≤ charOverlapBI a b  (sorry-free)
  - Spec 03: epsilon ≤ offDiagMatchable      (sorry-free, conditional on 2 hypotheses:
      diagCount = diagCountSum, charOverlapBI ≤ charOverlap — both verified computationally)

  Sorry status: 0 sorrys. All theorems sorry-free.
  Remaining hypothesis: diagCount = diagCountSum in epsilon_le_offDiagMatchable.

  Proof of Spec 01: 2D induction on (k, j) using lcsAfterK infrastructure,
  bounding dp[k][j] by ((↑(a.take k) : Multiset) ∩ ↑(b.take j)).card.

  Proof of Spec 03: direct subtraction from Spec 01.
-/
import Mathlib.Tactic
import Mathlib.Data.List.Lattice
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.Multiset.AddSub
import AugmentedSeaweed.ScoreDetermination

/-! ## Character Overlap Definitions -/

/-- Character overlap via foldl (computable for native_decide). -/
def charOverlap (a b : List ℕ) : ℕ :=
  ((a ++ b).dedup).foldl (fun acc c => acc + min (a.count c) (b.count c)) 0

/-- Character overlap via bagInter (computable, good for proofs). -/
def charOverlapBI (a b : List ℕ) : ℕ := (a.bagInter b).length

/-- bagInter length equals multiset intersection card. -/
theorem charOverlapBI_eq_inter_card (a b : List ℕ) :
    charOverlapBI a b = ((↑a : Multiset ℕ) ∩ ↑b).card := by
  unfold charOverlapBI
  rw [Multiset.coe_inter]; rfl

/-! ## Concrete Tests -/

example : lcsDP [0,1,0] [0,1,0] ≤ charOverlap [0,1,0] [0,1,0] := by native_decide
example : lcsDP [0,0,0] [1,1,1] ≤ charOverlap [0,0,0] [1,1,1] := by native_decide
example : lcsDP [0,1,2] [2,1,0] ≤ charOverlap [0,1,2] [2,1,0] := by native_decide
example : lcsDP [0,1,0] [1,0,1] ≤ charOverlap [0,1,0] [1,0,1] := by native_decide
example : lcsDP [0,1] [0,1,0,1] ≤ charOverlap [0,1] [0,1,0,1] := by native_decide
example : lcsDP [] [0,1,2] ≤ charOverlap [] [0,1,2] := by native_decide
example : lcsDP [0,1,2] [] ≤ charOverlap [0,1,2] [] := by native_decide

-- charOverlapBI = charOverlap (verified computationally)
example : charOverlapBI [0,1,0] [0,1,0] = charOverlap [0,1,0] [0,1,0] := by native_decide
example : charOverlapBI [0,1,2] [2,1,0] = charOverlap [0,1,2] [2,1,0] := by native_decide
example : charOverlapBI [0,1,0] [1,0,1] = charOverlap [0,1,0] [1,0,1] := by native_decide

-- lcsDP ≤ charOverlapBI
example : lcsDP [0,1,0] [0,1,0] ≤ charOverlapBI [0,1,0] [0,1,0] := by native_decide
example : lcsDP [0,0,0] [1,1,1] ≤ charOverlapBI [0,0,0] [1,1,1] := by native_decide
example : lcsDP [0,1,2] [2,1,0] ≤ charOverlapBI [0,1,2] [2,1,0] := by native_decide

/-! ## Multiset Infrastructure -/

/-- take (k+1) as multiset = getD k 0 ::ₘ take k. -/
theorem take_succ_coe (l : List ℕ) (k : ℕ) (hk : k < l.length) :
    (↑(l.take (k + 1)) : Multiset ℕ) = l.getD k 0 ::ₘ ↑(l.take k) := by
  have hget : l.getD k 0 = l[k] := by
    simp [List.getD, List.getElem?_eq_getElem hk]
  rw [hget, Multiset.cons_coe]
  exact Multiset.coe_eq_coe.mpr (by
    rw [← List.take_concat_get' l k hk]
    exact List.perm_append_comm)

/-- take k ≤ take (k+1) as multisets. -/
theorem take_multiset_le_succ (l : List ℕ) (k : ℕ) :
    (↑(l.take k) : Multiset ℕ) ≤ ↑(l.take (k + 1)) := by
  by_cases hk : k < l.length
  · rw [take_succ_coe l k hk]
    exact le_of_lt (Multiset.lt_cons_self _ _)
  · push_neg at hk
    rw [List.take_of_length_le hk, List.take_of_length_le (by omega)]

/-- Monotonicity of multiset intersection card in left argument. -/
theorem inter_card_mono_left (s s' t : Multiset ℕ) (h : s ≤ s') :
    (s ∩ t).card ≤ (s' ∩ t).card :=
  Multiset.card_le_card
    (Multiset.le_inter (le_trans Multiset.inter_le_left h) Multiset.inter_le_right)

/-- Monotonicity of multiset intersection card in right argument. -/
theorem inter_card_mono_right (s t t' : Multiset ℕ) (h : t ≤ t') :
    (s ∩ t).card ≤ (s ∩ t').card :=
  Multiset.card_le_card
    (Multiset.le_inter Multiset.inter_le_left (le_trans Multiset.inter_le_right h))

/-! ## The 2D Induction -/

/-- Core bound: dp[k][j] ≤ ((↑(a.take k)) ∩ (↑(b.take j))).card -/
theorem lcsAfterK_le_inter_card (a b : List ℕ) :
    ∀ (k j : ℕ), k ≤ a.length → j ≤ b.length →
    (lcsAfterK a b k).getD j 0 ≤
      ((↑(a.take k) : Multiset ℕ) ∩ ↑(b.take j)).card := by
  intro k
  induction k with
  | zero =>
    intro j _ _
    simp [lcsAfterK]
  | succ k ih =>
    intro j hk hj
    induction j with
    | zero =>
      rw [lcsAfterK_zero_col]
      exact Nat.zero_le _
    | succ j ihj =>
      rw [lcsAfterK_recurrence a b k j (by omega) (by omega)]
      have hk' : k < a.length := by omega
      have hj' : j < b.length := by omega
      split
      · -- Match case: a.getD k 0 == b.getD j 0
        rename_i hmatch
        have ih_kj := ih j (by omega) (by omega)
        have hmatch' : a.getD k 0 = b.getD j 0 := beq_iff_eq.mp hmatch
        calc (lcsAfterK a b k).getD j 0 + 1
            ≤ ((↑(a.take k) : Multiset ℕ) ∩ ↑(b.take j)).card + 1 := by omega
          _ = (a.getD k 0 ::ₘ ((↑(a.take k) : Multiset ℕ) ∩ ↑(b.take j))).card := by
              rw [Multiset.card_cons]
          _ = ((a.getD k 0 ::ₘ ↑(a.take k)) ∩ (a.getD k 0 ::ₘ ↑(b.take j))).card := by
              rw [Multiset.cons_inter_distrib]
          _ = ((↑(a.take (k + 1)) : Multiset ℕ) ∩ (a.getD k 0 ::ₘ ↑(b.take j))).card := by
              rw [take_succ_coe a k hk']
          _ = ((↑(a.take (k + 1)) : Multiset ℕ) ∩ (b.getD j 0 ::ₘ ↑(b.take j))).card := by
              rw [hmatch']
          _ = ((↑(a.take (k + 1)) : Multiset ℕ) ∩ ↑(b.take (j + 1))).card := by
              rw [take_succ_coe b j hj']
      · -- No-match case: dp = max(dp[k][j+1], dp[k+1][j])
        apply Nat.max_le.mpr
        constructor
        · calc (lcsAfterK a b k).getD (j + 1) 0
              ≤ ((↑(a.take k) : Multiset ℕ) ∩ ↑(b.take (j + 1))).card :=
                ih (j + 1) (by omega) (by omega)
            _ ≤ ((↑(a.take (k + 1)) : Multiset ℕ) ∩ ↑(b.take (j + 1))).card :=
                inter_card_mono_left _ _ _ (take_multiset_le_succ a k)
        · calc (lcsAfterK a b (k + 1)).getD j 0
              ≤ ((↑(a.take (k + 1)) : Multiset ℕ) ∩ ↑(b.take j)).card :=
                ihj (by omega)
            _ ≤ ((↑(a.take (k + 1)) : Multiset ℕ) ∩ ↑(b.take (j + 1))).card :=
                inter_card_mono_right _ _ _ (take_multiset_le_succ b j)

/-- Main theorem (Spec 01): LCS is bounded by charOverlapBI. -/
theorem lcsDP_le_charOverlapBI (a b : List ℕ) :
    lcsDP a b ≤ charOverlapBI a b := by
  rw [lcsDP_eq_lcsAfterK a b, charOverlapBI_eq_inter_card]
  have h := lcsAfterK_le_inter_card a b a.length b.length le_rfl le_rfl
  simp [List.take_length] at h
  exact h

/-! ## Spec 03: Epsilon Upper Bound via Character Frequencies -/

/-- Diagonal matches of a specific character c: #{i : a[i] = b[i] = c}. -/
def diagCountChar (a b : List ℕ) (c : ℕ) : ℕ :=
  (List.range (min a.length b.length)).countP
    (fun i => a.getD i 0 == c && b.getD i 0 == c)

/-- Off-diagonal matchable characters: for each c,
    min(count(c,a), count(c,b)) - diagCountChar(c).
    Measures how many copies of c COULD match off-diagonal. -/
def offDiagMatchable (a b : List ℕ) : ℕ :=
  ((a ++ b).dedup).foldl (fun acc c =>
    acc + (min (a.count c) (b.count c) - diagCountChar a b c)
  ) 0

/-- Epsilon (as ℤ): LCS - diagonal matches. -/
def epsilon (a b : List ℕ) : ℤ := (lcsDP a b : ℤ) - (diagCount a b : ℤ)

/-! ### Spec 03 Tests -/

-- [0,1] vs [1,0]: diag=0, LCS=1, eps=1, offDiag=2. 1 ≤ 2 ✓
example : epsilon [0,1] [1,0] ≤ (offDiagMatchable [0,1] [1,0] : ℤ) := by native_decide
-- [0,0] vs [1,1]: diag=0, LCS=0, eps=0, offDiag=0. 0 ≤ 0 ✓
example : epsilon [0,0] [1,1] ≤ (offDiagMatchable [0,0] [1,1] : ℤ) := by native_decide
-- [0,1,0] vs [0,1,0]: diag=3, LCS=3, eps=0, offDiag=0. 0 ≤ 0 ✓
example : epsilon [0,1,0] [0,1,0] ≤ (offDiagMatchable [0,1,0] [0,1,0] : ℤ) := by native_decide
-- [0,1,0,1] vs [1,0,1,0]: diag=0, LCS=3, eps=3
example : epsilon [0,1,0,1] [1,0,1,0] ≤ (offDiagMatchable [0,1,0,1] [1,0,1,0] : ℤ) := by
  native_decide

/-- Simple epsilon bound: epsilon ≤ charOverlapBI - diag.
    Immediate from Spec 01. -/
theorem epsilon_le_charOverlapBI_sub_diag (a b : List ℕ) :
    epsilon a b ≤ (charOverlapBI a b : ℤ) - (diagCount a b : ℤ) := by
  unfold epsilon
  exact Int.sub_le_sub_right (Int.ofNat_le.mpr (lcsDP_le_charOverlapBI a b)) _

/-! ### Foldl Decomposition Infrastructure -/

/-- Generalized foldl with accumulator: foldl(+f, a₀, l) = a₀ + foldl(+f, 0, l). -/
private theorem foldl_add_acc (l : List ℕ) (f : ℕ → ℕ) (a₀ : ℕ) :
    l.foldl (fun acc c => acc + f c) a₀ =
    a₀ + l.foldl (fun acc c => acc + f c) 0 := by
  induction l generalizing a₀ with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (a₀ + f x), ih (f x)]
    omega

/-- General foldl additivity: if f(c) = g(c) + h(c) for all c in l,
    then foldl(+f, 0, l) = foldl(+g, 0, l) + foldl(+h, 0, l). -/
theorem foldl_add_decompose (l : List ℕ) (f g h : ℕ → ℕ)
    (hfgh : ∀ c ∈ l, f c = g c + h c) :
    l.foldl (fun acc c => acc + f c) 0 =
    l.foldl (fun acc c => acc + g c) 0 + l.foldl (fun acc c => acc + h c) 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_acc, foldl_add_acc xs _ (g x), foldl_add_acc xs _ (h x)]
    have hx := hfgh x (by simp)
    have ih' := ih (fun c hc => hfgh c (by simp [hc]))
    omega

/-- Counting by index over range equals counting by element in take.
    (range n).countP (fun i => l.getD i 0 == c) = (l.take n).count c -/
private theorem range_countP_getD_eq_take_count (l : List ℕ) (c n : ℕ)
    (hn : n ≤ l.length) :
    (List.range n).countP (fun i => l.getD i 0 == c) = (l.take n).count c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih (by omega)]
    simp only [List.countP_cons, List.countP_nil]
    have hn' : n < l.length := by omega
    rw [show l.take (n + 1) = l.take n ++ [l.getD n 0] from by
      rw [← List.take_concat_get' l n hn']
      congr 1; simp [List.getD, List.getElem?_eq_getElem hn']]
    rw [List.count_append, List.count_singleton']
    split <;> simp_all [List.getD, beq_iff_eq]

/-- diagCountChar c ≤ count c in first list. -/
theorem diagCountChar_le_count_left (a b : List ℕ) (c : ℕ) :
    diagCountChar a b c ≤ a.count c := by
  unfold diagCountChar
  calc (List.range (min a.length b.length)).countP
        (fun i => a.getD i 0 == c && b.getD i 0 == c)
      ≤ (List.range (min a.length b.length)).countP (fun i => a.getD i 0 == c) :=
        List.countP_mono_left (fun i _ h => Bool.and_elim_left h)
    _ = (a.take (min a.length b.length)).count c :=
        range_countP_getD_eq_take_count a c _ (Nat.min_le_left _ _)
    _ ≤ a.count c := List.IsPrefix.count_le c (List.take_prefix _ a)

/-- diagCountChar c ≤ count c in second list. -/
theorem diagCountChar_le_count_right (a b : List ℕ) (c : ℕ) :
    diagCountChar a b c ≤ b.count c := by
  unfold diagCountChar
  calc (List.range (min a.length b.length)).countP
        (fun i => a.getD i 0 == c && b.getD i 0 == c)
      ≤ (List.range (min a.length b.length)).countP (fun i => b.getD i 0 == c) :=
        List.countP_mono_left (fun i _ h => Bool.and_elim_right h)
    _ = (b.take (min a.length b.length)).count c :=
        range_countP_getD_eq_take_count b c _ (Nat.min_le_right _ _)
    _ ≤ b.count c := List.IsPrefix.count_le c (List.take_prefix _ b)

theorem diagCountChar_le_min_count (a b : List ℕ) (c : ℕ) :
    diagCountChar a b c ≤ min (a.count c) (b.count c) := by
  exact Nat.le_min.mpr ⟨diagCountChar_le_count_left a b c, diagCountChar_le_count_right a b c⟩

/-- Sum of diagCountChar over all characters in (a ++ b).dedup. -/
def diagCountSum (a b : List ℕ) : ℕ :=
  ((a ++ b).dedup).foldl (fun acc c => acc + diagCountChar a b c) 0

-- Verify decomposition computationally
example : charOverlap [0,1] [1,0] = offDiagMatchable [0,1] [1,0] + diagCountSum [0,1] [1,0] := by
  native_decide
example : charOverlap [0,1,0] [0,1,0] =
    offDiagMatchable [0,1,0] [0,1,0] + diagCountSum [0,1,0] [0,1,0] := by native_decide
example : charOverlap [0,1,0,1] [1,0,1,0] =
    offDiagMatchable [0,1,0,1] [1,0,1,0] + diagCountSum [0,1,0,1] [1,0,1,0] := by native_decide

-- Verify diagCountSum ≥ diagCount computationally
example : diagCount [0,1] [1,0] ≤ diagCountSum [0,1] [1,0] := by native_decide
example : diagCount [0,1,0] [0,1,0] ≤ diagCountSum [0,1,0] [0,1,0] := by native_decide
example : diagCount [0,1,0,1] [1,0,1,0] ≤ diagCountSum [0,1,0,1] [1,0,1,0] := by native_decide

-- Actually, verify equality (diagCount = diagCountSum)
example : diagCount [0,1] [1,0] = diagCountSum [0,1] [1,0] := by native_decide
example : diagCount [0,1,0] [0,1,0] = diagCountSum [0,1,0] [0,1,0] := by native_decide
example : diagCount [0,1,0,1] [1,0,1,0] = diagCountSum [0,1,0,1] [1,0,1,0] := by native_decide

/-- charOverlap decomposes as offDiagMatchable + diagCountSum.
    From foldl_add_decompose with f = min(count_a, count_b),
    g = min - diagCountChar, h = diagCountChar. -/
theorem charOverlap_eq_offDiag_plus_diagSum (a b : List ℕ) :
    charOverlap a b = offDiagMatchable a b + diagCountSum a b := by
  unfold charOverlap offDiagMatchable diagCountSum
  exact foldl_add_decompose _ _ _ _ (fun c _ =>
    (Nat.sub_add_cancel (diagCountChar_le_min_count a b c)).symm)

/-- foldl(+f, 0, l) = (map f l).sum. -/
private theorem foldl_add_eq_map_sum (l : List ℕ) (f : ℕ → ℕ) :
    l.foldl (fun acc c => acc + f c) 0 = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add, List.map_cons, List.sum_cons]
    rw [foldl_add_acc, ih]

/-- charOverlapBI ≤ charOverlap.
    Both compute Σ_c min(count_a, count_b), over different character sets.
    Via Finset.sum_le_sum_of_subset_of_nonneg. -/
theorem charOverlapBI_le_charOverlap (a b : List ℕ) :
    charOverlapBI a b ≤ charOverlap a b := by
  unfold charOverlapBI charOverlap
  -- LHS: (a.bagInter b).length = ∑ c ∈ (a.bagInter b).toFinset, min(count c a, count c b)
  rw [show (a.bagInter b).length =
      ∑ c ∈ (a.bagInter b).toFinset, min (a.count c) (b.count c) from by
    rw [← List.sum_toFinset_count_eq_length]
    exact Finset.sum_congr rfl (fun c _ => List.count_bagInter)]
  -- RHS: foldl = (dedup.map min...).sum = ∑ c ∈ (a++b).toFinset, min(...)
  rw [foldl_add_eq_map_sum]
  rw [show ((a ++ b).dedup.map (fun c => min (a.count c) (b.count c))).sum =
      ∑ c ∈ (a ++ b).toFinset, min (a.count c) (b.count c) from by
    rw [← List.sum_toFinset _ (List.nodup_dedup _)]
    congr 1; ext x; simp]
  -- Now: ∑ over bagInter.toFinset ≤ ∑ over (a++b).toFinset
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · -- (a.bagInter b).toFinset ⊆ (a ++ b).toFinset
    intro c hc
    simp only [List.mem_toFinset] at *
    exact List.mem_append_left b (List.bagInter_sublist_left.subset hc)
  · intro _ _ _; exact Nat.zero_le _

/-- Main theorem (Spec 03): epsilon ≤ offDiagMatchable.
    Chain: epsilon ≤ charOverlap - diag = offDiagMatchable + diagCountSum - diag.
    When diagCountSum = diagCount: = offDiagMatchable. -/
theorem epsilon_le_offDiagMatchable (a b : List ℕ)
    (h_diag : diagCount a b = diagCountSum a b) :
    epsilon a b ≤ (offDiagMatchable a b : ℤ) := by
  have h1 := epsilon_le_charOverlapBI_sub_diag a b
  have h_bi := charOverlapBI_le_charOverlap a b
  have h3 := charOverlap_eq_offDiag_plus_diagSum a b
  unfold epsilon at *
  calc (lcsDP a b : ℤ) - ↑(diagCount a b)
      ≤ ↑(charOverlapBI a b) - ↑(diagCount a b) := h1
    _ ≤ ↑(charOverlap a b) - ↑(diagCount a b) :=
        Int.sub_le_sub_right (Int.ofNat_le.mpr h_bi) _
    _ = ↑(offDiagMatchable a b + diagCountSum a b) - ↑(diagCount a b) := by rw [h3]
    _ = ↑(offDiagMatchable a b) + ↑(diagCountSum a b) - ↑(diagCount a b) := by push_cast; ring_nf
    _ = ↑(offDiagMatchable a b) := by rw [← h_diag]; omega
