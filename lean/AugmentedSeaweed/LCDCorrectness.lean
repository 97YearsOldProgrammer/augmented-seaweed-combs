/-
  FlashAlignment/LCDCorrectness.lean

  LCD Correctness: the single-character comb is the correct base case
  for incremental composition.

  For a single character c against reference B of length n, the LCD comb
  produces a d_col where:
  - d_col[j] = 0 if b[j] ≠ c (no contribution at mismatches)
  - d_col[j] = j - prev_match(j) if b[j] = c (gap to previous match)

  The crossing count at any window [s, s+w) equals:
    1 if c appears in B[s:s+w], 0 otherwise

  Paper reference: Tiskin 2022 (monograph), Section 5
-/
import Mathlib.Tactic
import AugmentedSeaweed.CombComposition

/-! ## LCD Computation -/

/-- LCD step: process one column of the single-character comb.
    Since d_col starts at 0 and we process left-to-right,
    d_col[c] = 0 when first reached, so mismatch-swap never occurs. -/
def lcdStep (char bChar : ℕ) (d_row : ℕ) : ℕ × ℕ :=
  if char == bChar then
    (d_row, 1)       -- match: d_col gets d_row, d_row resets to 0+1=1
  else
    (0, d_row + 1)   -- mismatch: d_col stays 0, d_row increments

/-- LCD fold: process all columns left-to-right.
    Returns (d_col as list, final d_row value). -/
def lcdFoldAux (char : ℕ) (b : List ℕ) : List ℕ × ℕ :=
  b.foldl (fun (acc : List ℕ × ℕ) bc =>
    let (dc_val, dr') := lcdStep char bc acc.2
    (acc.1 ++ [dc_val], dr')
  ) ([], 1)

/-- LCD: compute d_col for a single character against reference b. -/
def lcdDcol (char : ℕ) (b : List ℕ) : List ℕ :=
  (lcdFoldAux char b).1

/-! ## LCD Structure Lemmas -/

/-- At a mismatch, LCD produces d_col = 0. -/
theorem lcdStep_mismatch (char bChar : ℕ) (d_row : ℕ) (h : ¬(char == bChar)) :
    (lcdStep char bChar d_row).1 = 0 := by
  simp [lcdStep, h]

/-- At a match, LCD produces d_col = d_row (positive). -/
theorem lcdStep_match (char bChar : ℕ) (d_row : ℕ) (h : char == bChar) :
    (lcdStep char bChar d_row).1 = d_row := by
  simp [lcdStep, h]

/-- After a match, d_row resets to 1. -/
theorem lcdStep_match_drow (char bChar : ℕ) (d_row : ℕ) (h : char == bChar) :
    (lcdStep char bChar d_row).2 = 1 := by
  simp [lcdStep, h]

/-- After a mismatch, d_row increments by 1. -/
theorem lcdStep_mismatch_drow (char bChar : ℕ) (d_row : ℕ) (h : ¬(char == bChar)) :
    (lcdStep char bChar d_row).2 = d_row + 1 := by
  simp [lcdStep, h]

/-! ## Crossing Count and Character Occurrence -/

/-- Crossing count: number of positions j in [s, s+w) where d_col[j] > j - s. -/
def crossingCount (d_col : List ℕ) (s w : ℕ) : ℕ :=
  (List.range w).countP (fun i => decide (d_col.getD (s + i) 0 > i))

/-- Character occurrence in a window (decidable). -/
def charOccurs (char : ℕ) (b : List ℕ) (s w : ℕ) : Bool :=
  (List.range w).any (fun i => b.getD (s + i) (char + 1) == char)

/-! ## Crossing Count = Character Occurrence

### Proof Sketch (verified empirically for |Σ| ≤ 4, n ≤ 9, all 58M+ cases)

Let match positions be j₀ < j₁ < ... < j_{K-1} where b[j_k] = char.

**d_col formula** (proved by induction on columns):
- d_col[j] = 0 if b[j] ≠ char
- d_col[j₀] = j₀ + 1  (d_row before first match = initial value 1 + j₀ mismatches)
- d_col[j_k] = j_k - j_{k-1}  for k ≥ 1  (d_row resets to 1 after each match)

**Crossing analysis** at window [s, s+w):
- Non-match j: d_col[j] = 0 ≤ j - s, no crossing. ✓
- Match j_k: crossing ⟺ d_col[j_k] > j_k - s ⟺ j_{k-1} < s.
  (Setting j_{-1} = -1 for k = 0.)
- First match in window: j_{k-1} < s always (either k=0 or j_{k-1} outside window). ✓
- Later matches: j_{k'-1} ≥ s (previous match is within window). ✗

Therefore: crossing count = 1 if char ∈ b[s:s+w], 0 otherwise. □
-/

/-! ## Concrete Verification -/

-- Specific (s, w) pairs verified via native_decide

example : crossingCount (lcdDcol 0 [0,1,0,1,0]) 0 5 = 1 := by native_decide
example : crossingCount (lcdDcol 0 [0,1,0,1,0]) 1 3 = 1 := by native_decide
example : crossingCount (lcdDcol 0 [0,1,0,1,0]) 1 1 = 0 := by native_decide
example : crossingCount (lcdDcol 0 [0,1,0,1,0]) 3 1 = 0 := by native_decide

example : crossingCount (lcdDcol 2 [0,1,0,1,0]) 0 5 = 0 := by native_decide
example : crossingCount (lcdDcol 2 [0,1,0,1,0]) 2 2 = 0 := by native_decide

example : crossingCount (lcdDcol 0 [0,0,0,0,0]) 0 5 = 1 := by native_decide
example : crossingCount (lcdDcol 0 [0,0,0,0,0]) 2 3 = 1 := by native_decide
example : crossingCount (lcdDcol 0 [0,0,0,0,0]) 4 1 = 1 := by native_decide

-- Verify d_col values directly
example : lcdDcol 0 [0,1,0,1,0] = [1, 0, 2, 0, 2] := by native_decide
example : lcdDcol 0 [1,1,0,0,1] = [0, 0, 3, 1, 0] := by native_decide
example : lcdDcol 0 [0,0,0,0,0] = [1, 1, 1, 1, 1] := by native_decide
example : lcdDcol 1 [0,1,0,1,0] = [0, 2, 0, 2, 0] := by native_decide

/-! ## Bounded Verification via Fin -/

/-- All windows for char=0 vs [0,1,0,1,0] (length 5).
    Uses Fin to make the quantifier decidable. -/
example : ∀ (s : Fin 6) (w : Fin 6),
    s.val + w.val ≤ 5 → w.val > 0 →
    crossingCount (lcdDcol 0 [0,1,0,1,0]) s.val w.val =
    if charOccurs 0 [0,1,0,1,0] s.val w.val then 1 else 0 := by
  native_decide

/-- All windows for char=1 vs [0,1,0,0,1,1] (length 6). -/
example : ∀ (s : Fin 7) (w : Fin 7),
    s.val + w.val ≤ 6 → w.val > 0 →
    crossingCount (lcdDcol 1 [0,1,0,0,1,1]) s.val w.val =
    if charOccurs 1 [0,1,0,0,1,1] s.val w.val then 1 else 0 := by
  native_decide

/-! ## LCD as Composition Basis -/

/-- colStep with dc = 0 equals lcdStep (the mismatch-swap branch 0 > d_row
    never fires). -/
private theorem colStep_zero_eq_lcdStep (char bChar d_row : ℕ) :
    colStep char bChar 0 d_row = lcdStep char bChar d_row := by
  simp only [colStep, lcdStep]
  split
  · simp
  · simp [Nat.not_lt.mpr (Nat.zero_le d_row)]

/-- Recursive LCD: compute d_col for char vs b[0..k) returning (d_col_list, d_row).
    This is equivalent to lcdFoldAux but defined recursively for easier induction. -/
private def lcdRec (char : ℕ) (b : List ℕ) (k : ℕ) : List ℕ × ℕ :=
  match k with
  | 0 => ([], 1)
  | k' + 1 =>
    let (prev_dcol, prev_dr) := lcdRec char b k'
    let bc := b.getD k' 0
    let (dc_val, dr') := lcdStep char bc prev_dr
    (prev_dcol ++ [dc_val], dr')

/-- lcdRec produces a list of length k. -/
private theorem lcdRec_length (char : ℕ) (b : List ℕ) (k : ℕ) :
    (lcdRec char b k).1.length = k := by
  induction k with
  | zero => simp [lcdRec]
  | succ k' ih => simp [lcdRec, ih]

/-- lcdRec: d_col values at positions < k are unchanged by processing column k. -/
private theorem lcdRec_getD_lt (char : ℕ) (b : List ℕ) (j k : ℕ) (hjk : j < k) :
    (lcdRec char b (k + 1)).1.getD j 0 = (lcdRec char b k).1.getD j 0 := by
  show (lcdRec char b (k + 1)).1.getD j 0 = (lcdRec char b k).1.getD j 0
  simp only [lcdRec, List.getD]
  have hl : (lcdRec char b k).1.length = k := lcdRec_length char b k
  congr 1
  exact List.getElem?_append_left (by omega)

/-- The d_col value at position j: match → d_row, mismatch → 0. -/
private theorem lcdRec_getD_eq (char : ℕ) (b : List ℕ) (j : ℕ) :
    (lcdRec char b (j + 1)).1.getD j 0 =
    if b.getD j 0 == char then (lcdRec char b j).2 else 0 := by
  show (lcdRec char b (j + 1)).1.getD j 0 = if b.getD j 0 == char then (lcdRec char b j).2 else 0
  simp only [List.getD_eq_getElem?_getD, beq_iff_eq]
  simp only [lcdRec, lcdStep]
  have hl : (lcdRec char b j).1.length = j := lcdRec_length char b j
  rw [List.getElem?_append_right (by omega)]
  simp [hl]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; tauto)

/-- Extending lcdRec preserves d_col values at earlier positions. -/
private theorem lcdRec_getD_of_lt (char : ℕ) (b : List ℕ) (j n : ℕ) (hjn : j < n) :
    (lcdRec char b n).1.getD j 0 = (lcdRec char b (j + 1)).1.getD j 0 := by
  induction n with
  | zero => omega
  | succ n' ih =>
    by_cases h : j < n'
    · rw [lcdRec_getD_lt char b j n' h]
      exact ih h
    · have : n' = j := by omega
      subst this; rfl

/-- d_row evolution: after a match, d_row = 1; after a mismatch, d_row increments. -/
private theorem lcdRec_drow_step (char : ℕ) (b : List ℕ) (j : ℕ) :
    (lcdRec char b (j + 1)).2 =
    if b.getD j 0 == char then 1 else (lcdRec char b j).2 + 1 := by
  simp only [lcdRec, lcdStep, beq_iff_eq, List.getD_eq_getElem?_getD]
  by_cases h : char = b[j]?.getD 0
  · simp [h]
  · simp [h, show ¬(b[j]?.getD 0 = char) from fun h' => h h'.symm]

/-- d_row counts consecutive mismatches + 1 from the last match.
    No match in [p..j) implies d_row > j - p. -/
private theorem lcdRec_drow_no_match (char : ℕ) (b : List ℕ) (p j : ℕ)
    (hpj : p ≤ j)
    (hno : ∀ q, p ≤ q → q < j → ¬(b.getD q 0 == char)) :
    (lcdRec char b j).2 > j - p := by
  induction j with
  | zero => simp [lcdRec]
  | succ j' ih =>
    by_cases hp : p ≤ j'
    · rw [lcdRec_drow_step]
      have hno_j' : ¬(b.getD j' 0 == char) = true := hno j' hp (by omega)
      rw [if_neg hno_j']
      have ih_applied := ih hp (fun q hpq hqj => hno q hpq (by omega))
      omega
    · -- p = j' + 1, need d_row > 0
      have : j' + 1 - p = 0 := by omega
      rw [this]
      exact Nat.pos_of_ne_zero (by
        rw [lcdRec_drow_step]
        split <;> omega)

/-- If there's a match at position p < j, then d_row ≤ j - p. -/
private theorem lcdRec_drow_match_bound (char : ℕ) (b : List ℕ) (p j : ℕ)
    (hpj : p < j) (hmatch : b.getD p 0 == char) :
    (lcdRec char b j).2 ≤ j - p := by
  induction j with
  | zero => omega
  | succ j' ih =>
    rw [lcdRec_drow_step]
    by_cases hmatch_j : (b.getD j' 0 == char) = true
    · rw [if_pos hmatch_j]; omega
    · rw [if_neg hmatch_j]
      by_cases hjp : p < j'
      · have := ih hjp; omega
      · -- p = j', contradiction: hmatch says match at p = j' but hmatch_j says mismatch
        have : j' = p := by omega
        subst this
        exfalso; exact hmatch_j hmatch

/-- lcdFoldAux equals lcdRec at full length. -/
private theorem lcdFoldAux_eq_lcdRec (char : ℕ) (b : List ℕ) :
    lcdFoldAux char b = lcdRec char b b.length := by
  suffices gen : ∀ (b : List ℕ) (k : ℕ) (hk : k ≤ b.length),
      (b.take k).foldl (fun (acc : List ℕ × ℕ) bc =>
        let (dc_val, dr') := lcdStep char bc acc.2
        (acc.1 ++ [dc_val], dr')) ([], 1) = lcdRec char b k by
    have := gen b b.length (Nat.le_refl _)
    simp [List.take_length] at this
    exact this
  intro b' k hk
  induction k with
  | zero => simp [lcdRec, List.take]
  | succ k' ih =>
    have hk' : k' ≤ b'.length := Nat.le_of_succ_le hk
    have hk'_lt : k' < b'.length := by omega
    rw [List.take_succ_eq_append_getElem hk'_lt]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih hk']
    simp only [lcdRec]
    have getD_eq : b'.getD k' 0 = b'[k'] := by
      simp [List.getD, List.getElem?_eq_getElem hk'_lt]
    rw [← getD_eq]

/-- lcdDcol value at position j equals lcdRec value at that position. -/
private theorem lcdDcol_getD_eq (char : ℕ) (b : List ℕ) (j : ℕ) (hj : j < b.length) :
    (lcdDcol char b).getD j 0 = (lcdRec char b (j + 1)).1.getD j 0 := by
  have h1 := lcdFoldAux_eq_lcdRec char b
  simp only [lcdDcol]
  rw [h1]
  exact lcdRec_getD_of_lt char b j b.length hj

/-! ## The LCD Crossing Count Theorem -/

/-- **LCD Crossing Count Theorem**: For a single character c and reference b,
    the crossing count at window [s, s+w) equals 1 if c appears in the window,
    0 otherwise. -/
theorem lcd_crossing_eq_occurrence (char : ℕ) (b : List ℕ) (s w : ℕ)
    (hs : s + w ≤ b.length) (hw : w > 0) :
    crossingCount (lcdDcol char b) s w =
    if charOccurs char b s w then 1 else 0 := by
  -- Helper: getD with different defaults agree when index in bounds
  have getD_agree : ∀ (i : ℕ) (d1 d2 : ℕ), i < b.length → b.getD i d1 = b.getD i d2 := by
    intro i d1 d2 hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  -- Crossing iff: d_col[s+i] > i iff first match in window at position s+i
  have crossing_iff : ∀ (i : ℕ), i < w →
      ((decide ((lcdDcol char b).getD (s + i) 0 > i) = true) ↔
       ((b.getD (s + i) 0 == char) = true ∧
        ∀ q, s ≤ q → q < s + i → ¬(b.getD q 0 == char) = true)) := by
    intro i hi
    constructor
    · intro hcross
      simp only [decide_eq_true_eq] at hcross
      rw [lcdDcol_getD_eq char b (s + i) (by omega)] at hcross
      rw [lcdRec_getD_eq] at hcross
      split at hcross
      · rename_i hmatch
        exact ⟨hmatch, fun q hsq hqs hmq =>
          absurd (lcdRec_drow_match_bound char b q (s + i) (by omega) hmq) (by omega)⟩
      · omega
    · intro ⟨hmatch, hno_earlier⟩
      simp only [decide_eq_true_eq]
      rw [lcdDcol_getD_eq char b (s + i) (by omega), lcdRec_getD_eq, if_pos hmatch]
      have := lcdRec_drow_no_match char b s (s + i) (by omega) hno_earlier
      omega
  -- Connect charOccurs (default char+1) with getD (default 0)
  have occurs_iff : charOccurs char b s w = true ↔
      ∃ i, i < w ∧ (b.getD (s + i) 0 == char) = true := by
    simp only [charOccurs, List.any_eq_true, List.mem_range, beq_iff_eq]
    exact ⟨
      fun ⟨i, hi, heq⟩ => ⟨i, hi, by rw [← getD_agree (s + i) 0 (char + 1) (by omega)] at heq; exact heq⟩,
      fun ⟨i, hi, heq⟩ => ⟨i, hi, by rw [getD_agree (s + i) (char + 1) 0 (by omega)]; exact heq⟩⟩
  -- Main proof by cases on charOccurs
  simp only [crossingCount]
  by_cases hocc : charOccurs char b s w = true
  · rw [if_pos hocc]
    obtain ⟨i₀, hi₀, hm₀⟩ := occurs_iff.mp hocc
    let p := fun i => i < w ∧ (b.getD (s + i) 0 == char) = true
    have hexp : ∃ i, p i := ⟨i₀, hi₀, hm₀⟩
    let i_min := Nat.find hexp
    have hi_min_bound : i_min < w := (Nat.find_spec hexp).1
    have hi_min_match : (b.getD (s + i_min) 0 == char) = true := (Nat.find_spec hexp).2
    have hi_min_min : ∀ j, j < i_min → ¬(j < w ∧ (b.getD (s + j) 0 == char) = true) :=
      fun j hj => Nat.find_min hexp hj
    have pred_iff : ∀ i ∈ List.range w,
        (decide ((lcdDcol char b).getD (s + i) 0 > i) = true) ↔ (i = i_min) := by
      intro i hi_mem
      simp only [List.mem_range] at hi_mem
      rw [crossing_iff i hi_mem]
      constructor
      · intro ⟨hm, hno⟩
        by_contra hne
        by_cases hlt : i < i_min
        · exact (hi_min_min i hlt) ⟨hi_mem, hm⟩
        · have : i_min < i := by omega
          exact hno (s + i_min) (by omega) (by omega) hi_min_match
      · intro heq; subst heq
        exact ⟨hi_min_match, fun q hsq hqs hm =>
          (hi_min_min (q - s) (by omega)) ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega : s ≤ q)]⟩⟩
    -- countP equals count of i_min in List.range w
    have countP_eq : (List.range w).countP (fun i => decide ((lcdDcol char b).getD (s + i) 0 > i)) =
        (List.range w).count i_min := by
      rw [List.countP_eq_length_filter, List.count, List.countP_eq_length_filter]
      congr 1
      apply List.filter_congr
      intro i hi
      have h_iff := pred_iff i hi
      rw [Bool.eq_iff_iff, beq_iff_eq]
      exact h_iff
    rw [countP_eq, List.count_range, if_pos hi_min_bound]
  · rw [if_neg hocc]
    -- No match in window: every position has d_col[s+i] = 0 (mismatch) or d_col > i fails
    apply List.countP_eq_zero.mpr
    intro i hi
    simp only [List.mem_range] at hi
    simp only [decide_eq_true_eq, not_lt]
    rw [lcdDcol_getD_eq char b (s + i) (by omega), lcdRec_getD_eq]
    have hno : ¬(b.getD (s + i) 0 == char) = true := by
      intro hm
      exact hocc (occurs_iff.mpr ⟨i, hi, hm⟩)
    rw [if_neg hno]
    omega

/-! ## LCD = Comb (composition basis) -/

/-- The comb column fold result at step k equals lcdRec (modulo take/padding). -/
private theorem comb_fold_eq_lcdRec (char : ℕ) (b : List ℕ) :
    let comb := (List.range b.length).foldl (colFoldStep char b)
                  (List.replicate b.length 0, 1)
    comb.1 = (lcdRec char b b.length).1 ∧ comb.2 = (lcdRec char b b.length).2 := by
  suffices gen : ∀ (k : ℕ) (hk : k ≤ b.length),
      let comb_k := (List.range k).foldl (colFoldStep char b)
                      (List.replicate b.length 0, 1)
      comb_k.1 = (lcdRec char b k).1 ++ List.replicate (b.length - k) 0 ∧
      comb_k.2 = (lcdRec char b k).2 by
    have := gen b.length (Nat.le_refl _)
    simp at this
    exact ⟨this.1, this.2⟩
  intro k hk
  induction k with
  | zero =>
    simp [lcdRec, List.range_zero]
  | succ k' ih =>
    have hk' : k' ≤ b.length := Nat.le_of_succ_le hk
    have hk'_lt : k' < b.length := by omega
    have prev := ih hk'
    rw [List.range_succ]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set comb_k' := (List.range k').foldl (colFoldStep char b)
                     (List.replicate b.length 0, 1) with h_comb
    set lcd_k' := lcdRec char b k' with h_lcd
    have h_list : comb_k'.1 = lcd_k'.1 ++ List.replicate (b.length - k') 0 := prev.1
    have h_dr : comb_k'.2 = lcd_k'.2 := prev.2
    simp only [colFoldStep, lcdRec]
    have h_len_lcd : lcd_k'.1.length = k' := by
      simp [h_lcd, lcdRec_length]
    have h_getD_zero : comb_k'.1.getD k' 0 = 0 := by
      rw [h_list]
      simp only [List.getD]
      rw [List.getElem?_append_right (by omega)]
      have h_sub : k' - lcd_k'.1.length = 0 := by omega
      rw [h_sub]
      simp only [List.getElem?_replicate]
      split <;> simp
    rw [h_getD_zero, h_dr]
    have h_step := colStep_zero_eq_lcdStep char (b.getD k' 0) lcd_k'.2
    rw [h_step]
    constructor
    · rw [h_list]
      have h_rep : List.replicate (b.length - k') 0 =
          (0 : ℕ) :: List.replicate (b.length - k' - 1) 0 := by
        rw [← List.replicate_succ]
        congr 1; omega
      rw [h_rep, List.set_append_right k' _ (by omega)]
      have h_len_lcd2 : (lcdRec char b k').1.length = k' := lcdRec_length char b k'
      rw [h_len_lcd2, Nat.sub_self]
      simp only [List.set_cons_zero]
      simp only [h_lcd, List.append_assoc, List.singleton_append]
      have : b.length - k' - 1 = b.length - (k' + 1) := by omega
      rw [this]
    · rfl

/-- Main connection: the full LCD fold equals the comb column fold. -/
private theorem lcd_comb_fold_eq (char : ℕ) (b : List ℕ) :
    let lcd := lcdFoldAux char b
    let comb := (List.range b.length).foldl (colFoldStep char b)
                  (List.replicate b.length 0, 1)
    lcd.1 = comb.1 ∧ lcd.2 = comb.2 := by
  have h1 := lcdFoldAux_eq_lcdRec char b
  have h2 := comb_fold_eq_lcdRec char b
  constructor
  · rw [h1]; exact h2.1.symm
  · rw [h1]; exact h2.2.symm

/-- LCD equals the combDcol for a single-character string.
    (The comb processes one row with the same logic as lcdFoldAux,
    except that lcdFoldAux optimizes away the impossible mismatch-swap case.) -/
theorem lcd_eq_comb (char : ℕ) (b : List ℕ) :
    lcdDcol char b = combDcol [char] b := by
  simp only [lcdDcol, combDcol, combFold, combInit, rowFoldStep, List.foldl]
  exact (lcd_comb_fold_eq char b).1
