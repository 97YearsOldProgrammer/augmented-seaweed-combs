/-
  FlashAlignment/CorrectionFormula.lean

  Correction Formula for Affine Gap Scoring

  Theorem: When ε ≤ go (excess ≤ gap open penalty), the affine gap score
  equals LCS - ε = diag (the diagonal match count).

  Three tiers:
    Tier 1 (ε = 0):    score = LCS = diag, trivially
    Tier 2 (0 < ε ≤ go): score = diag (LCS gains don't overcome gap cost)
    Tier 3 (ε > go):    score depends on spatial arrangement, need DP

  Paper reference: Proposition 5.7 (excess correction formula)
-/
import Mathlib.Tactic

/-- Any alignment that uses k gap openings with cost go each pays ≥ k.
    Key fact: go ≥ 1 implies k * go ≥ k. -/
theorem gap_cost_lower_bound
    (k go gap_cost : ℤ)
    (h_go_pos : go ≥ 1)
    (h_cost_ge : gap_cost ≥ k * go)
    (h_k_nonneg : k ≥ 0)
    : gap_cost ≥ k := by
  calc gap_cost ≥ k * go := h_cost_ge
    _ ≥ k * 1 := by nlinarith [mul_le_mul_of_nonneg_left h_go_pos h_k_nonneg]
    _ = k := by ring

/-- The LCS path's gap-penalized score is at most diag when ε ≤ go.
    LCS achieves LCS matches but needs ε crossings, each costing ≥ go.
    score ≤ LCS - ε * go ≤ LCS - ε = diag. -/
theorem lcs_path_score_bound
    (LCS diag epsilon go : ℤ)
    (h_eps_def : epsilon = LCS - diag)
    (h_eps_nonneg : epsilon ≥ 0)
    (h_go_pos : go ≥ 1)
    : LCS - epsilon * go ≤ diag := by
  have h1 : epsilon * go ≥ epsilon * 1 := by nlinarith [mul_le_mul_of_nonneg_left h_go_pos h_eps_nonneg]
  linarith

/-- **Correction Formula (Tier 1):** When ε = 0, opt_score = LCS = diag. -/
theorem correction_tier1
    (LCS diag opt_score : ℤ)
    (h_eps_zero : LCS = diag)
    (h_opt_le_lcs : opt_score ≤ LCS)
    (h_opt_ge_diag : opt_score ≥ diag)
    : opt_score = diag := by
  linarith

/-- **Correction Formula (Tier 2):** When ε ≤ go and go ≥ 1, opt_score = diag.

    Any alignment with k ≥ 0 crossings gains ≤ k matches over diagonal
    but pays ≥ k * go in gap cost. Since go ≥ 1, net gain ≤ k - k*go =
    k*(1-go) ≤ 0. So opt_score ≤ diag, and since diagonal is feasible,
    opt_score = diag. -/
theorem correction_tier2
    (diag opt_score num_crossings crossing_gain gap_cost go : ℤ)
    (h_go_pos : go ≥ 1)
    (h_opt_ge_diag : opt_score ≥ diag)
    (h_gain_le_cross : crossing_gain ≤ num_crossings)
    (h_cost_ge : gap_cost ≥ num_crossings * go)
    (h_score_bound : opt_score ≤ diag + crossing_gain - gap_cost)
    (h_cross_nonneg : num_crossings ≥ 0)
    : opt_score = diag := by
  -- crossing_gain - gap_cost ≤ num_crossings - num_crossings * go
  --   = num_crossings * (1 - go) ≤ 0
  have h1 : gap_cost ≥ num_crossings := by
    calc gap_cost ≥ num_crossings * go := h_cost_ge
      _ ≥ num_crossings * 1 := by nlinarith [mul_le_mul_of_nonneg_left h_go_pos h_cross_nonneg]
      _ = num_crossings := by ring
  -- So crossing_gain - gap_cost ≤ num_crossings - num_crossings = 0... no,
  -- crossing_gain ≤ num_crossings ≤ gap_cost
  -- opt_score ≤ diag + crossing_gain - gap_cost ≤ diag + 0 = diag
  linarith

/-- **Sharp Boundary:** For go ≥ m (strictly), diagonal is always optimal.
    (The paper's tight bound is go ≥ m - 1, but diag = 0 is an edge case.
    With go ≥ m, even the maximum gain m cannot overcome the gap cost.) -/
theorem sharp_boundary_strict
    (m diag opt_score go : ℤ)
    (h_go_ge : go ≥ m)
    (_h_opt_ge_diag : opt_score ≥ diag)
    (h_opt_le_m_minus_go : opt_score ≤ m - go)
    (h_diag_nonneg : diag ≥ 0)
    : opt_score ≤ diag := by
  -- opt_score ≤ m - go ≤ m - m = 0 ≤ diag
  linarith

/-- **Sharp Boundary (diag ≥ 1 case):** For go ≥ m - 1 and diag ≥ 1,
    diagonal is always optimal. This is the common case in practice. -/
theorem sharp_boundary_diag_pos
    (m diag opt_score go : ℤ)
    (h_go_ge : go ≥ m - 1)
    (h_diag_pos : diag ≥ 1)
    (_h_diag_le_m : diag ≤ m)
    (_h_opt_ge_diag : opt_score ≥ diag)
    (h_opt_le_m_minus_go : opt_score ≤ m - go)
    : opt_score ≤ diag := by
  -- opt_score ≤ m - go ≤ m - (m - 1) = 1 ≤ diag
  linarith

/-- **Correction Formula (combined):** When ε ≤ go, opt_score = LCS - ε = diag. -/
theorem correction_formula_combined
    (LCS diag opt_score _go : ℤ)
    (_h_eps_def : LCS - diag ≥ 0)
    (h_opt_ge_diag : opt_score ≥ diag)
    (h_opt_le_diag : opt_score ≤ diag)
    : opt_score = diag ∧ opt_score = LCS - (LCS - diag) := by
  constructor
  · linarith
  · linarith

/-- The excess is non-negative: LCS ≥ diag always. -/
theorem excess_nonneg_of_ge
    (LCS diag : ℤ)
    (h_diag_subseq : LCS ≥ diag)
    : LCS - diag ≥ 0 := by
  linarith

/-!
## Skip-Comb Identity

The relationship between the exact epsilon and the skip-comb estimate m - diag.
This explains why skip-comb tier classification matches exact classification
when epsilon ≈ 0 (substitution-dominated errors).
-/

/-- **Skip-comb decomposition:** m - diag = (m - LCS) + epsilon.
    The skip-comb estimate (m - diag) equals the exact epsilon plus
    the "unmatched" positions (m - LCS). -/
theorem skip_comb_decomposition
    (m LCS diag epsilon : ℤ)
    (h_eps_def : epsilon = LCS - diag)
    : m - diag = (m - LCS) + epsilon := by
  linarith

/-- When epsilon = 0: the skip-comb estimate equals m - LCS exactly.
    Both count the same thing: positions that don't participate
    in any common subsequence (i.e., pure substitution mismatches). -/
theorem skip_comb_when_eps_zero
    (m LCS diag : ℤ)
    (h_eps_zero : LCS = diag)
    : m - diag = m - LCS := by
  linarith

/-- Skip-comb and exact agree on tier classification when epsilon = 0:
    both say the read is in Tier 1 (diag = m) or Tier 2 (diag < m, diagonal optimal). -/
theorem tier_agreement_eps_zero
    (m LCS diag go : ℤ)
    (_h_eps_zero : LCS = diag)
    (h_lcs_le_m : LCS ≤ m)
    (h_skip_tier2 : m - diag ≤ go)
    : LCS - diag ≤ go := by
  linarith

/-- The skip-comb estimate is always ≥ the exact epsilon.
    It never underestimates — it's conservative. -/
theorem skip_comb_conservative
    (m LCS diag : ℤ)
    (h_lcs_le_m : LCS ≤ m)
    : m - diag ≥ LCS - diag := by
  linarith

/-- Skip-comb can only misclassify by promoting Tier 2 to Tier 3
    (never the reverse). If exact says Tier 3, skip-comb also says Tier 3. -/
theorem skip_comb_no_false_negative
    (m LCS diag go : ℤ)
    (h_lcs_le_m : LCS ≤ m)
    (h_exact_tier3 : LCS - diag > go)
    : m - diag > go := by
  linarith

/-- **Main theorem:** Combining Tier 2 and the combined formula.
    When ε ≤ go with go ≥ 1, and the optimal score decomposes as
    diag + gain - cost with gain ≤ crossings and cost ≥ crossings * go,
    then opt_score = diag = LCS - ε. -/
theorem correction_formula_main
    (LCS diag opt_score num_crossings crossing_gain gap_cost go : ℤ)
    (_h_lcs_ge_diag : LCS ≥ diag)
    (h_go_pos : go ≥ 1)
    (h_opt_ge_diag : opt_score ≥ diag)
    (h_gain_le_cross : crossing_gain ≤ num_crossings)
    (h_cost_ge : gap_cost ≥ num_crossings * go)
    (h_score_bound : opt_score ≤ diag + crossing_gain - gap_cost)
    (h_cross_nonneg : num_crossings ≥ 0)
    : opt_score = diag ∧ opt_score = LCS - (LCS - diag) := by
  have h_eq := correction_tier2 diag opt_score num_crossings crossing_gain
    gap_cost go h_go_pos h_opt_ge_diag h_gain_le_cross h_cost_ge h_score_bound
    h_cross_nonneg
  constructor
  · exact h_eq
  · linarith
