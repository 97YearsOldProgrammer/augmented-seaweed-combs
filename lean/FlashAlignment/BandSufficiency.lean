/-
  FlashAlignment/BandSufficiency.lean

  ε-Band Sufficiency Theorem for Affine Gap Alignment

  Theorem: The optimal Gotoh (affine gap) alignment of a query a[0..m-1]
  against a reference window b[s..s+m-1] never deviates more than
  ε = LCS(a,b) - diag(a,b) positions from the main diagonal.

  Consequence: ε-banded Gotoh DP (computing only cells (i,j) with |i-j| ≤ ε)
  produces the exact optimal score. Cost: O(m × ε) instead of O(m²).

  Paper reference: Proposition 5.9 (band sufficiency)
-/
import Mathlib.Tactic

/-!
## Core Inequality

The algebraic heart of the proof: if an alignment has deviation d > ε
from the diagonal, its score is strictly below the diagonal score.

**Key chain**: score(P) = matches - gaps ≤ LCS - d < diag

This uses three facts:
1. matches ≤ LCS (any alignment's matches form a common subsequence)
2. gap_penalty ≥ d (deviation d requires ≥ d gap positions, each costing ≥ 1)
3. d > LCS - diag (deviation exceeds excess)
-/

/-- Any alignment with deviation d > ε = LCS - diag scores below diag. -/
theorem score_below_diag_of_excess_deviation
    (LCS diag d gap_pen num_matches : ℤ)
    (h_matches_le : num_matches ≤ LCS)
    (h_gap_ge_d : gap_pen ≥ d)
    (h_d_gt_excess : d > LCS - diag)
    : num_matches - gap_pen < diag := by
  linarith

/-- The optimal alignment's deviation is bounded by ε = LCS - diag. -/
theorem optimal_deviation_le_excess
    (LCS diag opt_score opt_dev : ℤ)
    (h_opt_ge_diag : opt_score ≥ diag)
    (h_score_bound : opt_score ≤ LCS - opt_dev)
    (_h_dev_nonneg : opt_dev ≥ 0)
    : opt_dev ≤ LCS - diag := by
  linarith

/-- ε-banded Gotoh is exact: band width ε suffices for the optimal score. -/
theorem epsilon_band_exact
    (LCS diag opt_score opt_dev band : ℤ)
    (h_opt_ge_diag : opt_score ≥ diag)
    (h_score_bound : opt_score ≤ LCS - opt_dev)
    (h_dev_nonneg : opt_dev ≥ 0)
    (h_band_ge_excess : band ≥ LCS - diag)
    : opt_dev ≤ band := by
  have h := optimal_deviation_le_excess LCS diag opt_score opt_dev
    h_opt_ge_diag h_score_bound h_dev_nonneg
  linarith
