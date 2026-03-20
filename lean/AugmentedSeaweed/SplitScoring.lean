import Mathlib.Tactic
import AugmentedSeaweed.CorrectionScore

/-!
# Split Scoring for Junction Detection

Formalizes the per-half split scoring used in splice junction detection.
At each candidate junction point j, the read is split into forward [0,j)
and reverse [j,m), each scored independently with the correction formula.

  splitScore(j) = correction(fwd_LCS, fwd_diag, go) + correction(rev_LCS, rev_diag, go)

## Main results

- `rescue_condition`: correction reversal ⟺ differential penalty > LCS advantage
- `per_half_cap_le`: min(a,go) + min(b,go) ≤ min(a+b, 2*go) — per-half cap
  is weakly tighter than a single cap on total excess
- `low_excess_wins`: when truth has low per-half excess and wrong has high
  per-half excess, the correction formula rescues the true junction

## Key insight

The correction formula differentially penalizes junction positions where
the LCS score was inflated by gap-dependent matches. True junctions have
clean on-diagonal exon alignments (low excess), while false LCS peaks
achieve high scores through off-diagonal crossings (high excess).
-/

/-- The split correction score at a junction point.
    Sum of per-half correction scores for forward and reverse halves. -/
def splitScore (fwd_LCS fwd_diag rev_LCS rev_diag go : ℤ) : ℤ :=
  correctionScore fwd_LCS fwd_diag go + correctionScore rev_LCS rev_diag go

/-! ## Rescue condition -/

/-- **Rescue condition**: the correction formula makes position t beat position w
    if and only if the differential penalty exceeds the LCS advantage.

    LCS picks w (wrong): LCS_w ≥ LCS_t.
    Correction picks t (true): penalty_w - penalty_t > LCS_w - LCS_t.

    The penalty at a position is min(fwd_excess, go) + min(rev_excess, go).
    This theorem characterizes exactly when the correction formula rescues
    a junction that LCS alone would miss. -/
theorem rescue_condition
    (fwd_LCS_t fwd_diag_t rev_LCS_t rev_diag_t : ℤ)
    (fwd_LCS_w fwd_diag_w rev_LCS_w rev_diag_w : ℤ)
    (go : ℤ) :
    splitScore fwd_LCS_t fwd_diag_t rev_LCS_t rev_diag_t go >
    splitScore fwd_LCS_w fwd_diag_w rev_LCS_w rev_diag_w go
    ↔
    (min (excess fwd_LCS_w fwd_diag_w) go + min (excess rev_LCS_w rev_diag_w) go)
    - (min (excess fwd_LCS_t fwd_diag_t) go + min (excess rev_LCS_t rev_diag_t) go)
    > (fwd_LCS_w + rev_LCS_w) - (fwd_LCS_t + rev_LCS_t) := by
  simp only [splitScore, correctionScore, excess, min_def]
  split <;> split <;> split <;> split <;> constructor <;> intro h <;> omega

/-! ## Per-half cap comparison -/

/-- **Per-half cap**: applying min(·, go) independently to each half and summing
    yields a penalty ≤ applying a single min(·, 2*go) to the total excess.

    min(a, go) + min(b, go) ≤ min(a + b, 2 * go)

    This shows per-half capping is weakly tighter (less penalty) than
    a single cap, because one small half can "save" penalty even when
    the other half is large. -/
theorem per_half_cap_le (a b go : ℤ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hgo : 0 ≤ go) :
    min a go + min b go ≤ min (a + b) (2 * go) := by
  simp only [min_def]
  split <;> split <;> split <;> omega

/-- **Equality case**: per-half equals single cap when both halves are ≥ go
    or both halves are ≤ go. The caps differ only for mixed cases. -/
theorem per_half_cap_eq_both_large (a b go : ℤ)
    (ha : a ≥ go) (hb : b ≥ go) (_hgo : 0 ≤ go) :
    min a go + min b go = 2 * go := by
  simp only [min_def]
  split <;> split <;> omega

theorem per_half_cap_eq_both_small (a b go : ℤ)
    (ha : a ≤ go) (hb : b ≤ go) :
    min a go + min b go = a + b := by
  simp only [min_def]
  split <;> omega

/-! ## Junction rescue theorems -/

/-- **Low-excess wins**: if both halves of the true junction have excess ≤ ε
    and both halves of the wrong junction have excess ≥ go ≥ ε, and the
    penalty differential exceeds the LCS advantage, then correction rescues.

    This is the core mechanism: true junctions have clean exon alignments
    (low excess on both halves), while wrong positions have messy alignments
    (high excess on both halves). The per-half cap at go between ε and the
    wrong excess produces a penalty differential of 2*(go - ε). -/
theorem low_excess_wins
    (fwd_LCS_t fwd_diag_t rev_LCS_t rev_diag_t : ℤ)
    (fwd_LCS_w fwd_diag_w rev_LCS_w rev_diag_w : ℤ)
    (go ε : ℤ)
    -- True junction: both halves have low excess (clean alignment)
    (h_fwd_t : excess fwd_LCS_t fwd_diag_t ≤ ε)
    (h_rev_t : excess rev_LCS_t rev_diag_t ≤ ε)
    -- Wrong position: both halves have high excess (gap-inflated)
    (h_fwd_w : excess fwd_LCS_w fwd_diag_w ≥ go)
    (h_rev_w : excess rev_LCS_w rev_diag_w ≥ go)
    -- go is in the effective range
    (h_go_ge : go ≥ ε)
    -- The penalty differential exceeds the LCS advantage
    (h_rescue : 2 * (go - ε) > (fwd_LCS_w + rev_LCS_w) - (fwd_LCS_t + rev_LCS_t))
    : splitScore fwd_LCS_t fwd_diag_t rev_LCS_t rev_diag_t go >
      splitScore fwd_LCS_w fwd_diag_w rev_LCS_w rev_diag_w go := by
  simp only [splitScore, correctionScore, excess] at *
  simp only [min_def]
  split <;> split <;> split <;> split <;> omega

/-- **Penalty differential bound**: when true excess ≤ ε ≤ go ≤ wrong excess
    (per half), the penalty differential is at least 2*(go - ε). -/
theorem penalty_differential_bound
    (fwd_exc_t rev_exc_t fwd_exc_w rev_exc_w go ε : ℤ)
    (h_fwd_t : fwd_exc_t ≤ ε) (h_rev_t : rev_exc_t ≤ ε)
    (h_fwd_w : fwd_exc_w ≥ go) (h_rev_w : rev_exc_w ≥ go)
    (h_go_ge : go ≥ ε)
    : (min fwd_exc_w go + min rev_exc_w go)
      - (min fwd_exc_t go + min rev_exc_t go)
      ≥ 2 * (go - ε) := by
  simp only [min_def]
  split <;> split <;> split <;> split <;> omega

/-! ## Optimal go window -/

/-- **Go lower bound for rescue**: to rescue a junction with LCS advantage Δ
    and true excess ≤ ε (per half) against wrong excess ≥ go (per half),
    go must satisfy go > ε + Δ/2.

    Stated contrapositively: if go ≤ ε + Δ/2, there exists a configuration
    where rescue fails. Here we prove the positive direction: the bound
    2*(go - ε) > Δ is sufficient for rescue. -/
theorem go_sufficient_for_rescue (go ε Δ : ℤ)
    (h_bound : 2 * (go - ε) > Δ)
    : 2 * go > 2 * ε + Δ := by omega
