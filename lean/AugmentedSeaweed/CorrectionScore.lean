import Mathlib.Tactic

/-!
# Correction Score: Algebraic Characterization

Formalizes the correction scoring function from augmented seaweed comb theory:

  correction(LCS, diag, go) = LCS - min(LCS - diag, go) = max(LCS - go, diag)

This is a tropical max of two quantities: the diagonal match score and the
LCS score with a fixed gap-cap penalty. It defines a scoring function strictly
between LCS and diagonal matching — a bounded gap-count regularizer.

## Tropical interpretation

In tropical (max-plus) algebra, the correction score is the application of
a tropical carry element (T = diag, K = -go) to LCS:

  f(x) = max(T, x + K)

This connects to the `TropCarry` monoid in `TropicalCarry.lean`.

## Main results

- `correction_tropical_max`: equivalence of subtraction and max forms
- `correction_sandwich`: diag ≤ correction ≤ LCS
- `correction_mono_go`: monotone decreasing in go
- `correction_at_zero`: go = 0 recovers LCS
- `correction_saturates`: go ≥ excess recovers diag

## Application

For splice junction detection, the correction formula at go ≈ 5 outperforms
both LCS (+7.9pp) and Gotoh DP. The bounded cap preserves the LCS curve
shape while penalizing gap-inflated false peaks.
-/

/-- The excess: number of gap-dependent matches in the LCS alignment.
    excess = LCS - diag, where diag counts diagonal (gapless) matches.
    Excess measures how many LCS matches required a gap (off-diagonal). -/
def excess (LCS diag : ℤ) : ℤ := LCS - diag

/-- Excess is non-negative when diag ≤ LCS. -/
theorem excess_nonneg (LCS diag : ℤ) (h : diag ≤ LCS) : 0 ≤ excess LCS diag := by
  simp only [excess]; omega

/-- The correction score: LCS penalized by bounded gap count.
    correction(LCS, diag, go) = LCS - min(excess, go).
    Caps the gap penalty at `go`, penalizing gap-dependent matches
    but never more than `go` per alignment half. -/
def correctionScore (LCS diag go : ℤ) : ℤ := LCS - min (excess LCS diag) go

/-! ## Equivalence of forms -/

/-- **Tropical max form**: the correction score equals max(LCS - go, diag).
    This reveals the scoring function as a tropical max of two quantities:
    the capped LCS score and the diagonal score. -/
theorem correction_tropical_max (LCS diag go : ℤ)
    (h_le : diag ≤ LCS) (h_go : 0 ≤ go) :
    correctionScore LCS diag go = max (LCS - go) diag := by
  simp only [correctionScore, excess, min_def, max_def]
  split <;> split <;> omega

/-! ## Ordering -/

/-- **Lower bound**: the correction score is at least the diagonal score. -/
theorem diag_le_correction (LCS diag go : ℤ)
    (h_le : diag ≤ LCS) (h_go : 0 ≤ go) :
    diag ≤ correctionScore LCS diag go := by
  rw [correction_tropical_max LCS diag go h_le h_go]
  exact le_max_right _ _

/-- **Upper bound**: the correction score never exceeds LCS. -/
theorem correction_le_LCS (LCS diag go : ℤ)
    (h_le : diag ≤ LCS) (h_go : 0 ≤ go) :
    correctionScore LCS diag go ≤ LCS := by
  simp only [correctionScore, excess, min_def]
  split <;> omega

/-- **Sandwich**: diag ≤ correction ≤ LCS. -/
theorem correction_sandwich (LCS diag go : ℤ)
    (h_le : diag ≤ LCS) (h_go : 0 ≤ go) :
    diag ≤ correctionScore LCS diag go ∧ correctionScore LCS diag go ≤ LCS :=
  ⟨diag_le_correction LCS diag go h_le h_go,
   correction_le_LCS LCS diag go h_le h_go⟩

/-! ## Monotonicity -/

/-- **Monotone decreasing in go**: increasing the gap cap decreases the score.
    Higher go penalizes more gap-dependent matches, lowering the score. -/
theorem correction_mono_go (LCS diag go₁ go₂ : ℤ) (h : go₁ ≤ go₂) :
    correctionScore LCS diag go₂ ≤ correctionScore LCS diag go₁ := by
  simp only [correctionScore, excess, min_def]
  split <;> split <;> omega

/-! ## Boundary values -/

/-- **Zero gap cap**: with go = 0, the correction score equals LCS.
    No penalty is applied; the scoring function reduces to standard LCS. -/
theorem correction_at_zero (LCS diag : ℤ) (h_le : diag ≤ LCS) :
    correctionScore LCS diag 0 = LCS := by
  simp only [correctionScore, excess, min_def]
  split <;> omega

/-- **Saturation**: when go ≥ excess, the correction score equals diag.
    Full correction removes all gap-dependent matches, leaving only
    gapless diagonal matches. -/
theorem correction_saturates (LCS diag go : ℤ)
    (h_le : diag ≤ LCS) (h_go : go ≥ excess LCS diag) :
    correctionScore LCS diag go = diag := by
  simp only [correctionScore, excess] at *
  simp only [min_def]
  split <;> omega

/-- **Exact threshold**: at go = excess, correction = diag. -/
theorem correction_at_excess (LCS diag : ℤ) (h_le : diag ≤ LCS) :
    correctionScore LCS diag (excess LCS diag) = diag :=
  correction_saturates LCS diag (excess LCS diag) h_le le_rfl

/-! ## Strict interpolation -/

/-- **Strict lower bound**: if go < excess, correction > diag.
    The correction score is strictly above diag when the gap cap
    does not fully penalize all excess. -/
theorem correction_gt_diag (LCS diag go : ℤ)
    (h_le : diag ≤ LCS) (h_go : 0 ≤ go)
    (h_lt : go < excess LCS diag) :
    correctionScore LCS diag go > diag := by
  simp only [correctionScore, excess] at *
  simp only [min_def]
  split <;> omega

/-- **Strict upper bound**: if go > 0 and excess > 0, correction < LCS.
    Any positive gap penalty applied to a gapped alignment reduces score. -/
theorem correction_lt_LCS (LCS diag go : ℤ)
    (h_le : diag ≤ LCS) (h_go : 0 < go)
    (h_ex : 0 < excess LCS diag) :
    correctionScore LCS diag go < LCS := by
  simp only [correctionScore, excess] at *
  simp only [min_def]
  split <;> omega
