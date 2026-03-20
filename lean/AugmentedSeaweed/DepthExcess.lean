import Mathlib.Tactic
import AugmentedSeaweed.CorrectionScore
import AugmentedSeaweed.AffineMonoid
import AugmentedSeaweed.Observer
import AugmentedSeaweed.WreathHomomorphism

/-!
# Depth-Excess Bridge

Connects the augmented seaweed comb's depth values to the correction
score's excess term.

## Band-correction connection

The excess in the correction formula is the same ε as in the band
sufficiency theorem: both equal LCS - diag. This means the correction
score penalizes by the clamped *minimum band width* of the optimal alignment:

  correction = LCS - min(go, ε_band)

Two independently motivated quantities coincide:
- ε_band bounds alignment deviation (algorithmic efficiency, BandSufficiency)
- excess measures gap-dependent matches (scoring accuracy, CorrectionScore)

## Depth signals alignment quality

At each cell, the augmented comb tracks gap depth via Aff(ℤ≥0):
- **Match → reset**: depth = 0 (clean, on-diagonal alignment signal)
- **Mismatch → extend**: depth ≥ 1 (gap accumulation signal)

The depth at the boundary encodes "mismatches since last match" for
each wire. Low boundary depths indicate clean alignment; high depths
indicate gap-dependent scoring.

## Open question

Can excess(p) = LCS(p) - diag(p) at a specific window position p be
extracted from the augmented comb's (d_col, depth_col) output alone?
If yes, the correction score is fully computable from the wreath
product output — the augmented comb natively provides better-than-LCS
scoring without a separate Hamming count.

Computational evidence (YASIM pombe, 1083 reads): the correction
formula at go=5 improves junction detection by +7.9pp over LCS,
suggesting the depth information the augmented comb carries IS the
missing ingredient.
-/

/-! ## Band-correction connection -/

/-- The correction score equals LCS minus the clamped band width.
    This bridges CorrectionScore (accuracy) with BandSufficiency (efficiency):
    the same ε appears in both contexts.

    Note: we reverse the min arguments to match the band sufficiency
    convention where ε = excess = LCS - diag. -/
theorem band_correction_connection (LCS diag go : ℤ)
    (_h_le : diag ≤ LCS) (_h_go : 0 ≤ go) :
    correctionScore LCS diag go = LCS - min go (excess LCS diag) := by
  simp only [correctionScore, excess, min_comm]

/-- The correction score at go = ε (the band width) equals diag.
    When the cap exactly matches the band width, the correction fully
    deducts the gap-dependent matches and recovers the diagonal score.
    This is the "exact band" operating point. -/
theorem correction_at_band_width (LCS diag : ℤ) (h_le : diag ≤ LCS) :
    correctionScore LCS diag (excess LCS diag) = diag :=
  correction_at_excess LCS diag h_le

/-! ## Depth at single cells -/

/-- After a match cell, both column and row depths reset to 0.
    This is the "clean alignment" signal in the augmented comb. -/
theorem match_depth_zero (s : CellState) :
    (augmentedCellUpdate true s).colDepth = 0 ∧
    (augmentedCellUpdate true s).rowDepth = 0 := by
  simp [augmentedCellUpdate]

/-- After a mismatch cell, both depths are at least 1.
    Non-zero depth signals gap accumulation. -/
theorem mismatch_depth_pos (s : CellState) :
    (augmentedCellUpdate false s).colDepth ≥ 1 ∧
    (augmentedCellUpdate false s).rowDepth ≥ 1 := by
  constructor
  · simp [augmentedCellUpdate]; split <;> dsimp <;> omega
  · simp [augmentedCellUpdate]; split <;> dsimp <;> omega

/-- **Depth-zero characterizes match**: at a single cell, the output
    column depth is 0 if and only if the cell was a match.
    This is the atomic detection criterion. -/
theorem cell_col_depth_zero_iff_match (isMatchCell : Bool) (s : CellState) :
    (augmentedCellUpdate isMatchCell s).colDepth = 0 ↔ isMatchCell = true := by
  constructor
  · intro h
    by_contra hmm
    have : isMatchCell = false := by
      cases isMatchCell <;> simp_all
    subst this
    have ⟨hge, _⟩ := mismatch_depth_pos s
    omega
  · intro h
    subst h
    exact (match_depth_zero s).1

/-- Same characterization for row depth. -/
theorem cell_row_depth_zero_iff_match (isMatchCell : Bool) (s : CellState) :
    (augmentedCellUpdate isMatchCell s).rowDepth = 0 ↔ isMatchCell = true := by
  constructor
  · intro h
    by_contra hmm
    have : isMatchCell = false := by
      cases isMatchCell <;> simp_all
    subst this
    have ⟨_, hge⟩ := mismatch_depth_pos s
    omega
  · intro h
    subst h
    exact (match_depth_zero s).2

/-! ## Affine function and depth -/

/-- The depth of a wire after composing affine functions equals
    the intercept when starting from initial depth 0.
    This is the fundamental link between the algebraic (AffNat)
    and the concrete (depth value) representations. -/
theorem depth_eq_affine_intercept (f : AffNat) :
    f.apply 0 = f.intercept := by
  simp [AffNat.apply]

/-- The cell affine function for a match is reset (slope 0, intercept 0). -/
theorem cell_match_is_reset :
    cellAffine true = AffNat.reset := cellAffine_match

/-- The cell affine function for a mismatch is extend (slope 1, intercept 1). -/
theorem cell_mismatch_is_extend :
    cellAffine false = AffNat.extend := cellAffine_mismatch

/-- After composing with a reset (match), the resulting depth
    depends only on subsequent extends, not on prior history.
    This is why match resets depth: the slope becomes 0. -/
theorem depth_after_reset_then_extends (k : ℕ) :
    ((List.replicate k AffNat.extend).foldr AffNat.comp AffNat.reset).apply 0 = k := by
  rw [reset_then_extends]
  simp [AffNat.apply]

/-! ## Depth monotonicity along wire paths -/

/-- A wire that encounters only mismatches (extends) has depth equal
    to the number of cells it passed through. This is the maximum
    possible depth for a given path length. -/
theorem pure_extend_depth (k : ℕ) :
    ((List.replicate k AffNat.extend).foldr AffNat.comp AffNat.id).apply 0 = k := by
  induction k with
  | zero => simp [AffNat.id, AffNat.apply]
  | succ k ih =>
    simp only [List.replicate_succ, List.foldr_cons]
    rw [AffNat.comp_apply, ih]
    simp [AffNat.extend, AffNat.apply]

/-- A wire that had at least one match (slope = 0) has depth equal
    to its intercept, which counts mismatches since the last match.
    This is strictly less than total cells traversed when at least
    one match occurred before the final stretch of mismatches. -/
theorem matched_wire_depth (f : AffNat)
    (_h_matched : f.slope = ⟨0, by omega⟩) :
    f.apply 0 = f.intercept := depth_eq_affine_intercept f

/-! ## The depth-excess conjecture

### Statement

For a seaweed comb on strings a[0..m-1] and b[0..n-1], let p be
the optimal alignment position (maximizing LCS(a, b[p..p+m-1])).

**Conjecture**: there exists a function Φ of the depth_col values
at the boundary such that:

  Φ(depth_col, p) = excess(p) = LCS(p) - diag(p)

where diag(p) = #{i : a[i] = b[p+i]} is the diagonal match count.

### What we know

1. LCS(p) is extractable from d_col via the count transform (Krusche).
2. diag(p) is an O(m) Hamming count, currently computed separately.
3. depth_col[j] = (composed affine function for wire j).intercept
   = mismatches since last match on wire j.
4. At the true junction, excess is low (clean diagonal alignment).
   At false peaks, excess is high (gap-inflated LCS).
5. The correction score max(LCS - go, diag) = LCS - min(go, excess)
   uses excess as a bounded penalty.

### What would resolve it

Show that for the optimal alignment at position p:
  Σ_{i ∈ matched_wires(p)} depth_col[π(i)] or some weighted variant
  equals or bounds excess(p) from above.

This would mean the augmented comb's wreath product output
(permutation + depth) encodes BOTH the LCS score AND the quality
of that score (how gap-dependent it is), without any separate
Hamming computation.
-/
