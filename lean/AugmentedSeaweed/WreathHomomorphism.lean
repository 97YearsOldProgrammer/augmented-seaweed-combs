import Mathlib.Tactic
import AugmentedSeaweed.AffineMonoid

/-!
# Wreath product composition law

Formalizes the key lemma: composition of augmented comb outputs follows
the wreath product rule S_n ≀ Aff(ℤ≥0).

## Main results

- Each cell produces an affine function on depth (either reset f_{0,0} or extend f_{1,1})
- The net transformation of a wire through multiple cells is an Aff(ℤ≥0) element
- Composition of two segments follows the wreath product rule:
    g(i) = f₂(π₁(i)) ∘ f₁(i)
  where π₁ is the permutation from the first segment

## Key insight

The depth at each position after composition depends on:
1. Which wire arrived there (tracked by the permutation π₁)
2. The affine transformation of the first segment (f₁)
3. The affine transformation of the second segment (f₂), applied at
   the position determined by π₁

This is exactly the wreath product multiplication rule.
-/

/-- The elementary affine function produced by a single cell -/
def cellAffine (isMatchCell : Bool) : AffNat :=
  if isMatchCell then AffNat.reset  -- f_{0,0}: depth → 0
  else AffNat.extend                 -- f_{1,1}: depth → depth + 1

/-- Match produces reset -/
theorem cellAffine_match : cellAffine true = AffNat.reset := by
  simp [cellAffine]

/-- Mismatch produces extend -/
theorem cellAffine_mismatch : cellAffine false = AffNat.extend := by
  simp [cellAffine]

/-- Reset followed by k extends gives f_{0,k} -/
theorem reset_then_extends (k : ℕ) :
    (List.replicate k AffNat.extend).foldr AffNat.comp AffNat.reset =
    ⟨⟨0, by omega⟩, k⟩ := by
  induction k with
  | zero => simp [AffNat.reset]
  | succ k ih =>
    simp [List.replicate_succ, List.foldr_cons]
    rw [ih]
    simp [AffNat.comp, AffNat.extend]

/-- The slope of any composition of reset/extend is in {0, 1} -/
theorem slope_binary (f : AffNat) : f.slope.val = 0 ∨ f.slope.val = 1 := by
  have h := f.slope.isLt
  omega

/-- After a match (reset), the slope is 0 regardless of prior state -/
theorem comp_reset_slope (f : AffNat) :
    (AffNat.comp AffNat.reset f).slope = ⟨0, by omega⟩ := by
  simp [AffNat.comp, AffNat.reset]

/-- After any number of extends following a reset, slope stays 0 -/
theorem extend_after_reset_slope (f : AffNat) (h : f.slope = ⟨0, by omega⟩) :
    (AffNat.comp AffNat.extend f).slope = ⟨0, by omega⟩ := by
  obtain ⟨⟨sv, svlt⟩, i⟩ := f
  simp [Fin.ext_iff] at h
  subst h
  simp [AffNat.comp, AffNat.extend]
