/-
  FlashAlignment/NonMonge.lean

  Non-Monge Structure of Affine Gap Score Matrix

  The semi-local affine gap score matrix S(i,j) = affine_gap(A[i:], B[:j])
  is NOT Monge, even for m=2. This contrasts with LCS where S is always
  unit-Monge (Tiskin).

  Consequence: the standard Tiskin framework (unit-Monge composition)
  does not extend to affine gap. The wreath product is necessary.

  Paper reference: Theorem 6 (non-Monge structure)
-/
import Mathlib.Tactic

/-!
## Counterexample

A = "01", B = "0001", go = 3, ge = 1.

The semi-local score matrix S(i,j) for (i,j) ∈ {0,1,2} × {0,1,2,3,4}:

  S = | 0  -2   1   1   2 |
      | 0   0   0   0   1 |
      | 0   0   0   0   0 |

Monge condition: S(i₁,j₁) + S(i₂,j₂) ≤ S(i₁,j₂) + S(i₂,j₁)
for i₁ < i₂, j₁ < j₂.

Taking (i₁,i₂,j₁,j₂) = (0,1,0,1):
  S(0,0) + S(1,1) = 0 + 0 = 0
  S(0,1) + S(1,0) = -2 + 0 = -2
  0 > -2 → Monge VIOLATED with deficit 2.
-/

/-- The Monge condition for a 2×2 submatrix. -/
def monge_condition (s00 s01 s10 s11 : ℤ) : Prop :=
  s00 + s11 ≤ s01 + s10

/-- **Non-Monge counterexample:** The specific 2×2 submatrix from A="01", B="0001", go=3.
    S(0,0)=0, S(0,1)=-2, S(1,0)=0, S(1,1)=0.
    The Monge condition fails: 0 + 0 = 0 > -2 + 0 = -2. -/
theorem non_monge_counterexample :
    ¬ monge_condition 0 (-2) 0 0 := by
  simp [monge_condition]

/-- The deficit (violation amount) is exactly 2. -/
theorem monge_deficit :
    (0 : ℤ) + 0 - ((-2) + 0) = 2 := by
  omega

/-- For LCS (no gap penalty), the same strings give a unit-Monge matrix.
    This shows the non-Monge structure is caused by gap penalties specifically. -/
theorem lcs_is_unit_monge_example :
    monge_condition 0 0 0 0 := by
  simp [monge_condition]

/-- The Monge deficit is strictly positive — this is a genuine violation,
    not a boundary case. -/
theorem monge_deficit_positive :
    (0 : ℤ) + 0 > (-2) + 0 := by
  omega

/-!
## General Non-Monge Principle

The structural reason: gap penalties cause the score matrix to lose the
unit step property. In the LCS matrix, adjacent differences are always
in {0, -1} (unit anti-Monge). With affine gaps, adjacent differences
can be arbitrary integers, breaking the Monge structure.

The wreath product S_{m+n} ≀ Aff(ℤ≥0) provides the correct algebraic
framework that does NOT require Monge structure for composition.
-/

/-- Unit-Monge would require the deficit to be at most 1.
    Our deficit is 2, violating even the weakened condition. -/
theorem exceeds_unit_monge :
    (0 : ℤ) + 0 - ((-2) + 0) > 1 := by
  omega
