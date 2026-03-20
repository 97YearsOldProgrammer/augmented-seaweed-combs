import Mathlib.Tactic

/-!
# The affine monoid Aff(ℤ≥0)

Formalizes `Aff(ℤ≥0)`: functions `f_{a,b}(x) = a*x + b` with `a ∈ {0, 1}`,
`b ∈ ℕ`, under composition. This is the fiber monoid in the wreath product
`S_n ≀ Aff(ℤ≥0)`.

## Main results

- `AffNat` is a monoid under composition
- Composition formula: `f_{a₂,b₂} ∘ f_{a₁,b₁} = f_{a₂*a₁, a₂*b₁ + b₂}`
- The two generators are `reset := f_{0,0}` and `extend := f_{1,1}`
- Any composition of `reset` and `extend` yields slope `a ∈ {0, 1}`
-/

/-- An element of the affine monoid Aff(ℤ≥0).
    Represents the function x ↦ a * x + b where a ∈ {0, 1}. -/
structure AffNat where
  /-- Slope: 0 (reset/constant) or 1 (extend/translation) -/
  slope : Fin 2
  /-- Intercept: the constant term -/
  intercept : ℕ
  deriving DecidableEq, Repr

namespace AffNat

@[ext]
theorem ext {f g : AffNat} (hs : f.slope = g.slope) (hi : f.intercept = g.intercept) :
    f = g := by
  cases f; cases g; simp_all

/-- Apply the affine function to a value -/
def apply (f : AffNat) (x : ℕ) : ℕ := f.slope.val * x + f.intercept

/-- Compose two affine functions: (f₂ ∘ f₁)(x) = f₂(f₁(x)) -/
def comp (f₂ f₁ : AffNat) : AffNat where
  slope := ⟨f₂.slope.val * f₁.slope.val % 2,
            Nat.mod_lt _ (by omega)⟩
  intercept := f₂.slope.val * f₁.intercept + f₂.intercept

/-- The identity function f_{1,0}(x) = x -/
def id : AffNat where
  slope := ⟨1, by omega⟩
  intercept := 0

/-- The reset function f_{0,0}(x) = 0 (match resets depth) -/
def reset : AffNat where
  slope := ⟨0, by omega⟩
  intercept := 0

/-- The extend function f_{1,1}(x) = x + 1 (mismatch increments depth) -/
def extend : AffNat where
  slope := ⟨1, by omega⟩
  intercept := 1

/-- Composition is correct: comp f₂ f₁ applied = f₂ applied to f₁ applied -/
theorem comp_apply (f₂ f₁ : AffNat) (x : ℕ) :
    (comp f₂ f₁).apply x = f₂.apply (f₁.apply x) := by
  simp [comp, apply]
  have h1 : f₂.slope.val < 2 := f₂.slope.isLt
  have h2 : f₁.slope.val < 2 := f₁.slope.isLt
  interval_cases f₂.slope.val <;> interval_cases f₁.slope.val <;> simp_all <;> ring

/-- Right identity: comp f id = f -/
theorem comp_id (f : AffNat) : comp f id = f := by
  obtain ⟨⟨sv, svlt⟩, i⟩ := f
  unfold comp id
  simp
  omega

/-- Left identity: comp id f = f -/
theorem id_comp (f : AffNat) : comp id f = f := by
  obtain ⟨⟨sv, svlt⟩, i⟩ := f
  unfold comp id
  simp
  omega

/-- Composition is associative -/
theorem comp_assoc (f₃ f₂ f₁ : AffNat) :
    comp (comp f₃ f₂) f₁ = comp f₃ (comp f₂ f₁) := by
  obtain ⟨⟨s1, s1lt⟩, i1⟩ := f₁
  obtain ⟨⟨s2, s2lt⟩, i2⟩ := f₂
  obtain ⟨⟨s3, s3lt⟩, i3⟩ := f₃
  unfold comp
  simp
  refine ⟨?_, ?_⟩
  · interval_cases s1 <;> interval_cases s2 <;> interval_cases s3 <;> simp
  · interval_cases s1 <;> interval_cases s2 <;> interval_cases s3 <;> simp <;> ring

/-- Reset after anything is reset (with appropriate intercept) -/
theorem reset_comp (f : AffNat) : comp reset f = reset := by
  simp [comp, reset]

/-- Extend after reset gives a constant -/
theorem extend_comp_reset :
    comp extend reset = ⟨⟨0, by omega⟩, 1⟩ := by
  simp [comp, extend, reset]

/-- Extend composed with extend gives x + 2 -/
theorem extend_comp_extend :
    comp extend extend = ⟨⟨1, by omega⟩, 2⟩ := by
  simp [comp, extend]

/-- The slope of any composition of reset/extend is in {0, 1} -/
theorem slope_binary (f : AffNat) : f.slope.val = 0 ∨ f.slope.val = 1 := by
  have h := f.slope.isLt
  omega

end AffNat
