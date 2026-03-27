/-
  FlashAlignment/WreathComposition.lean

  Wreath Product Composition Law for Augmented Seaweed Combs

  The augmented comb for A = A1·A2 against B decomposes as:
    (π, g) = (π₂ ∘ π₁, λ i → f₂(π₁(i)) ∘ f₁(i))

  where (π₁, f₁) is the augmented comb for A1 vs B and
  (π₂, f₂) is the augmented comb for A2 vs B (with boundary state from A1).

  This is the standard wreath product multiplication rule for
  S_N ≀ Aff(ℤ≥0), and it holds because:
  1. Permutations compose (standard Krusche composition)
  2. Depth is a pure observer — it rides along with its wire
  3. After segment 1, wire i is at position π₁(i)
  4. Segment 2 applies f₂ at the position it sees the wire: π₁(i)
  5. Total depth = f₂(π₁(i)) ∘ f₁(i)

  Paper reference: Theorem 3 (Wreath product homomorphism)
-/
import Mathlib.Tactic
import AugmentedSeaweed.AffineMonoid

/-!
## Wreath Product Element

A labeled permutation: a permutation π on [N] together with
an affine function f(i) ∈ Aff(ℤ≥0) for each wire i.
-/

/-- A wreath product element (π, f) ∈ S_N ≀ Aff(ℤ≥0).
    π is a permutation (modeled as a function Fin N → Fin N)
    and f assigns an AffNat to each wire position. -/
structure WreathElem (N : ℕ) where
  /-- The permutation component -/
  perm : Fin N → Fin N
  /-- The fiber (depth transformation) at each wire position -/
  fiber : Fin N → AffNat
  deriving Repr

namespace WreathElem

/-- Wreath product multiplication:
    (π₂, f₂) · (π₁, f₁) = (π₂ ∘ π₁, λ i → f₂(π₁(i)) ∘ f₁(i))

    Wire i's journey:
    1. Segment 1 moves it from i to π₁(i), applying f₁(i)
    2. Segment 2 sees it at π₁(i), applies f₂(π₁(i))
    Total depth transformation: f₂(π₁(i)) composed with f₁(i) -/
def mul {N : ℕ} (w₂ w₁ : WreathElem N) : WreathElem N where
  perm := w₂.perm ∘ w₁.perm
  fiber := fun i => AffNat.comp (w₂.fiber (w₁.perm i)) (w₁.fiber i)

/-- The identity wreath element: identity permutation, identity fiber. -/
def one (N : ℕ) : WreathElem N where
  perm := id
  fiber := fun _ => AffNat.id

/-- Right identity: w · 1 = w -/
theorem mul_one {N : ℕ} (w : WreathElem N) :
    mul w (one N) = w := by
  cases w with | mk p f =>
  simp only [mul, one, Function.comp_id]
  congr 1
  funext i
  exact AffNat.comp_id (f i)

/-- Left identity: 1 · w = w -/
theorem one_mul {N : ℕ} (w : WreathElem N) :
    mul (one N) w = w := by
  cases w with | mk p f =>
  simp only [mul, one, Function.id_comp]
  congr 1
  funext i
  exact AffNat.id_comp (f i)

/-- Associativity: (w₃ · w₂) · w₁ = w₃ · (w₂ · w₁)

    This is the KEY structural property: composing three segments
    in any grouping gives the same result. -/
theorem mul_assoc {N : ℕ} (w₃ w₂ w₁ : WreathElem N) :
    mul (mul w₃ w₂) w₁ = mul w₃ (mul w₂ w₁) := by
  simp [mul, Function.comp_assoc, AffNat.comp_assoc]

/-!
## Fiber Composition Properties

Key facts about how depth transformations compose through the wreath product.
-/

/-- The fiber at position i after composition is f₂ at π₁(i) composed with f₁ at i.
    This is definitional but worth stating explicitly. -/
theorem fiber_comp {N : ℕ} (w₂ w₁ : WreathElem N) (i : Fin N) :
    (mul w₂ w₁).fiber i = AffNat.comp (w₂.fiber (w₁.perm i)) (w₁.fiber i) := by
  rfl

/-- The permutation after composition is π₂ ∘ π₁. -/
theorem perm_comp {N : ℕ} (w₂ w₁ : WreathElem N) (i : Fin N) :
    (mul w₂ w₁).perm i = w₂.perm (w₁.perm i) := by
  rfl

/-- After composition, applying the combined fiber to an initial depth x gives
    f₂(π₁(i)) applied to (f₁(i) applied to x). -/
theorem fiber_apply_comp {N : ℕ} (w₂ w₁ : WreathElem N) (i : Fin N) (x : ℕ) :
    ((mul w₂ w₁).fiber i).apply x =
    (w₂.fiber (w₁.perm i)).apply ((w₁.fiber i).apply x) := by
  simp [fiber_comp, AffNat.comp_apply]

/-!
## Connection to Augmented Comb

The augmented comb for a single character c against reference B
produces a wreath product element where:
- perm = the label permutation from the Krusche comb
- fiber(i) = reset (f_{0,0}) if c matched at position i,
             extend (f_{1,1}) if c mismatched at position i

Composing character-by-character via `mul` reproduces the full comb.
The observer property (Observer.lean) guarantees that the fiber
does not affect the permutation, so `perm` is identical to the
standard (non-augmented) Krusche comb permutation.
-/

/-- A single-character wreath element: each position gets reset or extend. -/
def singleChar {N : ℕ} (charPerm : Fin N → Fin N)
    (matched : Fin N → Bool) : WreathElem N where
  perm := charPerm
  fiber := fun i => if matched i then AffNat.reset else AffNat.extend

/-- For a match position, the fiber is reset (depth → 0). -/
theorem singleChar_match {N : ℕ} (p : Fin N → Fin N) (m : Fin N → Bool)
    (i : Fin N) (h : m i = true) :
    (singleChar p m).fiber i = AffNat.reset := by
  simp [singleChar, h]

/-- For a mismatch position, the fiber is extend (depth → depth + 1). -/
theorem singleChar_mismatch {N : ℕ} (p : Fin N → Fin N) (m : Fin N → Bool)
    (i : Fin N) (h : m i = false) :
    (singleChar p m).fiber i = AffNat.extend := by
  simp [singleChar, h]

/-- Composing two single-character wreath elements follows the wreath product rule.
    This is the inductive step: processing character c₂ after c₁. -/
theorem compose_two_chars {N : ℕ}
    (p₁ p₂ : Fin N → Fin N)
    (m₁ m₂ : Fin N → Bool) :
    mul (singleChar p₂ m₂) (singleChar p₁ m₁) =
    { perm := p₂ ∘ p₁,
      fiber := fun i => AffNat.comp
        (if m₂ (p₁ i) then AffNat.reset else AffNat.extend)
        (if m₁ i then AffNat.reset else AffNat.extend) } := by
  simp [mul, singleChar]

/-- Composing reset then k extends directly: net is f_{0,k}. -/
theorem reset_then_k_extends (k : ℕ) :
    AffNat.comp ⟨⟨1, by omega⟩, k⟩ AffNat.reset = ⟨⟨0, by omega⟩, k⟩ := by
  simp [AffNat.comp, AffNat.reset]

/-- k extends composed: net is f_{1,k}. -/
theorem k_extends_comp (k : ℕ) :
    AffNat.comp ⟨⟨1, by omega⟩, k⟩ AffNat.extend = ⟨⟨1, by omega⟩, k + 1⟩ := by
  simp [AffNat.comp, AffNat.extend]; omega

/-- Match then mismatch: reset ∘ extend = f_{0,1}. -/
theorem extend_then_reset :
    AffNat.comp AffNat.reset AffNat.extend = ⟨⟨0, by omega⟩, 0⟩ := by
  simp [AffNat.comp, AffNat.reset, AffNat.extend]

/-- Mismatch then match: extend ∘ reset = f_{0,1}. -/
theorem reset_then_extend :
    AffNat.comp AffNat.extend AffNat.reset = ⟨⟨0, by omega⟩, 1⟩ := by
  simp [AffNat.comp, AffNat.extend, AffNat.reset]

end WreathElem
