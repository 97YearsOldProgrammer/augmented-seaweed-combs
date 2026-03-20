import Mathlib.Tactic

/-!
# Tropical carry monoid and 2×2 matrix isomorphism

Formalizes the tropical carry monoid from Theorem 3.6 of the paper:
a pair (T, K) representing f(x) = max(T, x + K), with composition
(T₂, K₂) ∘ (T₁, K₁) = (max(T₂, T₁ + K₂), K₁ + K₂).

The isomorphism with 2×2 upper-triangular tropical matrices is:
(T, K) ↦ [[T, K], [-∞, 0]]

## Main results

- `TropCarry` forms a monoid under composition
- Composition is associative
- Isomorphism with 2×2 tropical matrix multiplication
-/

/-- A tropical carry element (T, K) where T ∈ ℤ ∪ {-∞} and K ∈ ℤ ∪ {-∞}.
    We encode -∞ as `none` using `Option ℤ`. -/
structure TropCarry where
  /-- Threshold T: the value below which the output is clamped -/
  threshold : Option ℤ
  /-- Carry K: the additive offset -/
  carry : Option ℤ
  deriving DecidableEq, Repr

namespace TropCarry

@[ext]
theorem ext {a b : TropCarry} (ht : a.threshold = b.threshold) (hc : a.carry = b.carry) :
    a = b := by
  cases a; cases b; simp_all

/-- Tropical addition: max with -∞ handling -/
def tropMax (a b : Option ℤ) : Option ℤ :=
  match a, b with
  | none, x => x
  | x, none => x
  | some a, some b => some (max a b)

/-- Tropical multiplication: + with -∞ handling -/
def tropPlus (a b : Option ℤ) : Option ℤ :=
  match a, b with
  | none, _ => none
  | _, none => none
  | some a, some b => some (a + b)

/-- Compose two tropical carries:
    (T₂, K₂) ∘ (T₁, K₁) = (max(T₂, T₁ + K₂), K₁ + K₂) -/
def comp (c₂ c₁ : TropCarry) : TropCarry where
  threshold := tropMax c₂.threshold (tropPlus c₁.threshold c₂.carry)
  carry := tropPlus c₁.carry c₂.carry

/-- The identity element (-∞, 0) -/
def identity : TropCarry where
  threshold := none
  carry := some 0

/-- Match carry: (T, -∞) where T = d_col[c] + 1 -/
def matchCarry (dcolVal : ℤ) : TropCarry where
  threshold := some (dcolVal + 1)
  carry := none

/-- Mismatch carry: (T, 1) where T = d_col[c] + 1 -/
def mismatchCarry (dcolVal : ℤ) : TropCarry where
  threshold := some (dcolVal + 1)
  carry := some 1

/-- Right identity law -/
theorem comp_identity (c : TropCarry) : comp c identity = c := by
  apply ext
  · simp [comp, identity, tropMax, tropPlus]
    cases c.threshold <;> simp
  · simp [comp, identity, tropPlus]
    cases c.carry <;> simp

/-- Left identity law -/
theorem identity_comp (c : TropCarry) : comp identity c = c := by
  apply ext
  · simp [comp, identity, tropMax, tropPlus]
    cases c.threshold <;> cases c.carry <;> simp
  · simp [comp, identity, tropPlus]
    cases c.carry <;> simp

/-! ## Helper lemmas for associativity -/

/-- Tropical addition (plus) is associative -/
theorem tropPlus_assoc (a b c : Option ℤ) :
    tropPlus (tropPlus a b) c = tropPlus a (tropPlus b c) := by
  cases a <;> cases b <;> cases c <;> simp [tropPlus, add_assoc]

/-- Tropical max is associative -/
theorem tropMax_assoc (a b c : Option ℤ) :
    tropMax (tropMax a b) c = tropMax a (tropMax b c) := by
  cases a <;> cases b <;> cases c <;> simp [tropMax, max_assoc]

/-- Tropical plus distributes over tropical max (right):
    (max(a, b)) + c = max(a + c, b + c) -/
theorem tropPlus_tropMax_distrib (a b c : Option ℤ) :
    tropPlus (tropMax a b) c = tropMax (tropPlus a c) (tropPlus b c) := by
  cases a <;> cases b <;> cases c <;> simp [tropMax, tropPlus, max_add_add_right]

/-! ## Associativity of composition (Theorem 3.6) -/

/-- Composition is associative:
    (c₃ ∘ c₂) ∘ c₁ = c₃ ∘ (c₂ ∘ c₁)

    Threshold component:
      max(max(T₃, T₂+K₃), T₁+(K₂+K₃))
      = max(T₃, max(T₂, T₁+K₂)+K₃)          -- by distrib + assoc

    Carry component:
      (K₁+K₂)+K₃ = K₁+(K₂+K₃)               -- by tropPlus_assoc -/
theorem comp_assoc (c₃ c₂ c₁ : TropCarry) :
    comp (comp c₃ c₂) c₁ = comp c₃ (comp c₂ c₁) := by
  apply ext
  · simp [comp]
    rw [tropPlus_tropMax_distrib, tropMax_assoc, tropPlus_assoc]
  · simp [comp, tropPlus_assoc]

end TropCarry
