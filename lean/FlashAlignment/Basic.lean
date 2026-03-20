import Mathlib.Tactic

/-!
# Basic definitions for semi-local string comparison

This file defines the core types: finite alphabets, strings, match predicates,
and the Krusche comb.
-/

/-- A position in the seaweed braid has index in `Fin (m + n)` -/
abbrev WireIdx (m n : ℕ) := Fin (m + n)

/-- The match predicate: whether two characters are equal -/
def isMatch {α : Type*} [DecidableEq α] (a b : α) : Bool := a == b

/-- Distance column: a vector of n natural numbers -/
def DCol (n : ℕ) := Fin n → ℕ

/-- Row distance: a vector of m natural numbers -/
def DRow (m : ℕ) := Fin m → ℕ

/-- Depth column: gap depth per column wire -/
def DepthCol (n : ℕ) := Fin n → ℕ

/-- Depth row: gap depth per row wire -/
def DepthRow (m : ℕ) := Fin m → ℕ
