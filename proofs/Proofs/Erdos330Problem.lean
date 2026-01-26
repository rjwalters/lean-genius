/-!
# Erdős Problem #330: Minimal Bases with Positive Density

Does there exist a minimal asymptotic additive basis A ⊂ ℕ of order h
with positive upper density such that for every n ∈ A, the upper density
of integers not representable as a sum of at most h elements from A \ {n}
is also positive?

A set A is an asymptotic additive basis of order h if every sufficiently
large integer can be written as a sum of at most h elements of A (with
repetition). A basis is minimal if removing any element destroys this
property.

Status: OPEN.

Reference: https://erdosproblems.com/330
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

/-! ## Definitions -/

/-- A can represent m using at most h summands (with repetition from A). -/
def IsRepresentable (A : Set ℕ) (h m : ℕ) : Prop :=
  ∃ (k : ℕ) (_ : k ≤ h) (f : Fin k → ℕ),
    (∀ i, f i ∈ A) ∧ (Finset.univ.sum f) = m

/-- A is an asymptotic additive basis of order h: every sufficiently
    large integer is representable. -/
def IsAsympBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m → IsRepresentable A h m

/-- The upper density of a set S ⊆ ℕ. Axiomatized. -/
axiom upperDensity (S : Set ℕ) : ℝ

/-- upperDensity is nonneg. -/
axiom upperDensity_nonneg (S : Set ℕ) : 0 ≤ upperDensity S

/-- upperDensity is at most 1. -/
axiom upperDensity_le_one (S : Set ℕ) : upperDensity S ≤ 1

/-- A has positive upper density. -/
def HasPosDensity (A : Set ℕ) : Prop := 0 < upperDensity A

/-- A is a minimal asymptotic basis of order h: it is a basis, but
    removing any single element destroys the basis property. -/
def IsMinimalBasis (A : Set ℕ) (h : ℕ) : Prop :=
  IsAsympBasis A h ∧ ∀ n ∈ A, ¬IsAsympBasis (A \ {n}) h

/-- The set of integers not representable from A \ {n} with at most
    h summands. -/
def unrepresentableWithout (A : Set ℕ) (n h : ℕ) : Set ℕ :=
  {m : ℕ | ¬IsRepresentable (A \ {n}) h m}

/-! ## Known Results -/

/-- For a minimal basis, removing any element leaves infinitely many
    integers unrepresentable (by definition of minimality). -/
axiom minimal_basis_infinite_unrep (A : Set ℕ) (h : ℕ)
    (hA : IsMinimalBasis A h) (n : ℕ) (hn : n ∈ A) :
  Set.Infinite (unrepresentableWithout A n h)

/-- There exist minimal bases of every order h ≥ 2. -/
axiom minimal_basis_exists (h : ℕ) (hh : 2 ≤ h) :
  ∃ A : Set ℕ, IsMinimalBasis A h

/-- There exist minimal bases with positive density (Härtter 1956,
    Stöhr 1955 for h = 2). Whether the stronger property holds is open. -/
axiom minimal_basis_pos_density_exists (h : ℕ) (hh : 2 ≤ h) :
  ∃ A : Set ℕ, IsMinimalBasis A h ∧ HasPosDensity A

/-! ## The Open Question -/

/-- Erdős Problem #330 (Erdős–Nathanson): Does there exist a minimal
    basis A of order h with positive density such that for every n ∈ A,
    the set of integers unrepresentable without n also has positive
    upper density? -/
axiom erdos_330_strong_minimal_basis :
  ∃ (A : Set ℕ) (h : ℕ),
    IsMinimalBasis A h ∧
    HasPosDensity A ∧
    ∀ n ∈ A, HasPosDensity (unrepresentableWithout A n h)
