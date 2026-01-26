/-!
# Erdős Problem #943 — Representation by Sums of Two Powerful Numbers

A powerful number is n such that if p | n then p² | n. Let A be the
set of powerful numbers. Define r(n) = |{(a,b) : a,b ∈ A, a+b = n}|,
the number of representations of n as a sum of two powerful numbers.

Question: Is r(n) = n^{o(1)} for every n? Equivalently, does the
Dirichlet-style convolution 1_A ∗ 1_A(n) grow subpolynomially?

This asks whether every integer has at most subpolynomially many
representations as a sum of two powerful numbers.

Status: OPEN
Reference: https://erdosproblems.com/943
Source: [Er76d]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A natural number is powerful if every prime dividing it
    appears with exponent ≥ 2. Equivalently, n = a²b³ for
    some a, b. -/
def IsPowerful (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- The set of powerful numbers. -/
def PowerfulSet : Set ℕ := {n : ℕ | IsPowerful n}

/-- r(n): the number of representations of n as a sum of two
    powerful numbers. -/
noncomputable def powerfulSumRep (n : ℕ) : ℕ :=
  Finset.card (Finset.filter
    (fun a => IsPowerful a ∧ IsPowerful (n - a) ∧ a ≤ n)
    (Finset.range (n + 1)))

/-! ## Main Question -/

/-- **Erdős Problem #943**: Is r(n) = n^{o(1)}? That is, for every
    ε > 0, is r(n) < n^ε for all sufficiently large n? -/
axiom erdos_943_subpolynomial :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (powerfulSumRep n : ℝ) ≤ (n : ℝ) ^ ε

/-! ## Known Results -/

/-- **Powerful number density**: The number of powerful numbers
    up to x is asymptotically c·√x where c = ζ(3/2)/ζ(3).
    This gives about √x potential summands for each n. -/
axiom powerful_density :
  ∃ c : ℝ, c > 0 ∧ ∀ x : ℕ, x ≥ 1 →
    (Finset.card (Finset.filter IsPowerful (Finset.range (x + 1))) : ℝ) ≤
      c * (x : ℝ) ^ ((1 : ℝ) / 2)

/-- **Trivial upper bound**: r(n) ≤ |A ∩ [1,n]| ≤ c·√n.
    The question asks whether the true growth is much slower. -/
axiom trivial_upper_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (powerfulSumRep n : ℝ) ≤ c * (n : ℝ) ^ ((1 : ℝ) / 2)

/-- **Powerful number structure**: Every powerful number can be
    written as a²b³ for some a, b ≥ 1. The special structure
    constrains which pairs can sum to n. -/
axiom powerful_structure :
  ∀ n : ℕ, IsPowerful n →
    ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ n = a ^ 2 * b ^ 3

/-! ## Observations -/

/-- **Average order**: On average over n ≤ x, the sum
    Σ_{n≤x} r(n) ∼ c²x (since there are ~c√x powerful numbers
    up to x). The question is about pointwise bounds. -/
axiom average_order : True

/-- **Connection to squares**: Perfect squares form a subset of
    powerful numbers. Representations as sums of two squares
    are well-understood (Jacobi's formula), but the powerful
    number case is harder due to the irregular structure. -/
axiom squares_connection : True

/-- **Diophantine constraints**: For n = a²b³ + c²d³, the
    equation constrains a,b,c,d in ways that should limit
    the number of solutions, but making this rigorous is
    the core difficulty. -/
axiom diophantine_constraints : True
