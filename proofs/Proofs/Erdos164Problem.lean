/-
Erdős Problem #164: Maximum Sum for Primitive Sets

Source: https://erdosproblems.com/164
Status: SOLVED (Lichtman 2023)

Statement:
A set A ⊆ ℕ is primitive if no member of A divides another.
Is the sum Σ_{n ∈ A} 1/(n log n) maximized when A is the set of primes?

Answer: YES — proved by Jared Lichtman (2023)

Background:
- Erdős (1935) proved that Σ 1/(n log n) converges for any primitive set
- Erdős conjectured the primes maximize this sum (posed 1976, repeated 1986)
- Lichtman (2023) proved the conjecture: primes uniquely maximize the sum
- The prime sum Σ_p 1/(p log p) ≈ 1.6366...

References:
- [Er35] Erdős, "Note on Sequences of Integers No One of Which is Divisible
  By Any Other" (1935)
- [Li23] Lichtman, "A proof of the Erdős primitive set conjecture" (2023),
  arXiv:2202.02384

Tags: number-theory, primitive-sets, primes, extremal, solved
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real Set

namespace Erdos164

/-
## Part 1: Primitive Sets
-/

/-- A set A ⊆ ℕ is primitive if no member divides another distinct member -/
def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ∣ b → a = b

/-- The set of prime numbers is primitive -/
theorem primes_primitive : IsPrimitive {p : ℕ | p.Prime} := by
  intro a b ha hb hdiv
  simp at ha hb
  have : a = 1 ∨ a = b := (Nat.Prime.eq_one_or_self_of_dvd hb a hdiv)
  cases this with
  | inl h1 => exact absurd h1 (Nat.Prime.ne_one ha)
  | inr heq => exact heq

/-- Example: {6, 10, 15} is primitive (no element divides another) -/
example : IsPrimitive {6, 10, 15} := by
  intro a b ha hb hdiv
  simp at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals simp at hdiv ⊢
  all_goals omega

/-
## Part 2: The Sum Σ 1/(n log n)
-/

/-- The function f(n) = 1/(n log n) for n ≥ 2 -/
noncomputable def f (n : ℕ) : ℝ :=
  if n ≥ 2 then 1 / (n * Real.log n) else 0

/-- The sum Σ_{n ∈ A} 1/(n log n) for a finite subset -/
noncomputable def primitiveSumFinite (A : Finset ℕ) : ℝ :=
  A.sum (fun n => f n)

/-- The supremum of finite sums gives the total -/
noncomputable def primitiveSum (A : Set ℕ) : ℝ :=
  ⨆ (S : Finset ℕ) (_ : ↑S ⊆ A), primitiveSumFinite S

/-- The sum over primes: Σ_p 1/(p log p) -/
noncomputable def primeSum : ℝ :=
  primitiveSum {p : ℕ | p.Prime}

/-
## Part 3: Erdős's Convergence Theorem (1935)
-/

/-- Erdős (1935): For any primitive set A, the sum Σ 1/(n log n) converges.
    This was the foundational result that made the conjecture meaningful. -/
axiom erdos_convergence :
  ∀ A : Set ℕ, IsPrimitive A → ∃ M : ℝ, primitiveSum A ≤ M

/-- The sum over primes converges (immediate from erdos_convergence) -/
theorem primes_sum_converges : ∃ M : ℝ, primeSum ≤ M :=
  erdos_convergence {p : ℕ | p.Prime} primes_primitive

/-- The prime sum Σ 1/(p log p) ≈ 1.6366... is bounded between 1.6 and 1.7 -/
axiom primes_sum_value : primeSum > 1.6 ∧ primeSum < 1.7

/-
## Part 4: Lichtman's Theorem (2023) — The Main Result
-/

/-- Lichtman's Theorem (2023): The primes maximize Σ 1/(n log n) among
    all primitive sets. This resolves Erdős Problem #164 affirmatively.
    The proof uses a comparison argument exploiting multiplicative structure. -/
axiom lichtman_theorem :
  ∀ A : Set ℕ, IsPrimitive A → primitiveSum A ≤ primeSum

/-- Lichtman also proved uniqueness: the primes are the only maximizer -/
axiom lichtman_uniqueness :
  ∀ A : Set ℕ, IsPrimitive A → primitiveSum A = primeSum →
    A = {p : ℕ | p.Prime}

/-- The answer to Erdős Problem #164 -/
theorem erdos_164_answer :
    ∀ A : Set ℕ, IsPrimitive A → primitiveSum A ≤ primeSum :=
  lichtman_theorem

/-
## Part 5: Generalization — Which Functions Are Maximized by Primes?
-/

/-- A function g : ℕ → ℝ is maximized by primes among primitive sets
    if no primitive set achieves a larger sum than the primes -/
def IsMaximizedByPrimes (g : ℕ → ℝ) : Prop :=
  ∀ A : Set ℕ, IsPrimitive A →
    (∃ M : ℝ, ∀ S : Finset ℕ, ↑S ⊆ A → S.sum g ≤ M) →
    (⨆ (S : Finset ℕ) (_ : ↑S ⊆ A), S.sum g) ≤
    (⨆ (S : Finset ℕ) (_ : ↑S ⊆ {p : ℕ | p.Prime}), S.sum g)

/-- 1/(n log n) is maximized by primes (Lichtman 2023) -/
theorem f_maximized_by_primes : IsMaximizedByPrimes f := by
  intro A hA _
  exact lichtman_theorem A hA

/-
## Part 6: Summary
-/

/-- Erdős Problem #164: SOLVED (Lichtman 2023)

QUESTION: Is Σ_{n ∈ A} 1/(n log n) maximized when A is the set of primes,
among all primitive sets A?

ANSWER: YES. The primes uniquely maximize this sum. -/
theorem erdos_164_main :
    (∀ A : Set ℕ, IsPrimitive A → primitiveSum A ≤ primeSum) ∧
    (∀ A : Set ℕ, IsPrimitive A → primitiveSum A = primeSum →
      A = {p | p.Prime}) :=
  ⟨lichtman_theorem, lichtman_uniqueness⟩

end Erdos164
