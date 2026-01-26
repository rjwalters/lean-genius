/-!
# Erdős Problem #51: Totient Preimage Growth

Is there an infinite set A ⊂ ℕ such that every a ∈ A is a totient value
(i.e., φ(n) = a for some n), yet the smallest preimage n_a satisfies
n_a / a → ∞ as a → ∞?

## Key Context

- Euler's totient φ(n) counts integers ≤ n coprime to n
- The inverse totient problem: given a, find smallest n with φ(n) = a
- Carmichael conjectured no totient value has exactly one preimage
- Erdős proved: if any counterexample exists, infinitely many do
- Related to Problem #694 on totient preimage structure

## References

- [Er95] Erdős (1995)
- [Er98] Erdős (1998)
- [Gu04] Guy, Unsolved Problems in Number Theory, B36, B39
- OEIS A002202 (totient values), A014197 (inverse totient counts)
- <https://erdosproblems.com/51>
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Filter
open scoped Nat Topology

/-! ## Core Definitions -/

/-- The set of preimages of a under Euler's totient function. -/
def totientPreimage (a : ℕ) : Set ℕ :=
  {n : ℕ | n.totient = a}

/-- Whether a natural number is a totient value (in the range of φ). -/
def IsTotientValue (a : ℕ) : Prop :=
  ∃ n : ℕ, n.totient = a

/-- The smallest preimage of a under φ, if one exists.
    Returns 0 if a is not a totient value. -/
noncomputable def smallestTotientPreimage (a : ℕ) : ℕ :=
  Nat.find (Classical.choice (by
    by_cases h : IsTotientValue a
    · exact ⟨h⟩
    · exact ⟨⟨0, by simp [IsTotientValue] at h; omega⟩⟩
  ) : Nonempty {n : ℕ | n.totient = a})

/-! ## Main Conjecture -/

/-- **Erdős Problem #51**: Is there an infinite set A ⊂ ℕ of totient values
    such that the smallest preimage grows faster than the value itself?

    Formally: ∃ infinite A ⊆ ℕ such that ∀ a ∈ A, IsTotientValue a, and
    smallestTotientPreimage(a) / a → ∞ as a → ∞ through A. -/
axiom erdos_51_conjecture :
  ∃ A : Set ℕ, A.Infinite ∧
    (∀ a ∈ A, IsTotientValue a) ∧
    ∀ C : ℝ, C > 0 → ∃ N : ℕ, ∀ a ∈ A, a ≥ N →
      (smallestTotientPreimage a : ℝ) / (a : ℝ) > C

/-! ## Basic Properties of Totient -/

/-- φ(1) = 1: the trivial totient value. -/
theorem totient_one : Nat.totient 1 = 1 := by simp

/-- φ(p) = p − 1 for prime p. -/
axiom totient_prime :
  ∀ p : ℕ, Nat.Prime p → Nat.totient p = p - 1

/-- φ(n) ≤ n for all n. -/
axiom totient_le :
  ∀ n : ℕ, Nat.totient n ≤ n

/-- φ(n) is even for n ≥ 3. -/
axiom totient_even :
  ∀ n : ℕ, n ≥ 3 → Even (Nat.totient n)

/-! ## Preimage Structure -/

/-- Every even number is a totient value: for any even a ≥ 2,
    there exists n with φ(n) = a. In fact, a + 1 works when a + 1 is prime. -/
axiom even_totient_values :
  ∀ a : ℕ, a ≥ 2 → Even a → IsTotientValue a

/-- The smallest preimage is at least a + 1 (since φ(n) < n for n ≥ 2). -/
axiom smallest_preimage_lower :
  ∀ a : ℕ, a ≥ 2 → IsTotientValue a →
    smallestTotientPreimage a ≥ a + 1

/-- Carmichael's observation: Erdős proved that if any totient value has
    exactly one preimage, then infinitely many do. -/
axiom erdos_carmichael :
  (∃ a : ℕ, IsTotientValue a ∧ (totientPreimage a).ncard = 1) →
  {a : ℕ | IsTotientValue a ∧ (totientPreimage a).ncard = 1}.Infinite

/-! ## Growth Bounds -/

/-- For prime p, the smallest preimage of p − 1 is at most p.
    So smallestTotientPreimage(p−1) ≤ p, giving ratio ≤ p/(p−1) → 1. -/
axiom prime_preimage_ratio :
  ∀ p : ℕ, Nat.Prime p →
    smallestTotientPreimage (p - 1) ≤ p

/-- Totient values p − 1 for primes p have small preimage ratios.
    This shows the conjecture requires avoiding these "easy" totient values. -/
axiom prime_minus_one_ratio_bounded :
  ∀ p : ℕ, Nat.Prime p → p ≥ 3 →
    (smallestTotientPreimage (p - 1) : ℝ) / ((p : ℝ) - 1) ≤ 2

/-- The inverse totient counting function: number of solutions to φ(n) = a. -/
noncomputable def inverseTotientCount (a : ℕ) : ℕ :=
  (totientPreimage a).ncard

/-- Highly totient numbers have many preimages; the conjecture asks about
    values where the smallest preimage is disproportionately large. -/
axiom highly_totient_exist :
  ∀ k : ℕ, ∃ a : ℕ, inverseTotientCount a ≥ k
