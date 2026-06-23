/-
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

/- ## Core Definitions -/

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

/- ## Main Conjecture -/

/-- **Erdős Problem #51**: Is there an infinite set A ⊂ ℕ of totient values
    such that the smallest preimage grows faster than the value itself? -/

/- ## Basic Properties of Totient -/

/-- φ(1) = 1: the trivial totient value. -/
theorem totient_one : Nat.totient 1 = 1 := by simp

/- ## Preimage Structure -/

/- ## Growth Bounds -/

/-- The inverse totient counting function: number of solutions to φ(n) = a. -/
noncomputable def inverseTotientCount (a : ℕ) : ℕ :=
  (totientPreimage a).ncard
