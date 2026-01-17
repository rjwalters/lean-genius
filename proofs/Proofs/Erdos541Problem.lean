/-
Erdős Problem #541: Graham's Conjecture on Zero-Sum Subsequences

Let a₁, ..., aₚ be (not necessarily distinct) residues modulo a prime p. Suppose
there exists some fixed r such that every nonempty subset S ⊆ [p] with
  Σᵢ∈S aᵢ ≡ 0 (mod p)
satisfies |S| = r.

**Graham's Conjecture** (SOLVED): Under these conditions, there are at most 2
distinct residues among the aᵢ.

**History**:
- Graham posed this question
- Erdős and Szemerédi (1976) proved it for p sufficiently large
- Gao, Hamidoune, and Wang (2010) proved it for all moduli (not just primes)

Reference: https://erdosproblems.com/541
-/

import Mathlib

namespace Erdos541

open scoped Classical
open Finset

/-!
## The Setup

We have p residues modulo p, indexed by Fin p. The key property is that
all zero-sum subsets have the same cardinality r.
-/

/-- Property: all nonempty zero-sum subsets have cardinality exactly r -/
def HasUniqueZeroSumLength (p : ℕ) (a : Fin p → ZMod p) (r : ℕ) : Prop :=
  ∀ (S : Finset (Fin p)), S ≠ ∅ → (∑ i ∈ S, a i) = 0 → S.card = r

/-- Property: there exists some r such that all nonempty zero-sum subsets have that cardinality -/
def HasSomeUniqueZeroSumLength (p : ℕ) (a : Fin p → ZMod p) : Prop :=
  ∃ r, HasUniqueZeroSumLength p a r

/-- Count of distinct values in the sequence -/
noncomputable def distinctCount (p : ℕ) (a : Fin p → ZMod p) : ℕ :=
  (Set.range a).ncard

/-!
## Main Theorem: Graham's Conjecture

If all nonempty zero-sum subsets have the same cardinality, then the sequence
uses at most 2 distinct residues.

The intuition: if there are 3 or more distinct values, one can construct
zero-sum subsets of different sizes by mixing elements appropriately.
-/

/-- **Graham's Conjecture** (Erdős Problem #541)

If a sequence of p residues modulo p has the property that all nonempty
zero-sum subsets have the same cardinality, then at most 2 distinct
residues appear in the sequence.

This was first posed by Graham, proved for large p by Erdős-Szemerédi (1976),
and fully resolved by Gao-Hamidoune-Wang (2010). -/
theorem graham_conjecture (p : ℕ) [hp : Fact p.Prime] (a : Fin p → ZMod p)
    (h : HasSomeUniqueZeroSumLength p a) : distinctCount p a ≤ 2 := by
  -- The full proof uses combinatorial arguments about zero-sum sequences
  -- and was resolved by Gao, Hamidoune, and Wang in 2010
  sorry

/-!
## Special Cases and Variants
-/

/-- **Erdős-Szemerédi (1976)**: The conjecture holds for sufficiently large primes -/
axiom erdos_szemeredi_large_primes :
    ∀ᶠ p in Filter.atTop, p.Prime → ∀ a : Fin p → ZMod p,
    HasSomeUniqueZeroSumLength p a → distinctCount p a ≤ 2

/-- **Gao-Hamidoune-Wang (2010)**: The conjecture holds for ALL moduli, not just primes

This is the most general form of Graham's conjecture. -/
axiom gao_hamidoune_wang (n : ℕ) (a : Fin n → ZMod n)
    (h : HasSomeUniqueZeroSumLength n a) : distinctCount n a ≤ 2

/-!
## Examples

To build intuition, consider what happens with 1, 2, or 3 distinct values.
-/

/-- Example: the constant sequence (all same residue) trivially satisfies the property

If a₁ = a₂ = ... = aₚ = c, then Σᵢ∈S aᵢ = |S| · c ≡ 0 (mod p) iff |S| ≡ 0 (mod ord(c)).
All such subsets have cardinality divisible by ord(c). -/
example (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    distinctCount p (fun _ : Fin p => c) ≤ 1 := by
  unfold distinctCount
  simp [Set.range_const, Set.ncard_singleton]

/-- Example: two distinct values can also work

Consider alternating 0 and 1 in positions. Zero-sum subsets must balance. -/
example (p : ℕ) [Fact p.Prime] (c d : ZMod p) (h : c ≠ d) :
    distinctCount p (fun i : Fin p => if i.val % 2 = 0 then c else d) ≤ 2 := by
  unfold distinctCount
  -- The range is {c, d} which has cardinality ≤ 2
  have hsub : Set.range (fun i : Fin p => if i.val % 2 = 0 then c else d) ⊆ {c, d} := by
    intro x hx
    simp only [Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    split_ifs at hi <;> simp [hi]
  have hcard : ({c, d} : Set (ZMod p)).ncard ≤ 2 := by
    -- {c, d} is insert c {d}, so need c ∉ {d}
    have hne : c ∉ ({d} : Set (ZMod p)) := by
      simp only [Set.mem_singleton_iff]
      exact h
    rw [Set.ncard_insert_of_notMem hne (Set.finite_singleton d), Set.ncard_singleton]
  exact le_trans (Set.ncard_le_ncard hsub) hcard

/-!
## The Key Insight

Why does 3 or more distinct values fail? The proof relies on:

1. **Olson's Theorem**: In any sequence of p elements from Z/pZ, there exists
   a nonempty zero-sum subsequence of length ≤ p.

2. **Structural argument**: With 3+ distinct values {a, b, c}, one can find
   zero-sum subsets of different cardinalities by:
   - Using copies of a alone (if a·k ≡ 0)
   - Mixing a's and b's
   - Introducing c's

The detailed combinatorial argument shows these lead to contradictory cardinalities.
-/

/-- Connection to Olson's theorem: in Z/pZ, zero-sum subsequences always exist -/
theorem zero_sum_exists (p : ℕ) [hp : Fact p.Prime] (a : Fin p → ZMod p) :
    ∃ (S : Finset (Fin p)), S ≠ ∅ ∧ (∑ i ∈ S, a i) = 0 := by
  -- This follows from the pigeonhole principle on partial sums
  -- Consider s₀ = 0, s₁ = a₁, s₂ = a₁ + a₂, ..., sₚ = a₁ + ... + aₚ
  -- These p+1 values in Z/pZ must have a collision: sᵢ = sⱼ for some i < j
  -- Then Σₖ∈{i+1,...,j} aₖ = sⱼ - sᵢ = 0
  sorry

/-!
## Historical Context

Graham's conjecture arose from the study of zero-sum problems in additive
combinatorics. Zero-sum theory studies when subsets of elements from an
abelian group must contain zero-sum subsequences.

Key milestones:
- **Davenport constant**: minimum length ensuring a zero-sum subsequence exists
- **Erdős-Ginzburg-Ziv (1961)**: 2n-1 integers contain n with sum ≡ 0 (mod n)
- **Olson's work**: bounds on zero-sum subsequence lengths

Graham's specific question about "unique cardinality" zero-sum subsets
captures an extremal phenomenon: such strong constraints force the sequence
to be nearly constant.
-/

/-- The Erdős-Ginzburg-Ziv theorem: 2n-1 integers contain n summing to 0 mod n -/
axiom erdos_ginzburg_ziv (n : ℕ) (hn : n > 0) (a : Fin (2*n - 1) → ZMod n) :
    ∃ (S : Finset (Fin (2*n - 1))), S.card = n ∧ (∑ i ∈ S, a i) = 0

end Erdos541
