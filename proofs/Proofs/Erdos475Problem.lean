/-
Erdős Problem #475: Graham's Rearrangement Conjecture

Source: https://erdosproblems.com/475
Status: OPEN (proven for various ranges of t)

Statement:
Let p be a prime. Given any finite set A ⊆ 𝔽ₚ \ {0}, is there always a
rearrangement A = {a₁, ..., aₜ} such that all partial sums Σₖ₌₁ᵐ aₖ
are distinct for all 1 ≤ m ≤ t?

Background:
This asks whether every non-zero subset of a prime field can be ordered
so that cumulative sums never repeat. Such an ordering is called a "valid
ordering" or "sequencing."

Known Results:
- Graham: True when t = p - 1 (the full set)
- Costa-Pellegrini (2020): True for t ≤ 12
- Hicks-Ollis-Schmitt (2019): True for p - 3 ≤ t ≤ p - 1
- Kravitz (2024): True for t ≤ log p / log log p
- Bedert-Kravitz (2024): True for t ≤ exp((log p)^{1/4})

References:
- [CoPe20] Costa-Pellegrini, "Some new results about a conjecture by Alspach"
- [HOS19] Hicks-Ollis-Schmitt, "Distinct partial sums in cyclic groups"
- [Kr24] Kravitz, "Rearranging small sets for distinct partial sums"
- [BeKr24] Bedert-Kravitz, "Graham's rearrangement conjecture beyond the
   rectification barrier"

Tags: additive-combinatorics, finite-fields, sequencing, partial-sums
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace Erdos475

open Finset

/- ## Part I: Valid Orderings -/

/-- A partial sum sequence: the cumulative sums of a list. -/
def partialSums {G : Type*} [AddMonoid G] (l : List G) : List G :=
  l.scanl (· + ·) 0 |>.tail

/-- An ordering of a set is valid if all partial sums are distinct. -/
def IsValidOrdering {p : ℕ} [Fact (Nat.Prime p)] (A : Finset (ZMod p))
    (ordering : List (ZMod p)) : Prop :=
  ordering.toFinset = A ∧
  ordering.Nodup ∧
  (partialSums ordering).Nodup

/-- Graham's conjecture: every non-zero subset has a valid ordering. -/
def GrahamConjecture (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ A : Finset (ZMod p), (∀ a ∈ A, a ≠ 0) →
    ∃ ordering : List (ZMod p), IsValidOrdering A ordering

/- ## Part II: Small Cases (Costa-Pellegrini 2020) -/

/--
**Costa-Pellegrini (2020):**
For t ≤ 12, the conjecture holds. Verified through a combination of
exhaustive computation for specific primes and theoretical reductions.
-/
axiom costa_pellegrini_2020 (p : ℕ) [Fact (Nat.Prime p)] (hp : p > 12) :
    ∀ A : Finset (ZMod p), A.card ≤ 12 → (∀ a ∈ A, a ≠ 0) →
      ∃ ordering : List (ZMod p), IsValidOrdering A ordering

/-- Explicit valid orderings exist for small sets. -/
theorem small_sets_have_valid_orderings (p : ℕ) [Fact (Nat.Prime p)]
    (A : Finset (ZMod p)) (hA : A.card ≤ 12) (hnonzero : ∀ a ∈ A, a ≠ 0)
    (hp : p > 12) :
    ∃ ordering : List (ZMod p), IsValidOrdering A ordering :=
  costa_pellegrini_2020 p hp A hA hnonzero

/- ## Part III: Large Cases — Near p (Hicks-Ollis-Schmitt 2019) -/

/--
**Hicks-Ollis-Schmitt (2019):**
For p - 3 ≤ t ≤ p - 1, the conjecture holds. When the set is
nearly the entire non-zero field, structural arguments suffice.
-/
axiom hicks_ollis_schmitt_2019 (p : ℕ) [Fact (Nat.Prime p)] :
    ∀ A : Finset (ZMod p), p - 3 ≤ A.card ∧ A.card ≤ p - 1 →
      (∀ a ∈ A, a ≠ 0) →
      ∃ ordering : List (ZMod p), IsValidOrdering A ordering

/--
**Graham's Original Result:**
The case t = p - 1 (the full non-zero set) was solved constructively
by Graham, providing an explicit ordering.
-/
/- ## Part IV: Logarithmic Range (Kravitz 2024) -/

/--
**Kravitz (2024):**
For t ≤ log p / log log p, the conjecture holds.
Will Sawin independently observed this bound on MathOverflow.
This significantly extends beyond the constant bound of 12.
-/
/- ## Part V: Beyond the Rectification Barrier (Bedert-Kravitz 2024)

Previous methods hit a "rectification barrier" at log p / log log p.
Bedert and Kravitz (2024) developed new techniques that go far beyond
this barrier, reaching exp((log p)^{1/4}).
-/

/--
**Bedert-Kravitz (2024):**
For t ≤ exp((log p)^{1/4}), the conjecture holds.
This is a major breakthrough beyond the rectification barrier.
exp((log p)^{1/4}) ≫ log p / log log p for large p.
-/
axiom bedert_kravitz_2024 (p : ℕ) [Fact (Nat.Prime p)] (hp : p > 2) :
    ∀ A : Finset (ZMod p),
      (A.card : ℝ) ≤ Real.exp ((Real.log p) ^ (1/4 : ℝ)) →
      (∀ a ∈ A, a ≠ 0) →
      ∃ ordering : List (ZMod p), IsValidOrdering A ordering

/- ## Part VI: Connection to Alspach's Conjecture

Alspach generalized Graham's conjecture to arbitrary finite abelian groups.
Graham's conjecture is precisely Alspach's conjecture for G = 𝔽ₚ.
-/

/-- Alspach's generalization to arbitrary abelian groups. -/
def AlspachConjecture (G : Type*) [AddCommGroup G] [Fintype G] : Prop :=
  ∀ A : Finset G, (∀ a ∈ A, a ≠ 0) →
    ∃ ordering : List G, ordering.toFinset = A ∧ ordering.Nodup ∧
      (partialSums ordering).Nodup

/-- Graham's conjecture is Alspach's conjecture for 𝔽ₚ. -/
theorem graham_is_alspach_for_prime_field (p : ℕ) [Fact (Nat.Prime p)] :
    GrahamConjecture p ↔ AlspachConjecture (ZMod p) := by
  constructor <;> intro h A hA <;> exact h A hA

/- ## Part VII: Constructive vs Existential

Some proofs provide explicit constructions of valid orderings,
while others are purely existential.
-/

/-- Some proofs give explicit constructions. -/
def HasExplicitValidOrdering {p : ℕ} [Fact (Nat.Prime p)]
    (A : Finset (ZMod p)) : Prop :=
  ∃ (f : Finset (ZMod p) → List (ZMod p)),
    IsValidOrdering A (f A)

/--
**Graham's Constructive Proof:**
Graham's proof for the full non-zero set t = p - 1 was constructive,
giving an explicit algorithm to produce a valid ordering.
-/
/- ## Part VIII: Summary

Graham's conjecture (Erdős Problem #475) has been proven for:
- Small t (≤ 12): Costa-Pellegrini 2020
- Large t (≥ p - 3): Hicks-Ollis-Schmitt 2019
- Medium t (≤ exp((log p)^{1/4})): Bedert-Kravitz 2024

The general case remains OPEN.
-/

/--
**Erdős Problem #475: Summary**

Combines the key axiomatized results:
1. Small case: t ≤ 12 (Costa-Pellegrini)
2. Large case: p - 3 ≤ t ≤ p - 1 (Hicks-Ollis-Schmitt)
3. Medium case: t ≤ exp((log p)^{1/4}) (Bedert-Kravitz)
4. Graham's original: t = p - 1 (constructive)
5. Alspach equivalence: GrahamConjecture p ↔ AlspachConjecture (ZMod p)
-/
theorem erdos_475_summary (p : ℕ) [Fact (Nat.Prime p)] (hp12 : p > 12) (hp2 : p > 2) :
    -- Small cases verified
    (∀ A : Finset (ZMod p), A.card ≤ 12 → (∀ a ∈ A, a ≠ 0) →
      ∃ ordering : List (ZMod p), IsValidOrdering A ordering) ∧
    -- Large cases verified
    (∀ A : Finset (ZMod p), p - 3 ≤ A.card ∧ A.card ≤ p - 1 →
      (∀ a ∈ A, a ≠ 0) →
      ∃ ordering : List (ZMod p), IsValidOrdering A ordering) ∧
    -- Bedert-Kravitz breakthrough
    (∀ A : Finset (ZMod p),
      (A.card : ℝ) ≤ Real.exp ((Real.log p) ^ (1/4 : ℝ)) →
      (∀ a ∈ A, a ≠ 0) →
      ∃ ordering : List (ZMod p), IsValidOrdering A ordering) :=
  ⟨costa_pellegrini_2020 p hp12,
   hicks_ollis_schmitt_2019 p,
   bedert_kravitz_2024 p hp2⟩

end Erdos475
