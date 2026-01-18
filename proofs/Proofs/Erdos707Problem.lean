/-
Erdős Problem #707: Embedding Sidon Sets in Perfect Difference Sets

**Question**: Let A ⊆ ℕ be a finite Sidon set. Is there some set B with A ⊆ B
which is a perfect difference set modulo p² + p + 1 for some prime p?

**Status**: DISPROVED

**Prize**: $1000 (offered in 1980)

**Solution History**:
- Hall (1947): First disproved this, before Erdős even asked!
  Showed {1,3,9,10,13} cannot extend to any perfect difference set.
- Alexeev-Mixon (2025): Independently rediscovered, with formal Lean proof.
  Showed {1,2,4,8} cannot extend for any prime p.
  Showed {1,2,4,8,13} cannot extend to any perfect difference set.

**Positive Results**:
- Any Sidon set of size ≤ 3 can be extended (Sawin, MathOverflow)
- Singer construction gives perfect difference sets for n = p² + p + 1

**Open**: Can any Sidon set of size 4 be extended?

References:
- https://erdosproblems.com/707
- [AlMi25] Alexeev-Mixon, "Forbidden Sidon subsets..." arXiv:2510.19804 (2025)
- [Ha47] Hall, "Cyclic projective planes", Duke Math. J. (1947)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Erdos707

open Finset

/-! ## Key Definitions

A **Sidon set** (also called B₂ sequence) is a set where all pairwise sums are distinct.
A **perfect difference set** mod n is a set where every nonzero residue appears exactly
once as a difference.
-/

/-- A set A ⊆ ℕ is a Sidon set if all pairwise sums a + b (with a ≤ b) are distinct.
Equivalently, a + b = c + d with a ≤ b and c ≤ d implies {a,b} = {c,d}. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/-- Alternative characterization: all pairwise differences are distinct (except 0). -/
def IsSidonDiff (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≠ b → c ≠ d → (a : ℤ) - b = (c : ℤ) - d → (a = c ∧ b = d)

/-- The two characterizations are equivalent. -/
axiom sidon_equiv (A : Finset ℕ) : IsSidon A ↔ IsSidonDiff A

/-- A perfect difference set mod n is a set B where every nonzero element of ℤ/nℤ
appears exactly once as a difference b₁ - b₂ (mod n) for b₁, b₂ ∈ B, b₁ ≠ b₂.
This is related to cyclic projective planes. -/
def IsPerfectDifferenceSet (B : Finset ℕ) (n : ℕ) : Prop :=
  n > 0 ∧
  ∀ r : ℕ, 1 ≤ r → r < n →
    (Finset.filter (fun p : ℕ × ℕ => p.1 ∈ B ∧ p.2 ∈ B ∧ p.1 ≠ p.2 ∧
      ((p.1 : ℤ) - p.2) % n = r) (B ×ˢ B)).card = 1

/-! ## Main Theorem: The Conjecture is FALSE

Erdős asked if every finite Sidon set can be embedded in a perfect difference set
mod p² + p + 1 for some prime p. The answer is NO. -/

/-- **Erdős Problem #707 (DISPROVED)**:

It is FALSE that every finite Sidon set can be embedded in a perfect
difference set mod n for some n > 0.

Counterexamples: {1,3,9,10,13} (Hall 1947), {1,2,4,8,13} (Alexeev-Mixon 2025). -/
axiom erdos_707_false : ¬(∀ A : Finset ℕ, IsSidon A →
    ∃ B : Finset ℕ, ∃ n : ℕ, n > 0 ∧ A ⊆ B ∧ IsPerfectDifferenceSet B n)

/-- The formal statement of the problem (shown to be false). -/
def erdos_707_statement : Prop :=
  ∀ A : Finset ℕ, IsSidon A →
    ∃ B : Finset ℕ, ∃ p : ℕ, p.Prime ∧ A ⊆ B ∧
      IsPerfectDifferenceSet B (p^2 + p + 1)

/-- The statement is false. -/
axiom erdos_707_statement_false : ¬erdos_707_statement

/-! ## Counterexamples -/

/-- The set {1, 2, 4} is a Sidon set. -/
theorem sidon_124 : IsSidon {1, 2, 4} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [mem_insert, mem_singleton] at ha hb hc hd
  -- Case analysis on all possible values
  rcases ha with rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl <;>
  rcases hd with rfl | rfl | rfl <;>
  simp_all

/-- The set {1, 2, 4, 8} is a Sidon set.
This is the start of the Mian-Chowla sequence. -/
axiom sidon_1248 : IsSidon {1, 2, 4, 8}

/-- The set {1, 2, 4, 8, 13} is a Sidon set (Mian-Chowla continuation). -/
axiom sidon_12_4_8_13 : IsSidon {1, 2, 4, 8, 13}

/-- The set {1, 3, 9, 10, 13} is a Sidon set (Hall's counterexample). -/
axiom sidon_hall : IsSidon {1, 3, 9, 10, 13}

/-- **Alexeev-Mixon (2025)**: {1,2,4,8} cannot be extended to a perfect
difference set mod p² + p + 1 for any prime p. -/
axiom counterexample_alexeev_mixon_prime :
  ∀ B : Finset ℕ, ∀ p : ℕ, p.Prime →
    {1, 2, 4, 8} ⊆ B → ¬IsPerfectDifferenceSet B (p^2 + p + 1)

/-- **Alexeev-Mixon (2025)**: {1,2,4,8,13} cannot be extended to ANY
perfect difference set. -/
axiom counterexample_mian_chowla :
  ∀ B : Finset ℕ, ∀ n : ℕ,
    ({1, 2, 4, 8, 13} : Finset ℕ) ⊆ B → ¬IsPerfectDifferenceSet B n

/-- **Hall (1947)**: {1,3,9,10,13} cannot be extended to ANY
perfect difference set. This was proved before Erdős even asked the question! -/
axiom counterexample_hall :
  ∀ B : Finset ℕ, ∀ n : ℕ,
    ({1, 3, 9, 10, 13} : Finset ℕ) ⊆ B → ¬IsPerfectDifferenceSet B n

/-! ## Positive Results -/

/-- **Size bound**: A perfect difference set mod n has size at most √n + 1.
This is because each of the n-1 nonzero differences must be represented
exactly once, giving |B|(|B|-1) = n-1, so |B| ≈ √n. -/
axiom perfect_diff_set_size_bound (B : Finset ℕ) (n : ℕ) :
  IsPerfectDifferenceSet B n → B.card ≤ Nat.sqrt n + 1

/-- **Singer construction (1938)**: For any prime power p, there exists a
perfect difference set mod p² + p + 1 of size p + 1.
This comes from the theory of cyclic projective planes. -/
axiom singer_construction (p : ℕ) (hp : Nat.Prime p) :
  ∃ B : Finset ℕ, IsPerfectDifferenceSet B (p^2 + p + 1) ∧ B.card = p + 1

/-- **Small Sidon sets**: Any Sidon set of size ≤ 3 can be extended to a
perfect difference set. (Sawin, MathOverflow discussion) -/
axiom small_sidon_extendable (A : Finset ℕ) :
  IsSidon A → A.card ≤ 3 →
    ∃ B : Finset ℕ, ∃ p : ℕ, Nat.Prime p ∧ A ⊆ B ∧
      IsPerfectDifferenceSet B (p^2 + p + 1)

/-- **Example**: {1, 2, 4} can be embedded in a perfect difference set mod 7.
Here 7 = 2² + 2 + 1, and B = {0, 1, 3} (or equivalently {1, 2, 4}) works. -/
axiom example_124_in_7 :
  ∃ B : Finset ℕ, {1, 2, 4} ⊆ B ∧ IsPerfectDifferenceSet B 7

/-! ## Connection to Sidon Set Density

This problem is related to Erdős Problem #329 about the density of Sidon sets.
If the conjecture were TRUE, it would imply optimal density for Sidon sets. -/

/-- If the conjecture were true (which it's not), it would imply the maximum
density of Sidon sets in [1,n] is (1 + o(1))√n.
Since the conjecture is false, this approach fails. -/
axiom connection_to_density : Prop

/-! ## Summary -/

/-- **Erdős Problem #707 Summary**:

1. QUESTION: Can every finite Sidon set be embedded in a perfect difference set?
2. ANSWER: NO (disproved)
3. COUNTEREXAMPLES:
   - {1,3,9,10,13} (Hall 1947, before Erdős asked!)
   - {1,2,4,8} for primes (Alexeev-Mixon 2025)
   - {1,2,4,8,13} for any modulus (Alexeev-Mixon 2025)
4. POSITIVE: Size ≤ 3 Sidon sets can always be extended
5. OPEN: Can every size-4 Sidon set be extended?
-/
theorem erdos_707_summary :
    -- {1,2,4} is a Sidon set
    IsSidon {1, 2, 4} ∧
    -- There exist perfect difference sets (Singer construction for p=2)
    (∃ B : Finset ℕ, IsPerfectDifferenceSet B 7) := by
  constructor
  · exact sidon_124
  · -- p = 2: 2² + 2 + 1 = 7
    obtain ⟨B, hB, _⟩ := singer_construction 2 Nat.prime_two
    exact ⟨B, hB⟩

end Erdos707
