/-!
# Erdős Problem 530: Maximum Sidon Subsets of Finite Sets

*Reference:* [erdosproblems.com/530](https://www.erdosproblems.com/530)

For a finite set `A ⊂ ℝ` of size `N`, let `ℓ(N)` denote the maximum size
of a Sidon subset of `A` (where `a + b = c + d` implies `{a,b} = {c,d}`).
Determine the order of growth of `ℓ(N)`.

Originally posed by Riddell (1969). Erdős proved `N^{1/3} ≪ ℓ(N) ≤ (1+o(1))N^{1/2}`.
Komlós, Sulyok, and Szemerédi improved the lower bound to `N^{1/2} ≪ ℓ(N)`.
The conjecture is that `ℓ(N) ~ N^{1/2}`.

This remains an open problem.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
## Section 1: Sidon set definition

A set `S` is *Sidon* (also called a B₂-set) if all pairwise sums `a + b`
with `a ≤ b` are distinct. Equivalently, `a + b = c + d` with `a,b,c,d ∈ S`
implies `{a,b} = {c,d}`.
-/

namespace Erdos530

open Finset

/-- A Finset of integers is Sidon if all pairwise sums are distinct:
    a + b = c + d with a ≤ b, c ≤ d implies a = c and b = d. -/
def IsSidon (S : Finset ℤ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- The empty set is Sidon. -/
theorem isSidon_empty : IsSidon ∅ := by
  intro a ha
  exact absurd ha (Finset.not_mem_empty a)

/-- Any singleton is Sidon. -/
theorem isSidon_singleton (x : ℤ) : IsSidon {x} := by
  intro a ha b hb c hc d hd hab hcd heq
  rw [Finset.mem_singleton] at ha hb hc hd
  exact ⟨by rw [ha, hc], by rw [hb, hd]⟩

/-!
## Section 2: Maximum Sidon subset size

For a finite set `A` of size `N`, `maxSidonSize A` is the maximum
cardinality of a Sidon subset of `A`.
-/

/-- The maximum size of a Sidon subset of A. -/
noncomputable def maxSidonSize (A : Finset ℤ) : ℕ :=
  (A.powerset.filter (fun S => IsSidon S)).sup Finset.card

/-!
## Section 3: Known bounds

The key results on `ℓ(N)`:
- Erdős: `N^{1/3} ≪ ℓ(N)` (lower bound)
- Trivially: `ℓ(N) ≤ (1 + o(1))N^{1/2}` (from {1,...,N})
- Komlós–Sulyok–Szemerédi: `N^{1/2} ≪ ℓ(N)` (improved lower bound)
-/

/-- Erdős's lower bound: every set of size N has a Sidon subset of
    size at least c · N^{1/3} for some absolute constant c. -/
axiom erdos_lower_bound :
  ∃ c : ℕ, c ≥ 1 ∧
    ∀ A : Finset ℤ, A.card ≥ 8 →
      maxSidonSize A * maxSidonSize A * maxSidonSize A ≥ c * A.card

/-- Komlós–Sulyok–Szemerédi improved lower bound: every set of size N
    has a Sidon subset of size at least c · N^{1/2}. -/
axiom komlos_sulyok_szemeredi :
  ∃ c : ℕ, c ≥ 1 ∧
    ∀ A : Finset ℤ, A.card ≥ 4 →
      maxSidonSize A * maxSidonSize A ≥ c * A.card

/-- Upper bound: the maximum Sidon subset of any set of size N
    has size at most (1 + o(1)) · N^{1/2}. For {1,...,N}, the
    Sidon set construction gives at most ~ N^{1/2} elements. -/
axiom sidon_upper_bound :
  ∀ A : Finset ℤ,
    maxSidonSize A * maxSidonSize A ≤ A.card * A.card

/-!
## Section 4: The main conjecture

Erdős conjectured that `ℓ(N) ~ N^{1/2}`, i.e., the lower and upper
bounds are of the same order.
-/

/-- Erdős Problem 530: The maximum Sidon subset size ℓ(N) satisfies
    c₁ · N^{1/2} ≤ ℓ(N) ≤ c₂ · N^{1/2} for absolute constants c₁, c₂. -/
def ErdosProblem530 : Prop :=
  ∃ c₁ c₂ : ℕ, c₁ ≥ 1 ∧ c₂ ≥ 1 ∧
    ∀ A : Finset ℤ, A.card ≥ 4 →
      maxSidonSize A * maxSidonSize A ≥ c₁ * A.card ∧
      maxSidonSize A * maxSidonSize A ≤ c₂ * A.card

/-!
## Section 5: Sidon set partition conjecture

Alon and Erdős conjectured that any set of size N can be partitioned
into at most (1 + o(1)) · N^{1/2} Sidon sets.
-/

/-- A partition of A into Sidon sets. -/
def IsSidonPartition (A : Finset ℤ) (parts : Finset (Finset ℤ)) : Prop :=
  (∀ P ∈ parts, IsSidon P) ∧
  (∀ P ∈ parts, P ⊆ A) ∧
  (∀ a ∈ A, ∃! P, P ∈ parts ∧ a ∈ P)

/-- Alon–Erdős conjecture: any set of N integers can be partitioned into
    at most c · N^{1/2} Sidon sets. -/
axiom alon_erdos_partition_conjecture :
  ∃ c : ℕ, c ≥ 1 ∧
    ∀ A : Finset ℤ, A.card ≥ 1 →
      ∃ parts : Finset (Finset ℤ),
        IsSidonPartition A parts ∧ parts.card * parts.card ≤ c * A.card

/-!
## Section 6: Connection to B₂-sets and additive combinatorics

Sidon sets are also called B₂-sets in the additive combinatorics literature.
The study of maximum Sidon subsets connects to the broader theory of
sum-free sets, Szemerédi's theorem, and additive number theory.
-/

/-- The number of distinct pairwise sums from a Sidon set S of size k
    is exactly k(k+1)/2 (all sums are distinct). -/
axiom sidon_sum_count (S : Finset ℤ) (hS : IsSidon S) :
  ((S ×ˢ S).filter (fun p => p.1 ≤ p.2)).image (fun p => p.1 + p.2)
    |>.card = S.card * (S.card + 1) / 2

end Erdos530
