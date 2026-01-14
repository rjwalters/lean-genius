/-
Erdős Problem #71: Arithmetic Progressions of Cycle Lengths

For every infinite arithmetic progression P containing even numbers, is there
a constant c = c(P) such that every graph with average degree at least c
contains a cycle whose length is in P?

**Status**: SOLVED (Bollobás 1977)

**Answer**: YES. For any arithmetic progression P = {a, a+d, a+2d, ...} with
a even (or d even), there exists c(P) such that graphs with average degree ≥ c
contain a cycle of length in P.

**Open Question**: The optimal dependence of c(P) on P is unknown.

**Prize**: None listed

Reference: https://erdosproblems.com/71
Bollobás (1977): Original proof
Erdős-Burr: Original conjecture (credited in [Er82e])
-/

import Mathlib

open Finset
open scoped BigOperators

namespace Erdos71

/-!
## Background

This problem connects graph density to the existence of cycles of specific lengths.

An arithmetic progression P = {a, a+d, a+2d, ...} contains even numbers if either:
- a is even, or
- d is even (so every other term is even)

The conjecture (now theorem) states that high average degree forces cycles
whose lengths lie in any such progression.

This is related to the Bondy-Simonovits theorem and other results about
cycle lengths in dense graphs.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Core Definitions
-/

/-- An arithmetic progression starting at a with common difference d. -/
def ArithProg (a d : ℕ) : Set ℕ := { n | ∃ k : ℕ, n = a + k * d }

/-- An arithmetic progression {a, a+d, a+2d, ...} contains even numbers iff
    either a is even, or d is odd (so elements alternate parity).

    Equivalently: the progression avoids all evens iff a is odd AND d is even
    (giving a, a+d, a+2d, ... all congruent to a mod 2, hence all odd). -/
def ArithProg.containsEven (a d : ℕ) : Prop :=
  Even a ∨ Odd d

/-- Membership in an arithmetic progression. -/
theorem mem_arithProg_iff (a d n : ℕ) :
    n ∈ ArithProg a d ↔ ∃ k : ℕ, n = a + k * d := Iff.rfl

/-- The first term a is always in the progression (k = 0). -/
theorem first_mem_arithProg (a d : ℕ) : a ∈ ArithProg a d :=
  ⟨0, by ring⟩

/-- If d > 0, the progression is infinite.

    Proof: The progression contains a + k*d for all k ∈ ℕ, which is unbounded. -/
axiom arithProg_infinite (a d : ℕ) (hd : d > 0) : Set.Infinite (ArithProg a d)

/-!
## Graph Definitions
-/

/-- Cyclic successor in Fin k. -/
def Fin.succMod {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

/-- A graph contains a cycle of length k ≥ 3. -/
def ContainsCycleLength (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (hk : k ≥ 3) (vs : Fin k → V), Function.Injective vs ∧
    ∀ i : Fin k, G.Adj (vs i) (vs (Fin.succMod (by omega : 0 < k) i))

/-- The set of cycle lengths in a graph. -/
def CycleLengths (G : SimpleGraph V) : Set ℕ :=
  { k | ContainsCycleLength G k }

/-- Number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- Average degree of a graph: 2|E|/|V|. -/
noncomputable def avgDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  if Fintype.card V = 0 then 0
  else 2 * edgeCount G / Fintype.card V

/-!
## The Main Theorem (Bollobás 1977)

For any arithmetic progression P = {a, a+d, a+2d, ...} containing even numbers,
there exists a constant c(P) such that every graph with average degree ≥ c
contains a cycle whose length is in P.
-/

/--
**Bollobás's Theorem (1977)**

For any arithmetic progression P containing even numbers, there exists c(P)
such that every graph with average degree ≥ c contains a cycle of length in P.

This is the positive resolution of Erdős-Burr's conjecture.
-/
axiom bollobas_theorem (a d : ℕ) (ha : a ≥ 3) (hd : d > 0)
    (heven : ArithProg.containsEven a d) :
    ∃ c : ℚ, c > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      avgDegree G ≥ c →
      ∃ k ∈ ArithProg a d, ContainsCycleLength G k

/--
**Corollary**: For P = {4, 6, 8, ...} (all even numbers ≥ 4), high average
degree implies an even cycle.
-/
theorem even_cycles_from_high_degree :
    ∃ c : ℚ, c > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      avgDegree G ≥ c →
      ∃ k, Even k ∧ k ≥ 4 ∧ ContainsCycleLength G k := by
  -- Apply Bollobás with a = 4, d = 2
  obtain ⟨c, hc_pos, hc⟩ := bollobas_theorem 4 2 (by norm_num) (by norm_num)
    (Or.inl ⟨2, rfl⟩)
  refine ⟨c, hc_pos, fun V _ _ G _ havg => ?_⟩
  obtain ⟨k, hk_mem, hk_cycle⟩ := hc V G havg
  obtain ⟨m, hm⟩ := hk_mem
  refine ⟨k, ?_, ?_, hk_cycle⟩
  · -- k is even: k = 4 + 2m
    use 2 + m
    omega
  · -- k ≥ 4
    omega

/-!
## The Open Question: Optimal Constants

The best dependence of c(P) on the progression P = {a, a+d, ...} is unknown.

For specific progressions, bounds are known:
- P = {even numbers}: c ~ constant (from Bondy-Simonovits)
- General P: c grows with a and d, but optimal rate unclear
-/

/--
**Open Problem**: What is the optimal growth rate of c(P) as a function of
the first term a and common difference d?

Known: c(P) exists for all valid P
Unknown: Tight bounds on c(P)
-/
def optimalConstantQuestion : Prop :=
  ∃ f : ℕ → ℕ → ℚ, ∀ a d : ℕ, a ≥ 3 → d > 0 → ArithProg.containsEven a d →
    (∀ (V : Type*) [Fintype V] [DecidableEq V]
       (G : SimpleGraph V) [DecidableRel G.Adj],
       avgDegree G ≥ f a d →
       ∃ k ∈ ArithProg a d, ContainsCycleLength G k) ∧
    -- f is "optimal" in some sense (this would need precise formulation)
    True

/-!
## Related Results
-/

/-- Bondy-Simonovits: High minimum degree implies cycles of consecutive even lengths. -/
axiom bondy_simonovits (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (d : ℕ) (hd : d ≥ 2) :
    (∀ v : V, d ≤ (G.neighborFinset v).card) →
    ∀ k, Even k → 4 ≤ k → k ≤ 2 * d → ContainsCycleLength G k

/-- High average degree implies high minimum degree in a subgraph. -/
axiom avg_to_min_degree (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    (avgDegree G : ℚ) ≥ 2 * d →
    ∃ (S : Finset V), S.Nonempty ∧
      ∀ v ∈ S, d ≤ ((G.neighborFinset v).filter (· ∈ S)).card

/-!
## Why Even Numbers Matter

The condition that P contains even numbers is necessary. Consider:

- P = {3, 7, 11, 15, ...} (odd numbers ≡ 3 mod 4)
- Bipartite graphs have arbitrarily high average degree but NO odd cycles
- So for odd-only progressions, no constant c exists

This is why Erdős-Burr specifically required P to contain even numbers.
-/

/-- Bipartite graphs have no odd cycles.

    Proof: Let G be bipartite with parts A and B (2-coloring).
    In any cycle v₀ → v₁ → ... → vₖ₋₁ → v₀, vertices alternate between A and B.
    So vᵢ ∈ A iff i is even. For the cycle to close (v₀ adjacent to vₖ₋₁),
    we need v₀ and vₖ₋₁ in different parts. Since v₀ ∈ A (wlog),
    we need vₖ₋₁ ∈ B, i.e., k-1 is odd, i.e., k is even.

    This is a classical result; we state it as an axiom. -/
axiom bipartite_no_odd_cycles (G : SimpleGraph V) (hG : G.IsBipartite) :
    ∀ k, Odd k → ¬ContainsCycleLength G k

/-- The even condition is necessary: no constant works for odd-only progressions.

    Proof: Consider P = {3, 7, 11, ...} = {3 + 4k : k ∈ ℕ}, which consists entirely
    of odd numbers. We show no constant c works:

    For any c > 0, consider the complete bipartite graph K_{n,n} with n large
    enough that average degree 2n²/(2n) = n ≥ c. This graph:
    - Has average degree n (arbitrarily large)
    - Is bipartite, so contains only even-length cycles
    - Therefore contains no cycles of length in P = {3, 7, 11, ...}

    Thus for odd-only progressions, the Erdős-Burr conjecture fails.
    This is why the "contains even numbers" condition is essential. -/
axiom even_condition_necessary :
    ∃ (a d : ℕ), a ≥ 3 ∧ d > 0 ∧ ¬ArithProg.containsEven a d ∧
      ¬∃ c : ℚ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        avgDegree G ≥ c →
        ∃ k ∈ ArithProg a d, ContainsCycleLength G k

/-!
## Special Cases
-/

/-- For P = {4, 8, 12, ...} (multiples of 4 ≥ 4). -/
theorem multiples_of_four :
    ∃ c : ℚ, c > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      avgDegree G ≥ c →
      ∃ k, 4 ∣ k ∧ k ≥ 4 ∧ ContainsCycleLength G k := by
  obtain ⟨c, hc_pos, hc⟩ := bollobas_theorem 4 4 (by norm_num) (by norm_num)
    (Or.inl ⟨2, rfl⟩)
  refine ⟨c, hc_pos, fun V _ _ G _ havg => ?_⟩
  obtain ⟨k, ⟨m, hm⟩, hk_cycle⟩ := hc V G havg
  refine ⟨k, ?_, ?_, hk_cycle⟩
  · -- k = 4 + 4m is divisible by 4
    use 1 + m
    omega
  · omega

/-!
## Summary

**Problem Status: SOLVED**

Erdős Problem 71 asked whether high average degree forces cycles whose lengths
lie in any arithmetic progression containing even numbers.

**Resolution**: Bollobás (1977) proved the affirmative answer.

**Key insight**: The even condition is necessary because bipartite graphs
(which have no odd cycles) can have arbitrarily high average degree.

**Open Question**: The optimal dependence c(P) on the progression P is unknown.

References:
- Bollobás (1977): Original proof
- Erdős-Burr: Original conjecture
- Bondy-Simonovits: Related results on cycle lengths
-/

end Erdos71
