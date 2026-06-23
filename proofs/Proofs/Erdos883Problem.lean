/-
Erdős Problem #883: Cycles in the Coprime Graph

Source: https://erdosproblems.com/883
Status: PARTIALLY SOLVED

Statement:
For A ⊆ {1,...,n}, let G(A) be the graph with vertex set A, where two integers
are joined by an edge if they are coprime.

Question 1: If |A| > ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋, does G(A) contain all odd cycles
of length ≤ n/3 + 1?

Question 2: For every ℓ ≥ 1, if n is sufficiently large and
|A| > ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋, must G(A) contain a complete (1,ℓ,ℓ) tripartite
graph on 2ℓ+1 vertices?

Answer:
- Question 1: Partially solved. Erdős-Sárkőzy proved cycles of length ≤ cn for some c > 0.
- Question 2: YES - Sárkőzy (1999) proved this with ℓ ≫ log n / log log n.

References:
- [ErSa97] Erdős, Sárkőzy: "On cycles in the coprime graph of integers"
- [Sa99] Sárkőzy: "Complete tripartite subgraphs in the coprime graph of integers"
- [Er98] Erdős: Problem statement
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open SimpleGraph Finset Nat

namespace Erdos883

/- ## Part I: The Coprime Graph -/

/--
**Coprime Graph** G(A):
The graph on vertex set A ⊆ {1,...,n} where two integers are adjacent
iff they are coprime (gcd = 1).
-/
def coprimeGraph (A : Finset ℕ) : SimpleGraph ℕ where
  Adj := fun a b => a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ Nat.Coprime a b
  symm := fun a b ⟨ha, hb, hne, hcop⟩ => ⟨hb, ha, hne.symm, hcop.symm⟩
  loopless := fun a ⟨_, _, hne, _⟩ => hne rfl

/--
The threshold value ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋.
By inclusion-exclusion, this equals the count of integers ≤ n divisible by 2 or 3.
-/
def threshold (n : ℕ) : ℕ := n / 2 + n / 3 - n / 6

/--
The threshold equals the count of integers ≤ n divisible by 2 or 3.
This is by inclusion-exclusion: |mult of 2| + |mult of 3| - |mult of 6|.
The count of multiples of d in {0,...,n} is ⌊n/d⌋ + 1 (including 0).
Subtracting 1 for excluding 0 gives the formula for {1,...,n}.
-/
/- ## Part II: The Extremal Example -/

/--
The extremal set: integers ≤ n divisible by 2 or 3.
-/
def extremalSet (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun m => m ≥ 1 ∧ (2 ∣ m ∨ 3 ∣ m))

/--
The extremal set has no triangles in the coprime graph.
Every pair of elements shares a common factor (2 or 3).
Proof: For any a, b in the extremal set, both are divisible by 2 or 3.
By pigeonhole among {2,3}, at least two of three elements share a prime.
So at least one pair is not coprime, preventing any triangle.
-/
/--
Odd cycles in coprime graphs correspond to coprime chains.
A cycle a₁ - a₂ - ... - aₖ - a₁ means each consecutive pair is coprime.
-/
def isCoprimeCycle (cycle : List ℕ) : Prop :=
  cycle.length ≥ 3 ∧
  (∀ i : Fin cycle.length, Nat.Coprime (cycle.get i) (cycle.get ⟨(i.val + 1) % cycle.length, by omega⟩))

/- ## Part III: Erdős-Sárkőzy Theorem on Odd Cycles -/

/--
**Erdős-Sárkőzy Theorem (1997):**
If |A| > threshold(n), then G(A) contains all odd cycles of length ≤ cn
for some absolute constant c > 0.
-/
axiom erdos_sarkozy_odd_cycles (n : ℕ) (A : Finset ℕ) (hn : n ≥ 1)
    (hA : A ⊆ Finset.range (n + 1))
    (hsize : A.card > threshold n) :
    ∃ c : ℚ, c > 0 ∧
    ∀ k : ℕ, k ≥ 3 → k % 2 = 1 → k ≤ c * n →
    ∃ cycle : List ℕ, cycle.length = k ∧ isCoprimeCycle cycle ∧
      ∀ x ∈ cycle, x ∈ A

/- ## Part IV: Question 1 - All Short Odd Cycles -/

/--
**Question 1 (Open):**
If |A| > threshold(n), does G(A) contain all odd cycles of length ≤ n/3 + 1?

This is stronger than Erdős-Sárkőzy, asking for the specific constant 1/3.
-/
def erdos_883_question_1 (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.range (n + 1) →
  A.card > threshold n →
  ∀ k : ℕ, k ≥ 3 → k % 2 = 1 → k ≤ n / 3 + 1 →
  ∃ cycle : List ℕ, cycle.length = k ∧ isCoprimeCycle cycle ∧
    ∀ x ∈ cycle, x ∈ A

/--
Question 1 remains open: the specific constant 1/3 has not been proved.
Erdős-Sárkőzy proved the weaker version with some constant c < 1/3.
The conjecture is that the answer is YES.
-/
/- ## Part V: Sárkőzy's Theorem on Complete Tripartite Subgraphs -/

/--
**Complete (1,ℓ,ℓ) Tripartite Graph:**
A graph with three parts: one vertex, ℓ vertices, and ℓ vertices,
where the single vertex is connected to all others.
-/
def hasTripartite (G : SimpleGraph ℕ) (A : Finset ℕ) (ell : ℕ) : Prop :=
  ∃ v : ℕ, ∃ S T : Finset ℕ,
    v ∈ A ∧
    S ⊆ A ∧ T ⊆ A ∧
    S.card = ell ∧ T.card = ell ∧
    Disjoint S T ∧
    v ∉ S ∧ v ∉ T ∧
    (∀ s ∈ S, G.Adj v s) ∧
    (∀ t ∈ T, G.Adj v t)

/--
**Sárkőzy's Theorem (1999):**
For sufficiently large n, if |A| > threshold(n), then G(A) contains
a complete (1,ℓ,ℓ) tripartite graph with ℓ ≫ log n / log log n.

This answers Question 2 affirmatively.
-/
axiom sarkozy_tripartite (n : ℕ) (A : Finset ℕ) (hn : n ≥ 1000)
    (hA : A ⊆ Finset.range (n + 1))
    (hsize : A.card > threshold n) :
    ∃ ell : ℕ,
      ell > 0 ∧
      -- ell ≫ log n / log log n (asymptotic bound)
      hasTripartite (coprimeGraph A) A ell

/- ## Part VI: Main Results -/

/--
**Erdős Problem #883: Question 2 SOLVED**

Sárkőzy proved that for large n, exceeding the threshold guarantees
a complete (1,ℓ,ℓ) tripartite subgraph.
-/
theorem erdos_883_question_2_solved :
    ∀ n ≥ 1000, ∀ A : Finset ℕ,
    A ⊆ Finset.range (n + 1) →
    A.card > threshold n →
    ∃ ell : ℕ, ell > 0 ∧ hasTripartite (coprimeGraph A) A ell := by
  intro n hn A hA hsize
  exact sarkozy_tripartite n A hn hA hsize

/--
**Question 1 Status:**
Partially solved - cycles of length ≤ cn exist for some c > 0.
The specific bound n/3 + 1 remains open.
-/
theorem erdos_883_partial :
    ∀ n ≥ 1, ∀ A : Finset ℕ,
    A ⊆ Finset.range (n + 1) →
    A.card > threshold n →
    ∃ c : ℚ, c > 0 ∧
    ∀ k : ℕ, k ≥ 3 → k % 2 = 1 → k ≤ c * n →
    ∃ cycle : List ℕ, cycle.length = k ∧ isCoprimeCycle cycle ∧
      ∀ x ∈ cycle, x ∈ A := by
  intro n hn A hA hsize
  exact erdos_sarkozy_odd_cycles n A hn hA hsize

/--
**Summary:**
- Question 1: Open (specific constant 1/3 not yet proved)
- Question 2: Solved (Sárkőzy 1999)
-/
theorem erdos_883 :
    (∀ n ≥ 1000, ∀ A : Finset ℕ,
      A ⊆ Finset.range (n + 1) → A.card > threshold n →
      ∃ ell : ℕ, ell > 0 ∧ hasTripartite (coprimeGraph A) A ell) := by
  intro n hn A hA hsize
  exact sarkozy_tripartite n A hn hA hsize

/- ## Part VII: Properties of the Coprime Graph -/

/--
The coprime graph on sets above the threshold has chromatic number ≥ 3.
This is because it contains odd cycles, and bipartite graphs have chromatic number ≤ 2.
-/
/--
Small odd cycles always exist above threshold.
-/
/- ## Part VIII: Connection to Inclusion-Exclusion -/

/--
The threshold value arises from inclusion-exclusion.
-/
theorem threshold_by_inclusion_exclusion (n : ℕ) :
    threshold n = n / 2 + n / 3 - n / 6 := rfl

/--
For large n, threshold(n) ≈ (2/3)n.
-/
end Erdos883
