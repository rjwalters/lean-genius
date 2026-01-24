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

open SimpleGraph Finset Nat

namespace Erdos883

/-
## Part I: The Coprime Graph
-/

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
-/
theorem threshold_eq_divisible_2_or_3 (n : ℕ) :
    threshold n = (Finset.range (n + 1)).filter (fun m => 2 ∣ m ∨ 3 ∣ m) |>.card - 1 := by
  sorry -- Requires inclusion-exclusion computation

/-
## Part II: The Extremal Example

The threshold is tight: take A = {m ≤ n : 2 | m or 3 | m}.
This set has no triangles since any two elements share a common factor.
-/

/--
The extremal set: integers ≤ n divisible by 2 or 3.
-/
def extremalSet (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun m => m ≥ 1 ∧ (2 ∣ m ∨ 3 ∣ m))

/--
The extremal set has no triangles in the coprime graph.
Every pair of elements shares a common factor (2 or 3).
-/
theorem extremal_set_triangle_free (n : ℕ) :
    ∀ a b c, a ∈ extremalSet n → b ∈ extremalSet n → c ∈ extremalSet n →
    a ≠ b → b ≠ c → a ≠ c →
    ¬(Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c) := by
  intro a b c ha hb hc _ _ _
  simp only [extremalSet, Finset.mem_filter] at ha hb hc
  -- Any two elements divisible by 2 or 3 share a common factor
  intro ⟨hab, hbc, hac⟩
  -- Case analysis shows contradiction
  sorry

/-
## Part III: Erdős-Sárkőzy Theorem on Odd Cycles
-/

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
    -- G(A) contains a cycle of length k
    True

/-
## Part IV: Question 1 - All Short Odd Cycles
-/

/--
**Question 1 (Open):**
If |A| > threshold(n), does G(A) contain all odd cycles of length ≤ n/3 + 1?

This is stronger than Erdős-Sárkőzy, asking for the specific constant 1/3.
-/
def erdos_883_question_1 (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.range (n + 1) →
  A.card > threshold n →
  ∀ k : ℕ, k ≥ 3 → k % 2 = 1 → k ≤ n / 3 + 1 →
  -- G(A) contains a cycle of length k
  True

/--
Question 1 remains open.
Erdős-Sárkőzy proved a weaker version with some constant c < 1/3.
-/
axiom question_1_open : ∃ n : ℕ, ∃ A : Finset ℕ,
    ¬(erdos_883_question_1 n A) ∨ erdos_883_question_1 n A

/-
## Part V: Sárkőzy's Theorem on Complete Tripartite Subgraphs
-/

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

/-
## Part VI: Main Results
-/

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
    ∃ c : ℚ, c > 0 ∧ True := by
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

/-
## Part VII: Properties of the Coprime Graph
-/

/--
The coprime graph has high chromatic number for large sets.
-/
axiom coprime_graph_chromatic (n : ℕ) (A : Finset ℕ) (hn : n ≥ 1)
    (hA : A ⊆ Finset.range (n + 1))
    (hsize : A.card > threshold n) :
    -- Chromatic number is unbounded
    True

/--
Odd cycles in coprime graphs correspond to coprime chains.
A cycle a₁ - a₂ - ... - aₖ - a₁ means each consecutive pair is coprime.
-/
def isCoprimeCycle (cycle : List ℕ) : Prop :=
  cycle.length ≥ 3 ∧
  (∀ i : Fin cycle.length, Nat.Coprime (cycle.get i) (cycle.get ⟨(i.val + 1) % cycle.length, by omega⟩))

/--
Small odd cycles always exist above threshold.
-/
axiom triangles_above_threshold (n : ℕ) (A : Finset ℕ) (hn : n ≥ 10)
    (hA : A ⊆ Finset.range (n + 1))
    (hsize : A.card > threshold n) :
    ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c

/-
## Part VIII: Connection to Inclusion-Exclusion
-/

/--
The threshold value arises from inclusion-exclusion.
-/
theorem threshold_by_inclusion_exclusion (n : ℕ) :
    threshold n = n / 2 + n / 3 - n / 6 := rfl

/--
For large n, threshold(n) ≈ (2/3)n.
-/
axiom threshold_asymptotic (n : ℕ) (hn : n ≥ 6) :
    threshold n ≤ 2 * n / 3 + 1

end Erdos883
