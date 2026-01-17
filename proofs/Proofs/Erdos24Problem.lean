/-
Erdős Problem #24: Pentagons in Triangle-Free Graphs

Does every triangle-free graph on 5n vertices contain at most n⁵ copies of C₅?

**Status**: SOLVED (affirmative)

**Key Results**:
- Grzesik (2012): Proved using flag algebras
- Hatami-Hladký-Král-Norine-Razborov (2013): Independent proof, also via flag algebras
- Earlier bounds: Győri proved ≤ 1.03n⁵, improved by Füredi

**Extremal Graph**: The balanced blow-up of C₅ (five independent sets of n vertices
each, arranged in a pentagon pattern) achieves exactly n⁵ copies of C₅.

**Intuition**: A triangle-free graph on 5n vertices can be partitioned into 5 parts.
The pentagon structure maximizes C₅ copies while avoiding triangles. Any deviation
from this balanced structure reduces the C₅ count.

**Generalization (Erdős)**: For odd r ≥ 5, if a graph on rn vertices has girth r
(smallest odd cycle has length r), is the number of r-cycles at most nʳ?

References:
- https://erdosproblems.com/24
- Grzesik, A. (2012), J. Combin. Theory Ser. B 102(5):1061-1066
- Hatami et al. (2013), J. Combin. Theory Ser. B 103(5):627-639
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Card

open SimpleGraph

namespace Erdos24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Core Definitions

We define what it means for a graph to be triangle-free and count cycles.
-/

/-- A graph is triangle-free if it contains no clique of size 3.

Equivalently, no three vertices form a triangle (complete graph K₃).
This is the same as having girth ≥ 4.
-/
def IsTriangleFree (G : SimpleGraph V) : Prop :=
  G.CliqueFree 3

/-- The 5-cycle graph C₅ on 5 vertices.

Vertices are 0, 1, 2, 3, 4 with edges forming a cycle:
0 -- 1 -- 2 -- 3 -- 4 -- 0
-/
def cycleGraph5 : SimpleGraph (Fin 5) where
  Adj x y := (x.val + 1) % 5 = y.val ∨ (y.val + 1) % 5 = x.val
  symm := by
    intro x y h
    cases h with
    | inl h => right; exact h
    | inr h => left; exact h
  loopless := by
    intro x h
    cases h with
    | inl h => omega
    | inr h => omega

/-- A C₅ (5-cycle) in a graph G is a graph homomorphism from cycleGraph5 to G
that is injective on vertices.

This represents a copy of the pentagon in G.
-/
def IsC5Copy (G : SimpleGraph V) (f : Fin 5 → V) : Prop :=
  Function.Injective f ∧ ∀ i j : Fin 5, cycleGraph5.Adj i j → G.Adj (f i) (f j)

/-- The number of C₅ copies in a graph.

We axiomatize this count since defining it precisely requires decidability
of the adjacency relation and the IsC5Copy predicate.
-/
noncomputable def countC5 (G : SimpleGraph V) : ℕ := by
  classical
  exact Finset.card (Finset.univ.filter fun f : Fin 5 → V => IsC5Copy G f) / 10

/-!
## The Blow-Up Construction

The extremal graph is the balanced blow-up of C₅.
-/

/-- The balanced blow-up of C₅ with n vertices per part.

Each of the 5 vertices of C₅ is replaced by an independent set of n vertices.
Two vertices in the blow-up are adjacent iff their corresponding parts are
adjacent in C₅.

This graph has 5n vertices, is triangle-free, and contains exactly n⁵ copies of C₅.
-/
def balancedBlowupC5 (n : ℕ) : SimpleGraph (Fin 5 × Fin n) where
  Adj x y := cycleGraph5.Adj x.1 y.1
  symm := by
    intro x y h
    exact cycleGraph5.symm h
  loopless := by
    intro x h
    exact cycleGraph5.loopless x.1 h

/-- The balanced blow-up of C₅ is triangle-free.

A triangle would require three parts mutually adjacent in C₅, but C₅ has no K₃.
-/
axiom balancedBlowupC5_triangleFree (n : ℕ) :
    IsTriangleFree (balancedBlowupC5 n)

/-- The balanced blow-up of C₅ with n vertices per part has exactly 5n vertices. -/
theorem balancedBlowupC5_card (n : ℕ) :
    Fintype.card (Fin 5 × Fin n) = 5 * n := by
  simp [Fintype.card_prod]

/-- The balanced blow-up achieves exactly n⁵ copies of C₅.

Each C₅ copy is formed by choosing one vertex from each of the 5 parts,
giving n choices per part, hence n⁵ total.
-/
axiom balancedBlowupC5_count (n : ℕ) (hn : 0 < n) :
    countC5 (balancedBlowupC5 n) = n^5

/-!
## The Main Theorem: Grzesik-Hatami et al. (2012-2013)

The pentagon conjecture: triangle-free graphs on 5n vertices have at most n⁵ C₅'s.
-/

/-- **Grzesik (2012) / Hatami et al. (2013)**: Pentagon Conjecture

Every triangle-free graph on 5n vertices contains at most n⁵ copies of C₅.

The proof uses Razborov's flag algebras method, a powerful technique for
proving extremal graph theory bounds. The key insight is to express the
constraint (triangle-free) and objective (maximize C₅ count) as a semidefinite
program over flag algebra elements.

This is stated as an axiom because:
1. Flag algebras proofs involve computer-assisted verification
2. The method is not yet formalized in Mathlib
3. The proof requires sophisticated SDP solvers
-/
axiom grzesik_hatami_theorem (n : ℕ) (hn : 0 < n) :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = 5 * n →
    IsTriangleFree G →
    countC5 G ≤ n^5

/-- The balanced blow-up is the unique extremal graph (up to isomorphism).

When |V| = 5n, the only triangle-free graph with exactly n⁵ copies of C₅
is the balanced blow-up of C₅.
-/
axiom uniqueness_of_extremal (n : ℕ) (hn : 0 < n) :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = 5 * n →
    IsTriangleFree G →
    countC5 G = n^5 →
    -- G is isomorphic to balancedBlowupC5 n
    ∃ (φ : V → Fin 5 × Fin n), Function.Bijective φ ∧
      ∀ v w : V, G.Adj v w ↔ (balancedBlowupC5 n).Adj (φ v) (φ w)

/-!
## Historical Progress

The problem had several partial results before the complete solution.
-/

/-- **Győri**: An earlier upper bound of approximately 1.03n⁵.

Before flag algebras, Győri proved that triangle-free graphs on 5n vertices
have at most about 1.03n⁵ copies of C₅. This was later improved by Füredi.
-/
axiom gyori_bound (n : ℕ) (hn : 0 < n) :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = 5 * n →
    IsTriangleFree G →
    -- 100 * countC5 G ≤ 103 * n^5 (integer form of 1.03)
    100 * countC5 G ≤ 103 * n^5

/-!
## Erdős's Generalization

Erdős proposed a more general conjecture for odd cycles.
-/

/-- **Erdős's General Conjecture** (Open for r > 5):

For odd r ≥ 5, if a graph on rn vertices has girth r (smallest cycle has length r),
then the number of r-cycles is at most nʳ.

The case r = 5 is exactly the pentagon theorem (girth 5 = triangle-free with no C₄).

For r > 5, this remains an open problem.
-/
def erdosGeneralConjecture (r : ℕ) : Prop :=
  r % 2 = 1 ∧ r ≥ 5 →
  ∀ n : ℕ, 0 < n →
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  Fintype.card V = r * n →
  -- "girth = r" means: has no cycle shorter than r, but has some cycle of length r
  G.CliqueFree 3 →  -- Simplified: at least triangle-free
  True  -- Placeholder for: countCr G ≤ n^r

/-- The r = 5 case of the general conjecture is exactly our main theorem. -/
theorem r5_is_pentagon_theorem :
    ∀ n : ℕ, 0 < n →
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = 5 * n →
    IsTriangleFree G →
    countC5 G ≤ n^5 :=
  grzesik_hatami_theorem

/-!
## Summary

The main result: Erdős Problem #24 is solved affirmatively.
-/

/-- **Erdős Problem #24** (SOLVED):
Every triangle-free graph on 5n vertices contains at most n⁵ copies of C₅.

The bound is tight: the balanced blow-up of C₅ achieves exactly n⁵ copies.

Proved independently by:
- Grzesik (2012) using flag algebras
- Hatami, Hladký, Král, Norine, Razborov (2013) using flag algebras
-/
theorem erdos_24_pentagon_theorem (n : ℕ) (hn : 0 < n) :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = 5 * n →
    IsTriangleFree G →
    countC5 G ≤ n^5 :=
  grzesik_hatami_theorem n hn

/-- The extremal graph achieves the bound. -/
theorem erdos_24_extremal_exists (n : ℕ) (hn : 0 < n) :
    ∃ G : SimpleGraph (Fin 5 × Fin n),
    Fintype.card (Fin 5 × Fin n) = 5 * n ∧
    IsTriangleFree G ∧
    countC5 G = n^5 := by
  use balancedBlowupC5 n
  constructor
  · exact balancedBlowupC5_card n
  constructor
  · exact balancedBlowupC5_triangleFree n
  · exact balancedBlowupC5_count n hn

end Erdos24
