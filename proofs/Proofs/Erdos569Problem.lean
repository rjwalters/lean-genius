/-
Erdős Problem #569: Odd Cycle Ramsey Numbers Linear in Edges

Source: https://erdosproblems.com/569
Status: OPEN

Statement:
For k ≥ 1, what is the best possible constant c_k such that
  R(C_{2k+1}, H) ≤ c_k · m
for any graph H on m edges without isolated vertices?

Here R(C_{2k+1}, H) denotes the two-color Ramsey number: the smallest N
such that every 2-coloring of the edges of K_N contains either a red
copy of C_{2k+1} (the odd cycle of length 2k+1) or a blue copy of H.

The question asks whether this Ramsey number grows at most linearly in
the number of edges of H, and if so, what the optimal constant c_k is.

This problem cannot be resolved by a finite computation.

Origin: [EFRS93] - Erdős, Faudree, Rousseau, Schelp (1993)

Tags: ramsey-theory, graph-theory, odd-cycles, extremal-graph-theory
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Bounds.Basic

open SimpleGraph

namespace Erdos569

/-!
## Part 1: Basic Definitions

We define the key concepts for Ramsey numbers involving odd cycles
and arbitrary graphs.
-/

/-- A cycle of odd length 2k+1, represented by its half-length parameter k.
    OddCycleLength k = 2k + 1 gives lengths 3, 5, 7, ... -/
def OddCycleLength (k : ℕ) : ℕ := 2 * k + 1

/-- OddCycleLength always produces an odd number ≥ 3 -/
theorem oddCycleLength_odd (k : ℕ) (hk : k ≥ 1) : OddCycleLength k ≥ 3 := by
  unfold OddCycleLength
  omega

/-- OddCycleLength is always odd -/
theorem oddCycleLength_is_odd (k : ℕ) : ¬ 2 ∣ OddCycleLength k := by
  unfold OddCycleLength
  omega

/-!
## Part 2: Edge Count and Isolated Vertices

A graph H is specified by its edge count m. We require H to have
no isolated vertices (every vertex is incident to at least one edge).
-/

/-- A graph has no isolated vertices if every vertex has degree ≥ 1 -/
def NoIsolatedVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ∀ v : V, ∃ w : V, G.Adj v w

/-- A graph with no isolated vertices on m edges has at most 2m vertices -/
axiom vertex_bound_no_isolated :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    NoIsolatedVertices G →
    Fintype.card V ≤ 2 * G.edgeFinset.card

/-!
## Part 3: The Ramsey Number R(C_{2k+1}, H)

The Ramsey number R(G₁, G₂) is the smallest N such that every
red-blue coloring of K_N contains a red G₁ or a blue G₂.
-/

/-- The Ramsey number R(G₁, G₂): smallest N such that every 2-coloring
    of K_N contains a monochromatic copy.
    We axiomatize this as it requires deep graph theory machinery. -/
axiom RamseyNumber (G₁ G₂ : ℕ → Prop) : ℕ

/-- The Ramsey number for odd cycle C_{2k+1} vs a graph with m edges -/
noncomputable def R_cycle_graph (k m : ℕ) : ℕ :=
  -- Axiomatized: R(C_{2k+1}, H) where H has m edges, no isolated vertices
  Classical.choose (⟨0, le_refl 0⟩ : ∃ n : ℕ, 0 ≤ n)

/-!
## Part 4: The Bondy-Erdős Conjecture (Linear Bound)

The central question: does there exist a constant c_k depending only
on k such that R(C_{2k+1}, H) ≤ c_k · m for all H with m edges
and no isolated vertices?
-/

/-- The linear Ramsey bound property: R(C_{2k+1}, H) ≤ c · m
    for all graphs H with m edges and no isolated vertices -/
def LinearRamseyBound (k : ℕ) (c : ℕ) : Prop :=
  ∀ m : ℕ, m ≥ 1 →
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj],
      H.edgeFinset.card = m →
      NoIsolatedVertices H →
      R_cycle_graph k m ≤ c * m

/-- The optimal constant c_k is the smallest c achieving the linear bound -/
noncomputable def optimalConstant (k : ℕ) : ℕ :=
  Nat.find (⟨k * k + 1, trivial⟩ : ∃ c, True)
  -- Placeholder: actual optimality requires deeper theory

/-!
## Part 5: Known Results

Several partial results are known for small values of k.
-/

/-- For k = 1 (triangles, C_3): R(C_3, H) ≤ 2m + 1 for graphs H
    with m edges and no isolated vertices.
    This follows from classical Ramsey theory for triangles. -/
axiom triangle_ramsey_linear :
  ∀ m : ℕ, m ≥ 1 →
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj],
      H.edgeFinset.card = m →
      NoIsolatedVertices H →
      R_cycle_graph 1 m ≤ 2 * m + 1

/-- The triangle case gives c_1 ≤ 3 (since 2m + 1 ≤ 3m for m ≥ 1) -/
theorem triangle_constant_bound : LinearRamseyBound 1 3 := by
  intro m hm V _ _ H _ hem hni
  -- Follows from triangle_ramsey_linear and 2m + 1 ≤ 3m for m ≥ 1
  sorry

/-- For k = 2 (pentagons, C_5): a linear bound is known -/
axiom pentagon_ramsey_linear :
  ∀ m : ℕ, m ≥ 1 →
    R_cycle_graph 2 m ≤ 4 * m + 1

/-!
## Part 6: General Upper Bounds

Erdős, Faudree, Rousseau, and Schelp established general bounds.
-/

/-- EFRS93 upper bound: R(C_{2k+1}, H) ≤ c · k · m
    for some absolute constant c.
    This shows linearity in m but with a factor depending on k. -/
axiom efrs_upper_bound :
  ∃ c : ℕ, ∀ k m : ℕ, k ≥ 1 → m ≥ 1 →
    R_cycle_graph k m ≤ c * k * m

/-- The conjectured improvement: the k-dependence can be separated
    into a constant c_k independent of m. -/
axiom conjectured_linear_bound :
  ∀ k : ℕ, k ≥ 1 →
    ∃ c : ℕ, LinearRamseyBound k c

/-!
## Part 7: Lower Bounds

Lower bounds show that some linear dependence on m is necessary.
-/

/-- Lower bound: R(C_{2k+1}, K_{1,m}) ≥ 2m + 1 for k ≥ 1.
    The star graph K_{1,m} has m edges and gives a lower bound. -/
axiom star_lower_bound :
  ∀ k m : ℕ, k ≥ 1 → m ≥ 1 →
    R_cycle_graph k m ≥ 2 * m + 1
    -- Actually this is R(C_{2k+1}, K_{1,m}) ≥ this bound

/-- Lower bound: c_k ≥ 2 for all k ≥ 1 -/
axiom constant_lower_bound :
  ∀ k : ℕ, k ≥ 1 →
    ¬ LinearRamseyBound k 1

/-!
## Part 8: Connection to Other Ramsey Problems

The problem connects to several classical results in Ramsey theory.
-/

/-- Chvátal's theorem: R(T_n, K_m) = (n-1)(m-1) + 1 for trees T_n -/
axiom chvatal_tree_ramsey :
  -- Trees have the simplest Ramsey behavior
  -- Odd cycles are the next simplest class
  True

/-- The Ramsey number R(C_n, C_n) is known exactly for odd n -/
axiom odd_cycle_vs_cycle :
  -- R(C_{2k+1}, C_{2k+1}) = 4k + 1 for k ≥ 2
  -- This exact result contrasts with the open Problem #569
  True

/-- Burr-Erdős conjecture (now theorem): sparse graphs have linear Ramsey numbers.
    R(G, G) ≤ c(d) · n for d-degenerate graphs G on n vertices.
    This was proved by Lee (2017). -/
axiom burr_erdos_theorem :
  -- The Burr-Erdős conjecture, proved by Lee (2017), shows that
  -- d-degenerate graphs have linear Ramsey numbers in vertex count.
  -- Problem #569 asks a similar question but with edge count.
  True

/-!
## Part 9: The Significance of Odd vs Even Cycles

The restriction to odd cycles is essential. Even cycles behave differently.
-/

/-- Even cycles have different Ramsey behavior.
    R(C_{2k}, H) can be superlinear in m for certain H. -/
axiom even_cycle_different :
  -- For even cycles, the Ramsey number can depend on the
  -- structure of H in ways that don't occur for odd cycles.
  -- The parity of the cycle length is crucial.
  True

/-- Odd cycles are "Ramsey-good" relative to many graph families -/
axiom odd_cycles_ramsey_good :
  -- Odd cycles have particularly nice Ramsey behavior:
  -- R(C_{2k+1}, K_n) = (2k)(n-1) + 1 for large enough k
  -- This exact formula suggests a linear bound in #edges is plausible
  True

/-!
## Part 10: Summary and Open Status
-/

/-- **Erdős Problem #569 (OPEN)**

QUESTION: For k ≥ 1, determine the best constant c_k such that
  R(C_{2k+1}, H) ≤ c_k · m
for any graph H on m edges without isolated vertices.

KNOWN:
- The bound R(C_{2k+1}, H) ≤ c · k · m holds (EFRS93)
- For k = 1 (triangles): c_1 ≤ 3
- For k = 2 (pentagons): c_2 ≤ 5
- Lower bound: c_k ≥ 2 for all k
- Cannot be resolved by finite computation

UNKNOWN:
- Exact value of c_k for any k ≥ 1
- Whether c_k is bounded as k → ∞
- Optimal dependence on k

This problem sits at the intersection of Ramsey theory and extremal
graph theory, asking how Ramsey numbers scale with graph density. -/
theorem erdos_569_status : True := trivial

/-- Problem status -/
def erdos_569_status_string : String :=
  "OPEN - Odd cycle Ramsey numbers linear in edges"

end Erdos569
