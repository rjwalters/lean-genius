/-
Erdős Problem #1105: Anti-Ramsey Numbers for Cycles and Paths

**Problem Statement (OPEN)**

The anti-Ramsey number AR(n,G) is the maximum number of colors in an edge-coloring
of K_n that contains no rainbow copy of G (where all edges have distinct colors).

**For cycles (C_k):** Is it true that
  AR(n, C_k) = ((k-2)/2 + 1/(k-1)) * n + O(1)?

**For paths (P_k):** If n ≥ k ≥ 5, is
  AR(n, P_k) = max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
where ℓ = ⌊(k-1)/2⌋, ε = 1 for odd k, ε = 2 for even k?

**Known Results:**
- Erdős, Simonovits, Sós (1975): AR(n, C₃) = n - 1
- Simonovits, Sós (1984): Path formula for n ≥ ck²
- Yuan (2021): Announced proof for all n ≥ k ≥ 5

**Status:** OPEN

**Reference:** Erdős, Simonovits, Sós (1975) - foundational anti-Ramsey theory

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Finset BigOperators

namespace Erdos1105

/-!
# Part 1: Basic Definitions

Define graphs, edge-colorings, and rainbow subgraphs.
-/

-- Simple graph on n vertices (labeled 0 to n-1)
abbrev SimpleGraph (n : ℕ) := Fin n → Fin n → Prop

-- Edge set of a simple graph
def EdgeSet (n : ℕ) (G : SimpleGraph n) : Set (Fin n × Fin n) :=
  {e | e.1 < e.2 ∧ G e.1 e.2}

-- Complete graph K_n
def CompleteGraph (n : ℕ) : SimpleGraph n :=
  fun i j => i ≠ j

-- Number of edges in K_n is C(n,2)
def numEdgesKn (n : ℕ) : ℕ := n.choose 2

-- An edge-coloring assigns colors to edges
def EdgeColoring (n : ℕ) (c : ℕ) := (Fin n × Fin n) → Fin c

-- Number of colors used in a coloring
noncomputable def numColors (n : ℕ) (coloring : (Fin n × Fin n) → ℕ) : ℕ :=
  (Finset.image coloring (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2))).card

/-!
# Part 2: Paths and Cycles

Define the path P_k and cycle C_k on k vertices.
-/

-- Path on k vertices: edges {0,1}, {1,2}, ..., {k-2, k-1}
def PathGraph (k : ℕ) : SimpleGraph k :=
  fun i j => (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)

-- Cycle on k vertices: path plus edge {0, k-1}
def CycleGraph (k : ℕ) : SimpleGraph k :=
  fun i j => PathGraph k i j ∨ (i.val = 0 ∧ j.val = k - 1) ∨ (j.val = 0 ∧ i.val = k - 1)

-- Number of edges in path P_k
def numEdgesPath (k : ℕ) : ℕ := k - 1

-- Number of edges in cycle C_k
def numEdgesCycle (k : ℕ) : ℕ := k

/-!
# Part 3: Rainbow Subgraphs

A subgraph is rainbow if all its edges have distinct colors.
-/

-- A copy of H in G is a subset of vertices isomorphic to H
structure GraphEmbedding (n k : ℕ) (H : SimpleGraph k) where
  vertices : Fin k → Fin n
  injective : Function.Injective vertices
  preserves_edges : ∀ i j, H i j → (CompleteGraph n) (vertices i) (vertices j)

-- Edges of an embedded copy
def embeddedEdges (n k : ℕ) (H : SimpleGraph k) (emb : GraphEmbedding n k H) :
    Set (Fin n × Fin n) :=
  {e | ∃ i j : Fin k, H i j ∧ i < j ∧ e = (emb.vertices i, emb.vertices j)}

-- A copy is rainbow if all edge colors are distinct
def IsRainbow (n : ℕ) (coloring : (Fin n × Fin n) → ℕ)
    (k : ℕ) (H : SimpleGraph k) (emb : GraphEmbedding n k H) : Prop :=
  ∀ e₁ e₂ : Fin k × Fin k, H e₁.1 e₁.2 → H e₂.1 e₂.2 →
    e₁ ≠ e₂ →
    coloring (emb.vertices e₁.1, emb.vertices e₁.2) ≠
    coloring (emb.vertices e₂.1, emb.vertices e₂.2)

-- A coloring avoids rainbow H if no embedded copy is rainbow
def AvoidsRainbow (n : ℕ) (coloring : (Fin n × Fin n) → ℕ)
    (k : ℕ) (H : SimpleGraph k) : Prop :=
  ∀ emb : GraphEmbedding n k H, ¬IsRainbow n coloring k H emb

/-!
# Part 4: Anti-Ramsey Numbers

AR(n, G) is the max colors in a rainbow-G-free coloring of K_n.
-/

-- The anti-Ramsey number
noncomputable def antiRamsey (n k : ℕ) (H : SimpleGraph k) : ℕ :=
  sSup {c : ℕ | ∃ coloring : (Fin n × Fin n) → ℕ,
    numColors n coloring = c ∧ AvoidsRainbow n coloring k H}

-- AR(n, C_k) for cycles
noncomputable def arCycle (n k : ℕ) : ℕ := antiRamsey n k (CycleGraph k)

-- AR(n, P_k) for paths
noncomputable def arPath (n k : ℕ) : ℕ := antiRamsey n k (PathGraph k)

/-!
# Part 5: The Cycle Conjecture

Conjecture: AR(n, C_k) = ((k-2)/2 + 1/(k-1)) * n + O(1)
-/

-- The conjectured coefficient for cycles
noncomputable def cycleCoeff (k : ℕ) : ℝ :=
  (k - 2 : ℝ) / 2 + 1 / (k - 1 : ℝ)

-- The cycle conjecture (asymptotic form)
def CycleConjecture : Prop :=
  ∀ k ≥ 3, ∃ C : ℝ, ∀ n : ℕ, n ≥ k →
    |((arCycle n k : ℝ) - cycleCoeff k * n)| ≤ C

-- Known: AR(n, C_3) = n - 1
axiom ar_triangle : ∀ n ≥ 3, arCycle n 3 = n - 1

-- Coefficient for k=3: (3-2)/2 + 1/(3-1) = 1/2 + 1/2 = 1
-- So AR(n, C_3) ≈ n, which matches n - 1

/-!
# Part 6: The Path Conjecture

Conjecture: AR(n, P_k) = max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
where ℓ = ⌊(k-1)/2⌋, ε = 1 for odd k, ε = 2 for even k.
-/

-- The ℓ parameter for paths
def pathL (k : ℕ) : ℕ := (k - 1) / 2

-- The ε parameter (1 for odd k, 2 for even k)
def pathEpsilon (k : ℕ) : ℕ := if k % 2 = 1 then 1 else 2

-- First term in the path formula
def pathTerm1 (k : ℕ) : ℕ := (k - 2).choose 2 + 1

-- Second term in the path formula
def pathTerm2 (n k : ℕ) : ℕ :=
  let ℓ := pathL k
  (ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + pathEpsilon k

-- Conjectured exact formula for AR(n, P_k)
def pathFormula (n k : ℕ) : ℕ := max (pathTerm1 k) (pathTerm2 n k)

-- The path conjecture
def PathConjecture : Prop :=
  ∀ n k : ℕ, n ≥ k → k ≥ 5 → arPath n k = pathFormula n k

-- Simonovits-Sós (1984): holds for n ≥ ck²
axiom simonovits_sos_path : ∃ c : ℕ, ∀ n k : ℕ, n ≥ c * k^2 → k ≥ 5 →
  arPath n k = pathFormula n k

-- Yuan (2021): announced full proof
axiom yuan_path_announced : PathConjecture

/-!
# Part 7: Lower and Upper Bounds

General bounds on anti-Ramsey numbers.
-/

-- Lower bound: AR(n, G) ≥ |E(G)| - 1 (need |E(G)| - 1 edges same color)
axiom ar_lower_bound : ∀ (n k : ℕ) (H : SimpleGraph k),
  antiRamsey n k H ≥ 1  -- Simplified; actual bound depends on H

-- Upper bound: AR(n, G) ≤ |E(K_n)| = C(n,2)
theorem ar_upper_bound (n k : ℕ) (H : SimpleGraph k) :
    antiRamsey n k H ≤ numEdgesKn n := by
  sorry -- Each edge can have its own color at most

-- Monotonicity in n
axiom ar_mono_n : ∀ (n₁ n₂ k : ℕ) (H : SimpleGraph k),
  n₁ ≤ n₂ → antiRamsey n₁ k H ≤ antiRamsey n₂ k H

/-!
# Part 8: Connection to Turán Numbers

Anti-Ramsey numbers relate to extremal graph theory.
-/

-- Turán number ex(n, H): max edges in H-free graph on n vertices
noncomputable def turan (n k : ℕ) (H : SimpleGraph k) : ℕ :=
  sSup {e : ℕ | ∃ G : SimpleGraph n,
    (∀ emb : GraphEmbedding n k H, False) ∧ e = (Finset.univ.filter
      (fun p : Fin n × Fin n => p.1 < p.2 ∧ G p.1 p.2)).card}

-- AR(n, H) ≥ ex(n, H) + 1 (give H-free graph rainbow, one color for complement)
axiom ar_turan_lower : ∀ (n k : ℕ) (H : SimpleGraph k),
  n ≥ k → antiRamsey n k H ≥ turan n k H + 1

-- Ramsey vs Anti-Ramsey: different extremal questions about colorings

/-!
# Part 9: Special Cases

Known exact values and special cases.
-/

-- AR(n, C_3) = n - 1 (Erdős-Simonovits-Sós 1975)
-- Already stated above as ar_triangle

-- AR(n, P_3) = 1 (trivial: any 2-coloring avoids rainbow path)
axiom ar_path_3 : ∀ n ≥ 3, arPath n 3 = 1

-- AR(n, K_3) = n - 1 (same as cycle)
axiom ar_k3 : ∀ n ≥ 3, antiRamsey n 3 (CompleteGraph 3) = n - 1

/-!
# Part 10: Problem Status

The problem remains OPEN for general cycles and the full path range.
-/

-- The problem is open
def erdos_1105_status : String := "OPEN"

-- Main formal statement for cycles
theorem erdos_1105_cycle_statement :
    CycleConjecture ↔
    ∀ k ≥ 3, ∃ C : ℝ, ∀ n : ℕ, n ≥ k →
      |((arCycle n k : ℝ) - cycleCoeff k * n)| ≤ C := by
  rfl

-- Main formal statement for paths
theorem erdos_1105_path_statement :
    PathConjecture ↔
    ∀ n k : ℕ, n ≥ k → k ≥ 5 → arPath n k = pathFormula n k := by
  rfl

/-!
# Summary

**Problem:** Determine exact formulas for anti-Ramsey numbers AR(n, C_k) and AR(n, P_k).

**Known:**
- AR(n, C_3) = n - 1 (Erdős-Simonovits-Sós 1975)
- Path formula for n ≥ ck² (Simonovits-Sós 1984)
- Yuan (2021) announced proof for all n ≥ k ≥ 5

**Open:**
- General cycle formula for all k
- Full verification of path formula

**Difficulty:** Requires careful analysis of rainbow-free colorings and extremal structures.
-/

end Erdos1105
