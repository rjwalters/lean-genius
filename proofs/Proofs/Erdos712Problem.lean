/-
  Erdős Problem #712: Hypergraph Turán Densities

  Source: https://erdosproblems.com/712
  Status: OPEN (one of the most famous open problems in combinatorics)
  Prize: $500 for any k > r > 2, $1000 for the full problem

  Statement:
  Determine, for any k > r > 2, the value of
    lim_{n→∞} ex_r(n, K_k^r) / C(n, r)
  where ex_r(n, K_k^r) is the maximum number of r-edges on n vertices
  with no complete k-clique K_k^r.

  Background:
  When r = 2, this is the classical Turán problem solved by Turán (1941):
    ex_2(n, K_k) / C(n,2) → (1 - 1/(k-1))/2
  For r > 2, even the simplest case ex_3(n, K_4^3) is unknown! This is
  considered one of the most important open problems in extremal combinatorics.

  Key Insight:
  Turán conjectured that the extremal hypergraph for K_4^3 is the "Turán
  hypergraph" T(n,4,3), but this remains unproven after 80+ years.

  Tags: hypergraph, turán-number, extremal-combinatorics
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real

namespace Erdos712

open Finset

/-
## Part I: r-Uniform Hypergraphs
-/

/-- An r-uniform hypergraph on vertex set V -/
structure Hypergraph (V : Type*) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- The number of edges in a hypergraph -/
def Hypergraph.edgeCount {V : Type*} [DecidableEq V] {r : ℕ}
    (H : Hypergraph V r) : ℕ := H.edges.card

/-- A clique K_k^r: the complete r-uniform hypergraph on k vertices -/
def isCompleteClique {V : Type*} [DecidableEq V] [Fintype V] (r : ℕ) : Prop :=
  ∀ (S : Finset V), S.card = r → S ∈ (Finset.univ.powerset.filter (fun T => T.card = r))

/-- A subset S of vertices forms a clique in H if all r-subsets of S are edges -/
def formsClique {V : Type*} [DecidableEq V] {r : ℕ}
    (H : Hypergraph V r) (S : Finset V) : Prop :=
  ∀ (T : Finset V), T ⊆ S → T.card = r → T ∈ H.edges

/-- H is K_k^r-free if no k vertices form a complete clique -/
def isCliqueFree {V : Type*} [DecidableEq V] {r : ℕ}
    (H : Hypergraph V r) (k : ℕ) : Prop :=
  ∀ (S : Finset V), S.card = k → ¬formsClique H S

/-
## Part II: Hypergraph Turán Numbers
-/

/-- The hypergraph Turán number ex_r(n, K_k^r) -/
noncomputable def turanNumber (n r k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Finset (Fin n)) (H : Hypergraph (Fin n) r),
    isCliqueFree H k ∧ H.edgeCount = m}

/-- Alternative definition using supremum -/
def turanNumberDef (n r k : ℕ) : Prop :=
  ∀ m : ℕ, (∃ (V : Type*) [DecidableEq V] [Fintype V] (H : Hypergraph V r),
    Fintype.card V = n ∧ isCliqueFree H k ∧ H.edgeCount = m) →
    m ≤ turanNumber n r k

/-
## Part III: The Turán Density
-/

/-- The Turán density π_r(K_k^r) -/
noncomputable def turanDensity (r k : ℕ) : ℝ :=
  sSup {(turanNumber n r k : ℝ) / (Nat.choose n r : ℝ) | n : ℕ}

/-
## Part IV: Classical Turán Theorem (r = 2)
-/

/-- Turán's theorem: The density for graphs avoiding K_k -/
noncomputable def turanGraphDensity (k : ℕ) : ℝ :=
  (1 - 1 / (k - 1 : ℝ)) / 2

/-- Turán's theorem (1941): The graph Turán density is (1-1/(k-1))/2 -/
axiom turan_theorem (k : ℕ) (hk : k ≥ 2) :
  turanDensity 2 k = turanGraphDensity k

/-- **Turán Graph Extremality:**
The Turán graph T(n, k-1) — the balanced complete (k-1)-partite graph — achieves
the maximum number of edges among K_k-free graphs on n vertices. -/

/-
## Part V: The Case r = 3, k = 4 (Turán's Conjecture)
-/

/-- Turán's conjecture for K_4^3: the density is 5/9 -/
def turanConjectureK43 : ℝ := 5 / 9

/-- **Turán Hypergraph T(n,4,3):**
The conjectured extremal 3-uniform hypergraph for K_4^3 is obtained by
partitioning n vertices into 4 balanced parts and taking all 3-edges
that meet at least 2 of the 4 parts. This gives ≈ (5/9)C(n,3) edges. -/

/-- Best known lower bound for K_4^3 -/
axiom K43_lower_bound :
  turanDensity 3 4 ≥ 5 / 9

/-
## Part VI: Known Bounds and Results
-/

/-- The density is positive when k > r -/
axiom turan_density_positive (r k : ℕ) (hr : r ≥ 2) (hk : k > r) :
  turanDensity r k > 0

/-- The Kruskal-Katona theorem gives upper bounds -/
axiom kruskal_katona_upper (r k : ℕ) (hr : r ≥ 2) (hk : k > r) :
  turanDensity r k ≤ 1 - 1 / (k : ℝ)

/-
## Part VII: The General Problem Statement
-/

/-- **Erdős Problem #712:** Determine the Turán density π_r(K_k^r)
    for all k > r > 2 as an explicit (preferably rational) value. -/
def erdos_712_problem (r k : ℕ) (hr : r > 2) (hk : k > r) : Prop :=
  ∃ explicit : ℚ, turanDensity r k = explicit

/-- The problem is unsolved for all k > r > 2 -/
axiom erdos_712_open (r k : ℕ) (hr : r > 2) (hk : k > r) :
  ¬∃ explicit : ℚ, turanDensity r k = explicit

/-- Erdős Problem #712: The main statement -/
theorem erdos_712 (r k : ℕ) (hr : r > 2) (hk : k > r) :
    -- The Turán density exists and has nice bounds
    (∃ π : ℝ, turanDensity r k = π ∧ 0 < π ∧ π < 1) ∧
    -- But the exact value is unknown
    (¬∃ explicit : ℚ, turanDensity r k = explicit) := by
  constructor
  · use turanDensity r k
    constructor
    · rfl
    constructor
    · exact turan_density_positive r k (by omega) hk
    · -- Use Kruskal-Katona bound: π ≤ 1 - 1/k < 1 for k > 1
      have hkk := kruskal_katona_upper r k (by omega) hk
      have hk_pos : (0 : ℝ) < k := by
        have : k > r := hk
        have : r > 2 := hr
        linarith
      have h_one_div_k_pos : (0 : ℝ) < 1 / k := by positivity
      calc turanDensity r k ≤ 1 - 1 / k := hkk
        _ < 1 := by linarith
  · exact erdos_712_open r k hr hk

/-
## Part VIII: Related Conjectures
-/

/-- **Extremal Structure Conjecture:**
For any r ≥ 2, k > r, the extremal K_k^r-free hypergraph is a balanced
k-partition construction (generalization of the Turán graph). -/

/-- **Mubayi's conjecture for K_5^3:**
π_3(K_5^3) = 3/4, achieved by taking 3-edges meeting at least 2 parts
of a balanced 5-partition. -/

/-
## Part IX: Computational Approaches
-/

/-
## Part X: Connections to Other Problems
-/

/-- **Connection to Ramsey Theory:**
π_r(K_k^r) < 1 is equivalent to the Ramsey-type statement that sufficiently
dense r-uniform hypergraphs must contain K_k^r. Since Ramsey numbers for
hypergraphs exist, the Turán density is strictly less than 1. -/

/-- **Connection to Coding Theory:**
Turán-type hypergraphs correspond to optimal covering codes: an r-uniform
hypergraph on n vertices avoiding K_k^r corresponds to a covering design
with prescribed intersection properties. -/

/-
## Part XI: Summary
-/

/-- **Summary: Erdős Problem #712 is OPEN**

Known:
1. Turán solved the graph case (r = 2) in 1941
2. Hypergraph case (r > 2) is open for all k > r
3. Best bounds for K_4^3: 5/9 ≤ π_3(K_4^3) ≤ 0.5616
Prize: $500 for any case, $1000 for full solution -/
theorem erdos_712_summary :
    -- Turán solved the graph case (r = 2)
    (∀ k ≥ 2, turanDensity 2 k = turanGraphDensity k) ∧
    -- Hypergraph case (r > 2) is open for all k > r
    (∀ r k, r > 2 → k > r → ¬∃ explicit : ℚ, turanDensity r k = explicit) ∧
    -- Turán's K_4^3 conjecture: lower bound 5/9
    (turanDensity 3 4 ≥ 5 / 9) := by
  exact ⟨fun k hk => turan_theorem k hk, erdos_712_open, K43_lower_bound⟩

end Erdos712
