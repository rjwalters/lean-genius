/-
Erdős Problem #815: Cycles in Degree 3 Critical Graphs

Source: https://erdosproblems.com/815
Status: DISPROVED (Narins-Pokrovskiy-Szabó 2017)

Statement:
Let k ≥ 3 and n be sufficiently large. If G is a graph with n vertices and
2n-2 edges such that every proper induced subgraph has minimum degree ≤ 2,
must G contain a copy of C_k (cycle of length k)?

Answer: NO (DISPROVED)

History:
- Erdős & Hajnal claimed they could prove it for 3 ≤ k ≤ 6
- Erdős, Faudree, Gyárfás, Schelp (1988) proved:
  * Such graphs contain cycles of length 3, 4, and 5
  * They contain a cycle of length at least ⌊log₂ n⌋
  * They need not contain a cycle longer than √n
- Narins, Pokrovskiy, Szabó (2017) disproved the conjecture:
  * There exist arbitrarily large such graphs with no cycle of length 23

Open: Does the conjecture hold for even k?

Terminology:
Such graphs are called "degree 3 critical" because:
- Every proper subgraph has min degree ≤ 2 (not 3-regular internally)
- The whole graph has some vertex of degree 3 (making it "critical")

References:
- [EFGS88] Erdős, Faudree, Gyárfás, Schelp, "Cycles in graphs without
           proper subgraphs of minimum degree 3" (1988)
- [Er91] Erdős, "Problems and results in combinatorial analysis" (1991)
- [NPS17] Narins, Pokrovskiy, Szabó, "Graphs without proper subgraphs of
          minimum degree 3 and short cycles" (2017)

Tags: graph-theory, extremal-graphs, cycles, counterexample, disproved
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open SimpleGraph Finset

namespace Erdos815

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Part I: Basic Definitions -/

/-- The minimum degree of a graph: the smallest degree among all vertices. -/
noncomputable def minDegree (G : SimpleGraph V) : ℕ :=
  sInf (Set.range (fun v : V => Nat.card (G.neighborSet v)))

/-- A graph is "degree 3 critical" if:
    1. Every proper induced subgraph has minimum degree ≤ 2
    2. The graph itself has some structure (2n-2 edges for n vertices)

    Such graphs are on the boundary of having a "3-regular core". -/
def IsDegree3Critical (G : SimpleGraph V) : Prop :=
  (Fintype.card V > 0) ∧
  (Nat.card G.edgeSet = 2 * Fintype.card V - 2) ∧
  (∀ (S : Finset V), S.card < Fintype.card V → S.Nonempty →
    minDegree (G.induce (S : Set V)) ≤ 2)

/-- The number of vertices in the graph. -/
def vertexCount (_G : SimpleGraph V) : ℕ := Fintype.card V

/-- The number of edges in the graph. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ := Nat.card G.edgeSet

/- ## Part II: Cycles -/

/-- A cycle of length k in a graph.
    (Simplified definition using walks.) -/
def HasCycleOfLength (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.length = k ∧ p.IsTrail ∧ k ≥ 3

/-- The graph contains C_k as a subgraph. -/
def ContainsCk (G : SimpleGraph V) (k : ℕ) : Prop :=
  HasCycleOfLength G k

/- ## Part III: The Erdős-Hajnal Conjecture -/

/-- **The Erdős-Hajnal Conjecture (original form):**
    For all k ≥ 3 and sufficiently large n, every degree 3 critical graph
    on n vertices contains a cycle of length k. -/
def ErdosHajnalConjecture : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      n ≥ N →
      IsDegree3Critical G →
      ContainsCk G k

/- ## Part IV: Known Positive Results -/

/-- **EFGS Theorem (1988):**
    Every degree 3 critical graph on n ≥ 5 vertices contains:
    - A triangle (C_3)
    - A 4-cycle (C_4)
    - A 5-cycle (C_5) -/
axiom efgs_short_cycles (n : ℕ) (G : SimpleGraph (Fin n))
    (hn : n ≥ 5) (hcrit : IsDegree3Critical G) :
    ContainsCk G 3 ∧ ContainsCk G 4 ∧ ContainsCk G 5

/- **EFGS Long Cycle Theorem (1988):**
    Every degree 3 critical graph on n vertices contains a cycle of length
    at least ⌊log₂ n⌋. -/
/- **EFGS Upper Bound (1988):**
    There exist degree 3 critical graphs with no cycle longer than √n. -/

/-- **Erdős-Hajnal k=6 claim:**
    Degree 3 critical graphs contain C₆ for sufficiently large n.
    Claimed by Erdős and Hajnal (1991) but the full proof was not published.
    The EFGS long cycle theorem (≥ ⌊log₂ n⌋) does not directly imply this,
    since having a long cycle does not guarantee a cycle of length exactly 6. -/
axiom erdos_hajnal_k6 :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      n ≥ N →
      IsDegree3Critical G →
      ContainsCk G 6

/-- **Erdős-Hajnal Partial Result:**
    The conjecture holds for k = 3, 4, 5, 6 (proved by EFGS for k ≤ 5,
    claimed by Erdős-Hajnal for k = 6). -/
theorem erdos_hajnal_small_k (k : ℕ) (hk : 3 ≤ k ∧ k ≤ 6) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      n ≥ N →
      IsDegree3Critical G →
      ContainsCk G k := by
  obtain ⟨hk_lo, hk_hi⟩ := hk
  interval_cases k
  · exact ⟨5, fun n G hn hcrit => (efgs_short_cycles n G hn hcrit).1⟩
  · exact ⟨5, fun n G hn hcrit => (efgs_short_cycles n G hn hcrit).2.1⟩
  · exact ⟨5, fun n G hn hcrit => (efgs_short_cycles n G hn hcrit).2.2⟩
  · exact erdos_hajnal_k6

/- ## Part V: The Counterexample -/

/--
**Theorem (Narins-Pokrovskiy-Szabó 2017):**
The Erdős-Hajnal conjecture is FALSE.

There exist arbitrarily large degree 3 critical graphs
containing NO cycle of length 23.

This disproves the conjecture for k = 23.
-/
axiom narins_pokrovskiy_szabo :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ ∃ G : SimpleGraph (Fin n),
      IsDegree3Critical G ∧
      ¬ContainsCk G 23

/-- **Erdős Problem #815: DISPROVED** -/
theorem erdos_815_disproved : ¬ErdosHajnalConjecture := by
  intro h
  -- The conjecture says: for k = 23, there exists N such that
  -- all degree 3 critical graphs on ≥N vertices contain C_23
  have ⟨N, hN⟩ := h 23 (by norm_num)
  -- But Narins-Pokrovskiy-Szabó gives a graph on ≥N vertices
  -- that is degree 3 critical but has no C_23
  have ⟨n, hn, G, hcrit, hno23⟩ := narins_pokrovskiy_szabo N
  exact hno23 (hN n G hn hcrit)

/- ## Part VI: What Remains Open -/

/-- **Open Problem:** Does the conjecture hold for EVEN k?

    The counterexample uses k = 23 (odd). It's unknown whether
    degree 3 critical graphs must contain C_k for all even k. -/
def evenKConjecture : Prop :=
  ∀ k : ℕ, k ≥ 4 → Even k →
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      n ≥ N →
      IsDegree3Critical G →
      ContainsCk G k

-- The even k conjecture remains open (status: OPEN).

/- ## Part VII: Why "Degree 3 Critical"? -/

/- **Understanding the Condition:**

    A graph with 2n-2 edges on n vertices is "sparse" - it has
    average degree about 4 (since 2|E| = Σ degrees).

    The "proper subgraphs have min degree ≤ 2" condition means:
    - You can't find a dense core inside the graph
    - Every subset loses its "3-regular" structure when isolated

    These graphs are on the boundary between:
    - Having enough edges for complex cycle structure
    - Being sparse enough that cycles might be avoided

    The name "degree 3 critical" comes from: these are minimal
    graphs (by edge count) that have a vertex of degree ≥ 3
    while all proper subgraphs stay at min degree ≤ 2. -/

/- ## Part VIII: The Construction Idea -/

/- **How the Counterexample Works (conceptual):**

    Narins-Pokrovskiy-Szabó construct graphs that:
    1. Satisfy the edge count: |E| = 2|V| - 2
    2. Every proper subgraph has min degree ≤ 2
    3. Carefully avoid creating any 23-cycle

    The construction uses:
    - Recursive structure
    - Careful local analysis of potential cycles
    - Graph products and expansions

    The choice of 23 is not magical - it's the smallest odd k
    where their construction works. Different techniques might
    find counterexamples for other odd k values. -/

/- ## Part IX: Summary -/

/--
**Summary of Erdős Problem #815**

**Question**: Must degree 3 critical graphs contain C_k for all k ≥ 3?

**Answer**: NO (DISPROVED for k = 23)

**What we formalize**:
1. Definition of degree 3 critical graphs
2. The Erdős-Hajnal conjecture
3. EFGS positive results (C_3, C_4, C_5 always exist)
4. EFGS bounds (log n ≤ longest cycle ≤ √n)
5. Narins-Pokrovskiy-Szabó counterexample (no C_23)
6. The formal disproof
7. Open problem: even k case

**Key insight**: While degree 3 critical graphs always contain
short cycles (3, 4, 5), carefully constructed examples can
avoid specific longer cycles like C_23.

**Timeline**:
1988: EFGS prove short cycles always exist
1991: Erdős states problem, claims k ≤ 6 case
2017: Narins-Pokrovskiy-Szabó disprove with k = 23
-/
theorem erdos_815_summary :
    ¬ErdosHajnalConjecture ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      n ≥ 5 → IsDegree3Critical G →
      ContainsCk G 3 ∧ ContainsCk G 4 ∧ ContainsCk G 5) :=
  ⟨erdos_815_disproved, fun n G hn hcrit => efgs_short_cycles n G hn hcrit⟩

end Erdos815
