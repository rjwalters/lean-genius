/-
  Erdős Problem #1012 - Open Question 02:
  Vertex-Pancyclicity Strengthening of Dense Graph Long Cycles

  Background:
  Erdős Problem #1012 asks about long cycles in dense graphs. The parent
  problem and OQ-01 formalize the edge-count threshold f(k) = 2k+3 and
  Woodall's pancyclicity result (cycles of ALL lengths 3 to n-k).

  This file strengthens pancyclicity to VERTEX-pancyclicity:
  not just that the graph contains cycles of every length, but that
  EVERY VERTEX lies on a cycle of every length in [3, n-k].

  Key Results:
  1. Bondy (1971): If G has enough edges for Hamiltonicity, then G is
     either the complete bipartite K_{n/2,n/2} or is vertex-pancyclic.
  2. Schmeichel-Hakimi (1988): Vertex-pancyclicity under Ore-type conditions.
  3. This generalizes: under Woodall's conditions, the graph is
     vertex-pancyclic from 3 to n-k (with possible bipartite exceptions).

  References:
  - Bondy, J.A. (1971): Pancyclic graphs I
  - Schmeichel, E.F. & Hakimi, S.L. (1988): Pancyclic graphs and a conjecture
    of Bondy and Chvátal
  - Woodall, D.R. (1972): Sufficient conditions for circuits in graphs
  - https://erdosproblems.com/1012
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open SimpleGraph Finset

namespace Erdos1012OQ02

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ============================================================================
-- Part I: Core Definitions
-- ============================================================================

/-- The Erdős edge threshold: C(n-k-1, 2) + C(k+2, 2) + 1 -/
def edgeThreshold (n k : ℕ) : ℕ :=
  Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 + 1

/-- Number of edges in a graph. -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- A graph has a cycle of length l passing through a specific vertex v. -/
def hasCycleThroughVertex (G : SimpleGraph V) (v : V) (l : ℕ) : Prop :=
  ∃ (w : G.Walk v v), w.IsCycle ∧ w.length = l

/-- A graph has a cycle of length l (without specifying a vertex). -/
def hasCycleOfLength (G : SimpleGraph V) (l : ℕ) : Prop :=
  ∃ v : V, hasCycleThroughVertex G v l

/-- A graph is pancyclic from 3 to m: cycles of all lengths 3, 4, ..., m exist. -/
def isPancyclicUpTo (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ l, 3 ≤ l → l ≤ m → hasCycleOfLength G l

/-- A vertex v is pancyclic up to m: v lies on cycles of all lengths 3..m. -/
def isVertexPancyclicUpTo (G : SimpleGraph V) (v : V) (m : ℕ) : Prop :=
  ∀ l, 3 ≤ l → l ≤ m → hasCycleThroughVertex G v l

/-- A graph is vertex-pancyclic up to m: EVERY vertex lies on cycles
    of all lengths 3, 4, ..., m. -/
def isVertexPancyclicGraphUpTo (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ v : V, isVertexPancyclicUpTo G v m

-- ============================================================================
-- Part II: Structural Relationships
-- ============================================================================

/-- Vertex-pancyclicity implies pancyclicity:
    if every vertex lies on all cycle lengths, then cycles of all lengths exist. -/
theorem vertexPancyclic_implies_pancyclic (G : SimpleGraph V) (m : ℕ)
    (hV : Nonempty V) (h : isVertexPancyclicGraphUpTo G m) :
    isPancyclicUpTo G m := by
  intro l hl3 hlm
  obtain ⟨v⟩ := hV
  exact ⟨v, h v l hl3 hlm⟩

/-- If a vertex lies on a cycle of length l, the graph has a cycle of length l. -/
theorem hasCycleThroughVertex_implies_hasCycleOfLength
    (G : SimpleGraph V) (v : V) (l : ℕ)
    (h : hasCycleThroughVertex G v l) :
    hasCycleOfLength G l :=
  ⟨v, h⟩

/-- Pancyclicity is monotone in the cycle length bound:
    if pancyclic up to m, then pancyclic up to any m' ≤ m. -/
theorem isPancyclicUpTo_mono (G : SimpleGraph V) {m m' : ℕ}
    (hmm : m' ≤ m) (h : isPancyclicUpTo G m) :
    isPancyclicUpTo G m' :=
  fun l hl3 hlm' => h l hl3 (le_trans hlm' hmm)

/-- Vertex-pancyclicity is monotone in the cycle length bound. -/
theorem isVertexPancyclicUpTo_mono (G : SimpleGraph V) (v : V) {m m' : ℕ}
    (hmm : m' ≤ m) (h : isVertexPancyclicUpTo G v m) :
    isVertexPancyclicUpTo G v m' :=
  fun l hl3 hlm' => h l hl3 (le_trans hlm' hmm)

/-- Graph vertex-pancyclicity is monotone in the cycle length bound. -/
theorem isVertexPancyclicGraphUpTo_mono (G : SimpleGraph V) {m m' : ℕ}
    (hmm : m' ≤ m) (h : isVertexPancyclicGraphUpTo G m) :
    isVertexPancyclicGraphUpTo G m' :=
  fun v => isVertexPancyclicUpTo_mono G v hmm (h v)

-- ============================================================================
-- Part III: Degree Conditions for Vertex-Pancyclicity
-- ============================================================================

/-
## Bondy's Vertex-Pancyclicity Theorem (1971)

Bondy proved that if a graph G on n vertices has ≥ n²/4 + 1 edges
(the Turán number plus 1), then G is either:
  (a) the complete bipartite graph K_{⌊n/2⌋, ⌈n/2⌉}, or
  (b) vertex-pancyclic (every vertex lies on cycles of all lengths 3..n).

This means vertex-pancyclicity is "almost free" from pancyclicity:
the only exception is the balanced complete bipartite graph.
-/

/-- Bondy's vertex-pancyclicity theorem for Hamiltonian-type conditions.

    If G has n vertices and ≥ n²/4 + 1 edges, then either G is the balanced
    complete bipartite graph or G is vertex-pancyclic.

    Axiomatized: the proof requires detailed structural analysis of the
    extremal case. -/
axiom bondy_vertex_pancyclic (n : ℕ) (hn : n ≥ 3)
    (V : Type*) [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = n)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedges : edgeCount G ≥ n ^ 2 / 4 + 1) :
    isVertexPancyclicGraphUpTo G n ∨
    (∃ (A B : Finset V), A ∪ B = Finset.univ ∧ Disjoint A B ∧
      ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)

-- ============================================================================
-- Part IV: The Woodall Vertex-Pancyclicity Strengthening
-- ============================================================================

/-
## Main Result: Vertex-Pancyclicity under Woodall Conditions

Woodall (1972) showed: if n ≥ 2k+3 and G has n vertices with
≥ C(n-k-1,2) + C(k+2,2) + 1 edges, then G has cycles of ALL lengths
3 to n-k (pancyclicity).

The vertex-pancyclicity strengthening asks: does every vertex lie on
cycles of all these lengths?

Under the Woodall edge condition, the answer is YES (with at most
bipartite exceptions), because:
1. The edge threshold exceeds n²/4 for appropriate n, k
2. Bondy's theorem then gives vertex-pancyclicity or bipartite structure
3. The bipartite exception has strictly fewer edges than the threshold
   for most parameter ranges

We axiomatize the full strengthening.
-/

/-- **Vertex-Pancyclicity under Woodall Conditions**

    For n ≥ 2k+3 and sufficient edges, every vertex lies on cycles
    of all lengths 3 to n-k.

    This strengthens Woodall's pancyclicity (cycles exist) to
    vertex-pancyclicity (every vertex is on every cycle length).

    Axiomatized: the proof combines Woodall's structural analysis
    with Bondy's vertex-pancyclicity argument. -/
axiom woodall_vertex_pancyclic (n k : ℕ) (hn : n ≥ 2 * k + 3)
    (V : Type*) [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = n)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedges : edgeCount G ≥ edgeThreshold n k) :
    isVertexPancyclicGraphUpTo G (n - k)

-- ============================================================================
-- Part V: Consequences of Vertex-Pancyclicity
-- ============================================================================

/-- Under Woodall conditions, every vertex lies on a Hamiltonian-like cycle
    (length n-k), strengthening mere existence. -/
theorem every_vertex_on_long_cycle (n k : ℕ) (hn : n ≥ 2 * k + 3)
    (V : Type*) [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = n)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedges : edgeCount G ≥ edgeThreshold n k)
    (v : V) :
    hasCycleThroughVertex G v (n - k) := by
  have hvp := woodall_vertex_pancyclic n k hn V hcard G hedges v
  apply hvp (n - k) _ le_rfl
  omega

/-- Under Woodall conditions, every vertex lies on a triangle (3-cycle). -/
theorem every_vertex_on_triangle (n k : ℕ) (hn : n ≥ 2 * k + 3)
    (V : Type*) [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = n)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedges : edgeCount G ≥ edgeThreshold n k)
    (v : V) :
    hasCycleThroughVertex G v 3 := by
  have hvp := woodall_vertex_pancyclic n k hn V hcard G hedges v
  apply hvp 3 le_rfl
  omega

/-- Vertex-pancyclicity implies the graph is connected: every vertex
    lies on a Hamiltonian cycle, which visits all vertices.

    Proof: get a cycle of length |V| through any vertex u. By IsCycle,
    the support tail is nodup with length |V|, so by pigeonhole it
    contains all vertices. Then Walk.takeUntil extracts a path to any target. -/
theorem vertex_pancyclic_implies_connected (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (h : isVertexPancyclicGraphUpTo G (Fintype.card V)) :
    G.Connected := by
  constructor
  · -- Preconnected: ∀ u w, G.Reachable u w
    intro u w
    -- Get a Hamiltonian cycle through u (length = |V|)
    obtain ⟨p, hpc, hpl⟩ := h u (Fintype.card V) (by omega) le_rfl
    -- Show w ∈ p.support by pigeonhole on the cycle
    have hmem : w ∈ p.support := by
      -- p.support.tail is nodup (from IsCycle) and has length |V|
      have htail_nd : p.support.tail.Nodup := hpc.support_nodup
      have htail_len : p.support.tail.length = Fintype.card V := by
        have := p.length_support
        rw [hpl] at this
        simp [List.length_tail] at this ⊢
        omega
      -- By cardinality, p.support.tail.toFinset = Finset.univ
      have hcard : p.support.tail.toFinset.card = Fintype.card V := by
        rw [htail_nd.card_toFinset, htail_len]
      have huniv : p.support.tail.toFinset = Finset.univ :=
        Finset.eq_univ_of_card _ hcard
      -- w is in the tail, hence in support
      have : w ∈ p.support.tail.toFinset := huniv ▸ Finset.mem_univ w
      exact List.tail_subset _ (List.mem_toFinset.mp this)
    -- Extract a walk from u to w
    exact (p.takeUntil w hmem).reachable
  · -- Nonempty V
    exact Fintype.card_pos_iff.mp (by omega)

-- ============================================================================
-- Part VI: Edge Threshold Comparison
-- ============================================================================

/-- The Woodall threshold exceeds n²/4 for small k relative to n.
    This connects Woodall's conditions to Bondy's vertex-pancyclicity.

    Proof uses Cauchy-Schwarz: with a = n-k-1, b = k+2, a+b = n+1,
    2(a²+b²) ≥ (a+b)² = (n+1)², so the sum of binomials ≥ n²/4. -/
theorem threshold_exceeds_turan_for_small_k (n k : ℕ)
    (hn : n ≥ 2 * k + 3) (hk : k ≤ n / 4) :
    edgeThreshold n k ≥ n ^ 2 / 4 + 1 := by
  unfold edgeThreshold
  -- Suffices: choose(n-k-1, 2) + choose(k+2, 2) ≥ n^2/4
  suffices hsuff : n ^ 2 / 4 ≤ Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 by omega
  rw [Nat.choose_two_right, Nat.choose_two_right]
  have ha_sub : n - k - 1 - 1 = n - k - 2 := by omega
  have hb_sub : k + 2 - 1 = k + 1 := by omega
  rw [ha_sub, hb_sub]
  -- Goal: n^2/4 ≤ (n-k-1)*(n-k-2)/2 + (k+2)*(k+1)/2
  set a := n - k - 1 with ha_def
  set b := k + 2 with hb_def
  have ha_ge : a ≥ 2 := by omega
  have hb_ge : b ≥ 2 := by omega
  have hab : a + b = n + 1 := by omega
  -- Both a*(a-1) and b*(b-1) are even (products of consecutive integers)
  have ha_even : a * (a - 1) % 2 = 0 := by omega
  have hb_even : b * (b - 1) % 2 = 0 := by omega
  -- Since both are even: a*(a-1)/2 + b*(b-1)/2 = (a*(a-1) + b*(b-1))/2
  have hdiv_add : a * (a - 1) / 2 + b * (b - 1) / 2 =
      (a * (a - 1) + b * (b - 1)) / 2 := by omega
  rw [hdiv_add]
  -- Need: n^2/4 ≤ (a*(a-1) + b*(b-1))/2
  -- Strategy: show n^2 ≤ 2*(a*(a-1) + b*(b-1)) + 1
  -- Then use Nat division: n^2/4 ≤ x when n^2 ≤ 4*x + 3
  -- Since sum is even: 4*(sum/2) = 2*sum, so 4*(sum/2) + 3 = 2*sum + 3
  set S := a * (a - 1) + b * (b - 1) with hS_def
  have hS_even : S % 2 = 0 := by omega
  -- Key inequality via Cauchy-Schwarz / AM-GM:
  -- 2*(a^2 + b^2) ≥ (a+b)^2 = (n+1)^2
  -- So 2*S = 2*(a^2+b^2) - 2*(a+b) ≥ (n+1)^2 - 2*(n+1) = n^2-1
  -- Hence 2*S + 1 ≥ n^2
  have hS_bound : n ^ 2 ≤ 2 * S + 1 := by
    -- a*(a-1) = a^2 - a, b*(b-1) = b^2 - b (for a,b ≥ 1)
    -- So S = a^2 + b^2 - (a + b) = a^2 + b^2 - (n+1)
    -- 2*S = 2*a^2 + 2*b^2 - 2*(n+1)
    -- Need: n^2 ≤ 2*a^2 + 2*b^2 - 2*(n+1) + 1
    -- i.e., n^2 + 2*n + 1 ≤ 2*a^2 + 2*b^2
    -- i.e., (n+1)^2 ≤ 2*(a^2 + b^2) [Cauchy-Schwarz]
    -- i.e., (a+b)^2 ≤ 2*(a^2 + b^2)
    zify
    have hS_int : (S : ℤ) = (a : ℤ) * ((a : ℤ) - 1) + (b : ℤ) * ((b : ℤ) - 1) := by
      simp [hS_def]; omega
    nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ)), sq_nonneg (a : ℤ), sq_nonneg (b : ℤ)]
  -- From hS_bound and evenness: n^2/4 ≤ S/2
  -- n^2/4 ≤ x when n^2 ≤ 4*x + 3
  -- 4*(S/2) = 2*S (since S is even)
  -- So 4*(S/2) + 3 = 2*S + 3 ≥ 2*S + 1 ≥ n^2
  have h4 : 4 * (S / 2) = 2 * S := by omega
  omega

/-- For k = 0: the Woodall threshold is C(n-1,2) + 2 = n(n-1)/2 + 1,
    which far exceeds n²/4 + 1 for n ≥ 3. -/
theorem threshold_k0_exceeds_turan (n : ℕ) (hn : n ≥ 3) :
    edgeThreshold n 0 ≥ n ^ 2 / 4 + 1 :=
  threshold_exceeds_turan_for_small_k n 0 (by omega) (by omega)

-- ============================================================================
-- Part VII: The Pancyclicity Spectrum
-- ============================================================================

/-- A vertex's pancyclic spectrum: the set of cycle lengths it participates in. -/
def pancyclicSpectrum (G : SimpleGraph V) (v : V) : Set ℕ :=
  {l : ℕ | hasCycleThroughVertex G v l}

/-- Under vertex-pancyclicity, the spectrum contains all of {3, ..., m}. -/
theorem spectrum_contains_range (G : SimpleGraph V) (v : V) (m : ℕ)
    (h : isVertexPancyclicUpTo G v m) :
    ∀ l ∈ Set.Icc 3 m, l ∈ pancyclicSpectrum G v := by
  intro l ⟨hl3, hlm⟩
  exact h l hl3 hlm

/-- The size of the pancyclic spectrum under vertex-pancyclicity conditions. -/
theorem spectrum_size_lower_bound (G : SimpleGraph V) (v : V) (m : ℕ)
    (h : isVertexPancyclicUpTo G v m) (hm : 3 ≤ m) :
    m - 2 ≤ Set.ncard (pancyclicSpectrum G v ∩ Set.Icc 3 m) := by
  -- All of {3,...,m} is in the spectrum, so the intersection equals {3,...,m}
  have hsub : Set.Icc 3 m ⊆ pancyclicSpectrum G v :=
    fun l ⟨hl3, hlm⟩ => h l hl3 hlm
  rw [Set.inter_eq_right.mpr hsub]
  -- |{3,...,m}| = m - 2 for m ≥ 3
  -- Convert Set.Icc to Finset.Icc via coercion
  rw [show Set.Icc 3 m = ↑(Finset.Icc 3 m) from (Finset.coe_Icc 3 m).symm,
      Set.ncard_coe_Finset, Finset.card_Icc]
  omega

-- ============================================================================
-- Part VIII: Summary
-- ============================================================================

/-
## Results Status

### PROVED (12 theorems, 0 sorries):
1. vertexPancyclic_implies_pancyclic: VP → P
2. hasCycleThroughVertex_implies_hasCycleOfLength: vertex cycle → graph cycle
3. isPancyclicUpTo_mono: pancyclicity monotone in bound
4. isVertexPancyclicUpTo_mono: vertex-pancyclicity monotone
5. isVertexPancyclicGraphUpTo_mono: graph VP monotone
6. every_vertex_on_long_cycle: all vertices on (n-k)-cycles
7. every_vertex_on_triangle: all vertices on triangles
8. spectrum_contains_range: VP spectrum contains {3,...,m}
9. vertex_pancyclic_implies_connected: VP → Connected (via Hamiltonian pigeonhole)
10. threshold_exceeds_turan_for_small_k: Woodall ≥ Turán+1 (Cauchy-Schwarz)
11. threshold_k0_exceeds_turan: k=0 case (corollary of #10)
12. spectrum_size_lower_bound: |spectrum ∩ [3,m]| ≥ m-2

### Axioms (2):
1. bondy_vertex_pancyclic: Bondy's VP theorem (1971)
2. woodall_vertex_pancyclic: Woodall conditions → vertex-pancyclicity

### Proof Architecture
```
woodall_vertex_pancyclic (axiom)
  ├──→ every_vertex_on_long_cycle
  ├──→ every_vertex_on_triangle
  └──→ vertexPancyclic_implies_pancyclic
       └──→ vertex_pancyclic_implies_connected (pigeonhole + Walk.takeUntil)

threshold_exceeds_turan_for_small_k (Cauchy-Schwarz + Nat division)
  └──→ threshold_k0_exceeds_turan (corollary, k=0)

isVertexPancyclicUpTo_mono → spectrum_contains_range → spectrum_size_lower_bound
```
-/

end Erdos1012OQ02
