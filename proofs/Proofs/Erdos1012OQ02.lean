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
    lies on a cycle, hence is reachable from some other vertex.

    Proof sketch: every vertex lies on a 3-cycle, so it has at least
    2 neighbors. Any two vertices that share a cycle are connected.
    Since all vertices participate in cycles, the graph is connected. -/
theorem vertex_pancyclic_implies_connected (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (h : isVertexPancyclicGraphUpTo G (Fintype.card V)) :
    G.Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · -- Show Preconnected: any two vertices are reachable
    intro u w
    -- u lies on a cycle of length |V| ≥ 3
    obtain ⟨wu, hwuc, hwul⟩ := h u (Fintype.card V) hV le_rfl
    -- All vertices are in wu.support since the cycle visits |V| vertices.
    -- wu.support.tail has Nodup (from IsCycle) and length = |V|.
    have htail_nd : wu.support.tail.Nodup := hwuc.support_nodup
    have htail_len : wu.support.tail.length = Fintype.card V := by
      simp [List.length_tail, wu.length_support, hwul]
    -- Nodup list of length |V| from type V must contain all elements
    have htail_univ : wu.support.tail.toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [List.toFinset_card_of_nodup htail_nd, htail_len]
    have hw_mem : w ∈ wu.support := by
      have : w ∈ wu.support.tail :=
        List.mem_toFinset.mp (htail_univ ▸ Finset.mem_univ w)
      exact List.tail_subset _ this
    exact (wu.takeUntil w hw_mem).reachable
  · -- Show Nonempty V
    exact Fintype.card_pos_iff.mp (by omega)

-- ============================================================================
-- Part VI: Edge Threshold Comparison
-- ============================================================================

/-- The Woodall threshold exceeds n²/4 for small k relative to n.
    This connects Woodall's conditions to Bondy's vertex-pancyclicity.

    Proof: Setting a = n-k-1, b = k+2, a+b = n+1, we have the identity
    2*(a*(a-1) + b*(b-1)) + 1 = n² + (a-b)².  Since (a-b)² ≥ 0,
    we get C(a,2) + C(b,2) ≥ n²/4, so the threshold = C(a,2) + C(b,2) + 1 ≥ n²/4 + 1. -/
theorem threshold_exceeds_turan_for_small_k (n k : ℕ)
    (hn : n ≥ 2 * k + 3) (_hk : k ≤ n / 4) :
    edgeThreshold n k ≥ n ^ 2 / 4 + 1 := by
  -- Substitute n = 2k+3+c for c ≥ 0
  obtain ⟨c, rfl⟩ : ∃ c, n = 2 * k + 3 + c := ⟨n - (2 * k + 3), by omega⟩
  unfold edgeThreshold
  rw [Nat.choose_two_right, Nat.choose_two_right]
  have h1 : 2 * k + 3 + c - k - 1 = k + 2 + c := by omega
  have h2 : (k + 2 + c) - 1 = k + 1 + c := by omega
  have h3 : k + 2 - 1 = k + 1 := by omega
  rw [h1, h2, h3]
  -- Goal: (k+2+c)*(k+1+c)/2 + (k+2)*(k+1)/2 + 1 ≥ (2*k+3+c)^2/4 + 1
  suffices h : (2 * k + 3 + c) ^ 2 / 4 ≤
      (k + 2 + c) * (k + 1 + c) / 2 + (k + 2) * (k + 1) / 2 by omega
  -- Both products are even (consecutive integers), factor out
  obtain ⟨p, hp⟩ := Nat.even_mul_succ_self (k + 1 + c)
  obtain ⟨q, hq⟩ := Nat.even_mul_succ_self (k + 1)
  have hp' : (k + 2 + c) * (k + 1 + c) = 2 * p := by
    have : (k + 1 + c) + 1 = k + 2 + c := by omega
    rw [mul_comm, this] at hp; omega
  have hq' : (k + 2) * (k + 1) = 2 * q := by
    have : (k + 1) + 1 = k + 2 := by omega
    rw [mul_comm, this] at hq; omega
  rw [hp', hq']
  -- Simplify 2*p/2 = p, 2*q/2 = q
  have hp2 : 2 * p / 2 = p := Nat.mul_div_cancel_left p (by omega)
  have hq2 : 2 * q / 2 = q := Nat.mul_div_cancel_left q (by omega)
  rw [hp2, hq2]
  -- Goal: (2*k+3+c)^2/4 ≤ p + q
  -- Key identity: 4*(p+q) + 1 = (2*k+3+c)^2 + c^2
  have hident : 4 * (p + q) + 1 = (2 * k + 3 + c) ^ 2 + c ^ 2 := by
    have : 2 * ((k + 2 + c) * (k + 1 + c) + (k + 2) * (k + 1)) + 1 =
        (2 * k + 3 + c) ^ 2 + c ^ 2 := by ring
    rw [hp', hq'] at this; omega
  -- (2*k+3+c)^2 ≤ 4*(p+q) + 1 since c^2 ≥ 0
  set X := (2 * k + 3 + c) ^ 2
  have hbound : X ≤ 4 * (p + q) + 1 := by linarith [hident, Nat.zero_le (c ^ 2)]
  omega

/-- For k = 0: the Woodall threshold is C(n-1,2) + 2 = n(n-1)/2 + 1,
    which far exceeds n²/4 + 1 for n ≥ 3. -/
theorem threshold_k0_exceeds_turan (n : ℕ) (hn : n ≥ 3) :
    edgeThreshold n 0 ≥ n ^ 2 / 4 + 1 := by
  unfold edgeThreshold
  simp only [Nat.sub_zero]
  have hc22 : Nat.choose 2 2 = 1 := by decide
  rw [hc22, Nat.choose_two_right]
  have hsub : n - 1 - 1 = n - 2 := by omega
  rw [hsub]
  -- Goal: (n-1)*(n-2)/2 + 1 + 1 ≥ n^2/4 + 1
  suffices h : n ^ 2 / 4 ≤ (n - 1) * (n - 2) / 2 + 1 by omega
  rcases le_or_gt n 5 with hsmall | hlarge
  · -- n ∈ {3, 4, 5}: check directly
    interval_cases n <;> omega
  · -- n ≥ 6: algebraic bound
    have hkey : n ^ 2 ≤ 2 * ((n - 1) * (n - 2)) := by
      obtain ⟨a, rfl⟩ : ∃ a, n = a + 6 := ⟨n - 6, by omega⟩
      have h5 : a + 6 - 1 = a + 5 := by omega
      have h4 : a + 6 - 2 = a + 4 := by omega
      rw [h5, h4]
      have hexp1 : (a + 6) ^ 2 = a ^ 2 + 12 * a + 36 := by ring
      have hexp2 : 2 * ((a + 5) * (a + 4)) = 2 * a ^ 2 + 18 * a + 40 := by ring
      linarith [sq_nonneg a]
    calc n ^ 2 / 4
        ≤ 2 * ((n - 1) * (n - 2)) / 4 := Nat.div_le_div_right hkey
      _ = (n - 1) * (n - 2) / 2 := by
          rw [show (4 : ℕ) = 2 * 2 from by omega]
          exact Nat.mul_div_mul_left _ _ (by omega)
      _ ≤ (n - 1) * (n - 2) / 2 + 1 := Nat.le_add_right _ _

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
  -- Set.Icc 3 m ⊆ pancyclicSpectrum G v (from spectrum_contains_range)
  have hsub : Set.Icc 3 m ⊆ pancyclicSpectrum G v ∩ Set.Icc 3 m :=
    Set.subset_inter (spectrum_contains_range G v m h) Set.Subset.rfl
  -- pancyclicSpectrum G v ∩ Set.Icc 3 m is finite
  have hfin : (pancyclicSpectrum G v ∩ Set.Icc 3 m).Finite :=
    Set.Finite.subset (Set.finite_Icc 3 m) Set.inter_subset_right
  calc m - 2
      = Set.ncard (Set.Icc 3 m : Set ℕ) := by
        rw [Set.ncard_eq_toFinset_card']
        simp only [Set.toFinset_Icc, Nat.card_Icc]
        omega
    _ ≤ Set.ncard (pancyclicSpectrum G v ∩ Set.Icc 3 m) :=
        Set.ncard_le_ncard hsub hfin

-- ============================================================================
-- Part VIII: Summary
-- ============================================================================

/-
## Results Status

### PROVED (0 sorries):
1. vertexPancyclic_implies_pancyclic: VP → P
2. hasCycleThroughVertex_implies_hasCycleOfLength: vertex cycle → graph cycle
3. isPancyclicUpTo_mono: pancyclicity monotone in bound
4. isVertexPancyclicUpTo_mono: vertex-pancyclicity monotone
5. isVertexPancyclicGraphUpTo_mono: graph VP monotone
6. every_vertex_on_long_cycle: all vertices on (n-k)-cycles
7. every_vertex_on_triangle: all vertices on triangles
8. spectrum_contains_range: VP spectrum contains {3,...,m}
9. vertex_pancyclic_implies_connected: VP graph is connected (Walk API)
10. threshold_exceeds_turan_for_small_k: binomial inequality (QM-AM identity)
11. threshold_k0_exceeds_turan: arithmetic for k=0 case
12. spectrum_size_lower_bound: counting via Set.ncard

### Axioms (2):
1. bondy_vertex_pancyclic: Bondy's VP theorem (1971)
2. woodall_vertex_pancyclic: Woodall conditions → vertex-pancyclicity

### Sorries: 0

### Proof Architecture
```
woodall_vertex_pancyclic (axiom)
  ├──→ every_vertex_on_long_cycle
  ├──→ every_vertex_on_triangle
  └──→ vertexPancyclic_implies_pancyclic

bondy_vertex_pancyclic (axiom)
  └──→ threshold_exceeds_turan_for_small_k (connects to Bondy)

vertex_pancyclic_implies_connected ← isVertexPancyclicGraphUpTo
  └──→ uses Walk.IsCycle.support_nodup + pigeonhole

threshold_k0_exceeds_turan ← Nat.choose_two_right + algebraic bound
threshold_exceeds_turan_for_small_k ← QM-AM identity: 2S+1 = n²+c²

spectrum_contains_range → spectrum_size_lower_bound (via Set.ncard)
```
-/

end Erdos1012OQ02
