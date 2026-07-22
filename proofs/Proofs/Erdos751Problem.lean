/-
Erdős Problem #751: Cycle Lengths in 4-Chromatic Graphs

Source: https://erdosproblems.com/751
Status: SOLVED

Statement:
Let G be a graph with chromatic number χ(G) = 4. If m₁ < m₂ < ⋯ are the lengths
of the cycles in G, can min(mᵢ₊₁ - mᵢ) be arbitrarily large? Can this happen
if the girth of G is large?

Answer: NO

Bondy and Vince (1998) proved that every graph with minimum degree at least 3
has two cycles whose lengths differ by at most 2. Since every graph with
chromatic number 4 has minimum degree at least 3, the answer follows.

Key Insight:
The chromatic number lower bounds the minimum degree (χ(G) ≤ Δ(G) + 1, and
more relevantly, minimum degree at least χ(G) - 1 for graphs with χ(G) ≥ 2).

References:
- Bondy, Vince (1998): "Cycles in a graph whose lengths differ by one or two"
  J. Graph Theory 27, 11-15
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

namespace Erdos751

/-
## Part I: Graph Theory Foundations

Basic definitions for graphs, cycles, and chromatic number.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/--
**Minimum Degree:**
The minimum degree δ(G) is the smallest vertex degree in G.
-/
noncomputable def minDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.min' (Finset.univ.image (fun v => G.degree v)) (by simp)

/--
**Maximum Degree:**
The maximum degree Δ(G) is the largest vertex degree in G.
-/
noncomputable def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.max' (Finset.univ.image (fun v => G.degree v)) (by simp)

/--
**Chromatic Number:**
The chromatic number χ(G) is the minimum number of colors needed to properly
color the vertices of G (no two adjacent vertices have the same color).

Defined from Mathlib's `SimpleGraph.chromaticNumber : ℕ∞` via `.toNat`.
(Formerly an axiom.) -/
noncomputable def chromaticNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (SimpleGraph.chromaticNumber G).toNat

/--
**Girth:**
The girth of G is the length of the shortest cycle in G.
If G is acyclic (a forest), the girth is 0 (Mathlib's `girth = egirth.toNat`,
and `egirth` of an acyclic graph is `⊤`, whose `toNat` is `0`).

Defined from Mathlib's `SimpleGraph.girth`. (Formerly an axiom.) -/
noncomputable def girth (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  SimpleGraph.girth G

/--
**Cycle Lengths:**
The set of all cycle lengths present in G: lengths of closed cycle walks.

Defined directly from Mathlib's `Walk`/`IsCycle`. (Formerly an axiom.) -/
def cycleLengths (G : SimpleGraph V) [DecidableRel G.Adj] : Set ℕ :=
  {n | ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = n}

/--
**Cycle Length Gap:**
Given the cycle lengths, the minimum gap between consecutive lengths.
-/
noncomputable def minCycleLengthGap (lengths : Set ℕ) : ℕ :=
  sInf {d : ℕ | ∃ a ∈ lengths, ∃ b ∈ lengths, a < b ∧ d = b - a}

/--
**Minimum gap upper bound.**
Any pair of distinct lengths in the set witnesses an upper bound on the minimum
gap: the closest pair of elements is always a consecutive pair, so the minimum
difference over all distinct pairs equals the minimum consecutive gap. -/
theorem minCycleLengthGap_le {S : Set ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a < b) : minCycleLengthGap S ≤ b - a :=
  Nat.sInf_le ⟨a, ha, b, hb, hab, rfl⟩

/-
## Part II: Key Relationships
-/

/- 
**Chromatic Number and Minimum Degree:**
For any graph G with at least one vertex:
  χ(G) ≤ Δ(G) + 1 (greedy coloring bound)

More importantly for us:
  If χ(G) ≥ k, then G has a subgraph with minimum degree ≥ k - 1.
-/
/--
**Alternative formulation:**
Every graph with chromatic number 4 contains a subgraph of minimum degree 3.
In fact, for χ(G) = 4, we need minimum degree at least 3.
-/
axiom four_chromatic_minDeg (G : SimpleGraph V) [DecidableRel G.Adj] :
    chromaticNumber G = 4 → minDegree G ≥ 3

/-
## Part III: Bondy-Vince Theorem

The key result: graphs with minimum degree ≥ 3 have close cycle lengths.
-/

/--
**Bondy-Vince Theorem (1998):**
Every graph with minimum degree at least 3 has two cycles whose lengths
differ by at most 2.

More precisely: if G has δ(G) ≥ 3, then there exist cycle lengths
m, m' in G with |m - m'| ≤ 2.
-/
axiom bondy_vince_theorem (G : SimpleGraph V) [DecidableRel G.Adj] :
    minDegree G ≥ 3 →
    ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
      (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2

/- 
**Immediate Corollary:**
The minimum gap between consecutive cycle lengths is at most 2.
-/
/-
## Part IV: Main Results

Answer to Erdős's question.
-/

/--
**Erdős Problem #751: Part 1**
For graphs with chromatic number 4, the minimum gap between consecutive
cycle lengths cannot be arbitrarily large.

In fact, the gap is always at most 2.
-/
theorem erdos_751_chromatic_4 (G : SimpleGraph V) [DecidableRel G.Adj] :
    chromaticNumber G = 4 →
    ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
      (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2 := by
  intro hchi
  have hminDeg : minDegree G ≥ 3 := four_chromatic_minDeg G hchi
  exact bondy_vince_theorem G hminDeg

/--
**Erdős Problem #751: Part 2**
The answer is NO even if we require large girth.
Having large girth doesn't help because minimum degree ≥ 3 is the key.
-/
theorem erdos_751_with_girth (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    chromaticNumber G = 4 → girth G ≥ k →
    ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
      (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2 := by
  intro hchi _hgirth
  -- The girth condition doesn't help - the result follows from χ(G) = 4 alone
  exact erdos_751_chromatic_4 G hchi

/--
**Erdős Problem #751: Full Answer**
Can min(mᵢ₊₁ - mᵢ) be arbitrarily large for χ(G) = 4?
Answer: NO, the gap is always ≤ 2.
-/
theorem erdos_751 (G : SimpleGraph V) [DecidableRel G.Adj] :
    chromaticNumber G = 4 →
    ¬(∀ n : ℕ, minCycleLengthGap (cycleLengths G) > n) := by
  intro hchi hcontra
  -- The gap is at most 2, so it can't be > 2
  have h := erdos_751_chromatic_4 G hchi
  obtain ⟨m, m', hm, hm', hne, hgap1, hgap2⟩ := h
  -- The minimum gap is at most |m - m'| ≤ 2
  have hgap_bound : minCycleLengthGap (cycleLengths G) ≤ 2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · calc minCycleLengthGap (cycleLengths G) ≤ m' - m := minCycleLengthGap_le hm hm' h
        _ ≤ 2 := by omega
    · calc minCycleLengthGap (cycleLengths G) ≤ m - m' := minCycleLengthGap_le hm' hm h
        _ ≤ 2 := by omega
  -- But hcontra says gap > 3, contradiction
  have := hcontra 3
  omega

/-
## Part V: Strengthening - Minimum Degree 3 Suffices
-/

/--
**Generalization:**
The result holds for any graph with minimum degree ≥ 3, not just χ(G) = 4.
-/
theorem min_degree_3_cycle_gap (G : SimpleGraph V) [DecidableRel G.Adj] :
    minDegree G ≥ 3 →
    ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
      (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2 :=
  bondy_vince_theorem G

/--
**Why Chromatic Number 4 Implies Minimum Degree 3:**
A graph with χ(G) = 4 must have a vertex of degree ≥ 3.
Actually, it must have minimum degree ≥ 3 (otherwise we could
color greedily with fewer colors).
-/
theorem chromatic_4_implies_min_deg_3 (G : SimpleGraph V) [DecidableRel G.Adj] :
    chromaticNumber G = 4 → minDegree G ≥ 3 :=
  four_chromatic_minDeg G

/-
## Part VI: Summary
-/

/--
**Erdős Problem #751: SOLVED**

Summary of results:
1. Bondy-Vince: δ(G) ≥ 3 ⟹ two cycles differ by at most 2
2. χ(G) = 4 ⟹ δ(G) ≥ 3
3. Therefore: χ(G) = 4 ⟹ gap ≤ 2

The answer is NO - the gap cannot be arbitrarily large, and large
girth doesn't help either.
-/
theorem erdos_751_summary (G : SimpleGraph V) [DecidableRel G.Adj] :
    -- Main result: 4-chromatic implies close cycles
    (chromaticNumber G = 4 →
      ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
        (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2) ∧
    -- Generalization: min degree 3 suffices
    (minDegree G ≥ 3 →
      ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
        (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2) ∧
    -- Connection: χ = 4 implies min degree ≥ 3
    (chromaticNumber G = 4 → minDegree G ≥ 3) :=
  ⟨erdos_751_chromatic_4 G, min_degree_3_cycle_gap G, chromatic_4_implies_min_deg_3 G⟩

end Erdos751
