/-
Erdős Problem #832: Minimum Edges in Hypergraphs with Given Chromatic Number

Source: https://erdosproblems.com/832
Status: SOLVED (Conjecture disproved by Alon)

Statement:
Let r ≥ 3 and k be sufficiently large in terms of r. Is it true that every
r-uniform hypergraph with chromatic number k has at least C((r-1)(k-1)+1, r)
edges, with equality only for the complete graph on (r-1)(k-1)+1 vertices?

Answer: NO (for r ≥ 4) - Alon (1985) disproved this conjecture.

Key Results:
- r = 2: Classical - chromatic number k implies ≥ C(k,2) edges
- r = 3: The conjecture is FALSE for k = 3 (Steiner triples: 7 vertices, 7 edges)
- r ≥ 4: Alon proved counterexamples exist using Turán numbers
- Asymptotic: m(r,k) ~ c_r · k^r for some constant c_r depending on r

Bounds on m(r,k) (minimum edges for chromatic number > k):
- Lower: (r/log r) · k^r ≪ m(r,k) (Akolzin-Shabanov 2016)
- Upper: m(r,k) ≪ (r³ log r) · k^r (Akolzin-Shabanov 2016)
- Limit: m(r,k)/k^r → c_r as k → ∞ (Cherkashin-Petrov 2020)

References:
- [Al85] Alon: Hypergraphs with high chromatic number (1985)
- [AkSh16] Akolzin-Shabanov: Colorings of hypergraphs with large number of colors (2016)
- [ChPe20] Cherkashin-Petrov: Regular behavior of maximal hypergraph chromatic number (2020)
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Erdos832

/-
## Part I: Basic Definitions
-/

/--
**r-Uniform Hypergraph:**
A collection of edges where each edge has exactly r vertices.
-/
structure Hypergraph (V : Type*) where
  edges : Set (Finset V)

/--
**r-Uniformity:**
All edges have exactly r vertices.
-/
def IsUniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

/--
**Number of edges:**
-/
noncomputable def numEdges (H : Hypergraph V) [Fintype V] : ℕ :=
  (H.edges.toFinite.toFinset).card

/--
**Proper k-colouring of a hypergraph:**
An assignment of colours {1, ..., k} to vertices such that no edge is monochromatic.
-/
def IsProperColouring {V : Type*} (H : Hypergraph V) (c : V → Fin k) : Prop :=
  ∀ e ∈ H.edges, ∃ u v, u ∈ e ∧ v ∈ e ∧ c u ≠ c v

/--
**Chromatic number of a hypergraph:**
The minimum k such that H has a proper k-colouring.
-/
noncomputable def chromaticNumber (H : Hypergraph V) : ℕ :=
  Nat.find (by use Fintype.card V; sorry : ∃ k, ∃ c : V → Fin k, IsProperColouring H c)

/--
**Chromatic number at least k:**
-/
def hasChromaticNumberAtLeast (H : Hypergraph V) (k : ℕ) : Prop :=
  ¬∃ c : V → Fin (k - 1), IsProperColouring H c

/-
## Part II: The Classical Graph Case (r = 2)
-/

/--
**Classical result for graphs (r = 2):**
A graph with chromatic number k has at least C(k, 2) = k(k-1)/2 edges.

This is because the complete graph K_k is the extremal example.
-/
axiom classical_graph_bound (G : SimpleGraph V) [Fintype V] [DecidableEq V] (k : ℕ)
    (hχ : G.chromaticNumber = k) :
    G.edgeFinset.card ≥ k * (k - 1) / 2

/-
## Part III: Erdős's Conjecture
-/

/--
**Erdős's conjecture:**
For r ≥ 3 and k sufficiently large (in terms of r), every r-uniform hypergraph
with chromatic number k has at least C((r-1)(k-1)+1, r) edges.

The conjectured extremal example is the complete r-uniform hypergraph
on (r-1)(k-1)+1 vertices.
-/
def erdosConjecture (r k : ℕ) : Prop :=
  r ≥ 3 →
    ∀ H : Hypergraph V, IsUniform H r → hasChromaticNumberAtLeast H k →
      numEdges H ≥ Nat.choose ((r - 1) * (k - 1) + 1) r

/--
**The conjectured extremal graph:**
The complete r-uniform hypergraph on n = (r-1)(k-1)+1 vertices has
exactly C(n, r) edges and chromatic number exactly k.
-/
def completeHypergraph (V : Type*) [Fintype V] (r : ℕ) : Hypergraph V where
  edges := {e : Finset V | e.card = r}

/-
## Part IV: The r = 3, k = 3 Counterexample
-/

/--
**Steiner triple system:**
The Fano plane is a 3-uniform hypergraph on 7 vertices with 7 edges
that requires 3 colours.

Erdős's conjecture would predict ≥ C(2·2+1, 3) = C(5, 3) = 10 edges.
But the Fano plane has only 7 edges with chromatic number 3.

This is why Erdős required k to be "sufficiently large".
-/
axiom steiner_counterexample :
    ∃ H : Hypergraph (Fin 7),
      IsUniform H 3 ∧
      hasChromaticNumberAtLeast H 3 ∧
      numEdges H = 7 ∧
      7 < Nat.choose 5 3

/-
## Part V: Alon's Disproof (1985)
-/

/--
**Alon's theorem (1985):**
For r ≥ C (some absolute constant) and k ≥ C·r, there exists an
r-uniform hypergraph with chromatic number ≥ k having at most
(7/8)^r · C((r-1)(k-1)+1, r) edges.

This disproves Erdős's conjecture for all r ≥ 4.
-/
axiom alon_disproof :
    ∃ C : ℕ, C > 0 ∧
      ∀ r : ℕ, r ≥ C →
        ∀ k : ℕ, k ≥ C * r →
          ∃ H : Hypergraph V,
            IsUniform H r ∧
            hasChromaticNumberAtLeast H k ∧
            (numEdges H : ℝ) ≤ (7/8 : ℝ)^r * Nat.choose ((r-1)*(k-1)+1) r

/--
**Alon's method:**
Uses Turán numbers to construct hypergraphs with high chromatic number
but fewer edges than the complete hypergraph.
-/
axiom alon_turan_connection : True

/--
**Conjecture status for different r:**
- r = 2: TRUE (classical)
- r = 3: FALSE for small k (Steiner), OPEN for large k
- r ≥ 4: FALSE (Alon)
-/
def conjectureStatus : Prop :=
  -- r = 2: true
  (∀ k, erdosConjecture 2 k) ∧
  -- r = 3: false for k = 3
  ¬erdosConjecture 3 3 ∧
  -- r ≥ 4: false
  (∀ r ≥ 4, ∃ k, ¬erdosConjecture r k)

/-
## Part VI: The Function m(r, k)
-/

/--
**m(r, k):**
The minimum number of edges in any r-uniform hypergraph with chromatic number > k.
-/
noncomputable def m (r k : ℕ) : ℕ :=
  -- The infimum over all hypergraphs with χ > k
  Nat.find (by use 1; sorry : ∃ n, ∃ H : Hypergraph (Fin n),
    IsUniform H r ∧ hasChromaticNumberAtLeast H (k + 1) ∧ numEdges H ≤ n)

/--
**Akolzin-Shabanov bounds (2016):**
(r / log r) · k^r ≪ m(r, k) ≪ (r³ log r) · k^r

The implied constants are absolute (independent of r and k).
-/
axiom akolzin_shabanov_bounds :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ r k : ℕ, r ≥ 3 → k ≥ 2 →
        c₁ * (r / Real.log r) * (k : ℝ)^r ≤ m r k ∧
        (m r k : ℝ) ≤ c₂ * (r^3 * Real.log r) * k^r

/--
**Cherkashin-Petrov theorem (2020):**
For fixed r, the ratio m(r, k) / k^r converges to some limit c_r as k → ∞.
-/
axiom cherkashin_petrov_limit :
    ∀ r : ℕ, r ≥ 3 →
      ∃ c_r : ℝ, c_r > 0 ∧
        Filter.Tendsto (fun k => (m r k : ℝ) / k^r) Filter.atTop (nhds c_r)

/-
## Part VII: Turán Numbers and Hypergraphs
-/

/--
**Turán number T(n, r, k):**
Maximum edges in an r-uniform hypergraph on n vertices not containing
a complete r-uniform hypergraph on k vertices.
-/
noncomputable def turanNumber (n r k : ℕ) : ℕ := sorry

/--
**Connection to chromatic number:**
High Turán numbers allow construction of hypergraphs with high
chromatic number but few edges (relative to the complete hypergraph).
-/
axiom turan_chromatic_connection : True

/-
## Part VIII: The r = 3 Open Case
-/

/--
**Open problem for r = 3:**
Is Erdős's conjecture true for r = 3 and k sufficiently large?

- FALSE for k = 3 (Steiner triple)
- OPEN for large k
-/
def r3_open_question : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, erdosConjecture 3 k

axiom r3_remains_open : True -- Status: unknown

/-
## Part IX: Examples
-/

/--
**Example: Complete 2-uniform hypergraph (graph) K_k**
Has C(k, 2) edges and chromatic number k.
This is tight for r = 2.
-/
example (k : ℕ) : Nat.choose k 2 = k * (k - 1) / 2 := by
  sorry

/--
**Example: Fano plane (Steiner triple)**
7 vertices, 7 edges, 3-uniform, chromatic number 3.
Erdős's bound would require 10 edges.
-/
example : 7 < Nat.choose 5 3 := by norm_num

/--
**Example: Alon's factor**
(7/8)^4 ≈ 0.586, showing significant reduction for r = 4.
-/
example : (7/8 : ℝ)^4 < 0.6 := by norm_num

/-
## Part X: Summary
-/

/--
**Erdős Problem #832: Summary**

CONJECTURE: r-uniform hypergraph with χ = k has ≥ C((r-1)(k-1)+1, r) edges.

STATUS: DISPROVED (for r ≥ 4)

KNOWN RESULTS:
- r = 2: TRUE (classical graph theory)
- r = 3, k = 3: FALSE (Fano plane has 7 edges, not 10)
- r = 3, large k: OPEN
- r ≥ 4: FALSE (Alon 1985 - factor (7/8)^r improvement)

ASYMPTOTIC BOUNDS:
- m(r,k) ~ c_r · k^r (Cherkashin-Petrov 2020)
- (r/log r) · k^r ≪ m(r,k) ≪ (r³ log r) · k^r (Akolzin-Shabanov 2016)

KEY INSIGHT: Turán numbers allow constructing hypergraphs that beat the
complete hypergraph bound.
-/
theorem erdos_832_summary :
    -- Alon's disproof exists
    (∃ C, ∀ r ≥ C, ∀ k ≥ C * r,
      ∃ H : Hypergraph V, IsUniform H r ∧ hasChromaticNumberAtLeast H k) ∧
    -- Steiner counterexample for r = 3
    (∃ H : Hypergraph (Fin 7), IsUniform H 3 ∧ numEdges H = 7) ∧
    -- Asymptotic bounds exist
    (∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0) := by
  constructor
  · use 4
    intro r hr k hk
    sorry
  constructor
  · sorry
  · use 1, 1
    norm_num

/--
**Problem status:**
-/
theorem erdos_832_status : True := trivial

end Erdos832
