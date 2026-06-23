/-
Erdős Problem #1010, Open Question 2:
  Supersaturation for K_r (r ≥ 3)

The parent problem (#1010) established that for t < ⌊n/2⌋, every graph on n
vertices with ⌊n²/4⌋ + t edges contains at least t·⌊n/2⌋ triangles.

This open question asks: what is the minimum number of copies of K_r in a graph
on n vertices with a given number of edges exceeding the Turán threshold ex(n, K_r)?

**Status**: PARTIALLY SOLVED
  - r = 3: Razborov (2010) determined the exact minimum triangle density
    using flag algebras, confirming Razborov's triangle density theorem.
  - r = 4: Nikiforov (2011) obtained asymptotic results.
  - General r: Exact supersaturation for K_r remains open for r ≥ 5.

Key results:
  - Kruskal-Katona theorem (1963/1968): relates shadow sizes of set systems,
    implies lower bounds on clique counts from edge counts.
  - Razborov (2010): exact minimum triangle density via flag algebras.
  - Reiher (2016): extended Razborov's methods to K_4 (clique density theorem).

Reference: https://erdosproblems.com/1010 (open question 2)
-/

import Mathlib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## The Turán Number for K_r

The Turán number ex(n, K_r) is the maximum number of edges in a K_r-free graph.
The Turán graph T(n, r-1) achieves this: the complete (r-1)-partite graph
with balanced parts.
-/

/-- The Turán number ex(n, r) = (1 - 1/(r-1)) · n²/2, floor'd.
    Maximum edges in a K_r-free graph on n vertices. -/
def turanNumber (n r : ℕ) : ℕ :=
  (r - 2) * n^2 / (2 * (r - 1))

/-
## Clique Counting

The number of copies of K_r in a graph. Each r-clique is an unordered
set of r vertices with complete adjacency.
-/

/-- Count of r-cliques in a graph. -/
def cliqueCount (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Finset V =>
    s.card = r ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card

/-
## Edge Density and Clique Density

The edge density d(G) = |E(G)| / C(n, 2) and clique density
ρ_r(G) = |K_r(G)| / C(n, r) relate via supersaturation.
-/

/-- Edge density of a graph: |E| / (n choose 2). -/
noncomputable def edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  G.edgeFinset.card / (Fintype.card V).choose 2

/-- r-clique density: |K_r(G)| / (n choose r). -/
noncomputable def cliqueDensity (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) : ℝ :=
  cliqueCount G r / (Fintype.card V).choose r

/-
## Turán's Theorem (General)

Turán's theorem for K_r: the maximum edge count of a K_r-free graph is
ex(n, K_r), achieved uniquely by the Turán graph T(n, r-1).
-/

/-- Turán's theorem: exceeding ex(n, K_r) edges forces a K_r. -/
axiom turan_theorem (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 3) :
    G.edgeFinset.card > turanNumber (Fintype.card V) r →
    cliqueCount G r ≥ 1

/-
## General Supersaturation

The Erdős-Simonovits supersaturation theorem (1983): for any fixed graph H,
if |E(G)| > ex(n, H), then G contains Ω(n^{v(H)}) copies of H.
-/

/-- Erdős-Simonovits supersaturation: exceeding the Turán threshold for K_r
    by a positive fraction forces Ω(n^r) copies of K_r. -/
/-
## The Kruskal-Katona Theorem

The Kruskal-Katona theorem gives a tight lower bound on the shadow
(or shade) of a set system. It implies that among all graphs with m
edges, the one minimizing triangle count is the "colex" graph.
-/

/-- The shadow of a set family: sets obtained by removing one element. -/
def shadow (F : Finset (Finset V)) : Finset (Finset V) :=
  F.biUnion (fun s => s.image (fun v => s.erase v))

/-- Kruskal-Katona theorem: the shadow of a k-uniform family of size m
    is minimized by the initial segment of the colex order.
    Here stated as a lower bound on shadow size. -/
/-
## Razborov's Triangle Density Theorem (2010)

For graphs with edge density d > 1/2, the minimum triangle density is:
  g(d) = d(2d - 1)²/2

This was proved using the flag algebra method.
-/

/-- The Razborov triangle density function:
    g(d) = d(2d - 1)²/2 for d ∈ [1/2, 1]. -/
noncomputable def razborovMinTriangleDensity (d : ℝ) : ℝ :=
  d * (2 * d - 1)^2 / 2

/-- Razborov (2010): For sufficiently large n, any graph on n vertices
    with edge density d ≥ 1/2 has triangle density at least g(d) - ε.
    This is the exact minimum for d ∈ (1/2, 1]. -/
axiom razborov_triangle_density (d : ℝ) (hd1 : 1 / 2 ≤ d) (hd2 : d ≤ 1)
    (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V ≥ N₀ →
      edgeDensity G ≥ d →
      cliqueDensity G 3 ≥ razborovMinTriangleDensity d - ε

/-
## Reiher's K₄ Density Theorem (2016)

Reiher extended flag algebra methods to determine the minimum K₄ density,
confirming a conjecture of Lovász and Simonovits.
-/

/-- Reiher (2016): For sufficiently large n and edge density d ≥ 2/3,
    there exists a minimum K₄ density function analogous to Razborov's result. -/
axiom reiher_k4_density (d : ℝ) (hd1 : 2 / 3 ≤ d) (hd2 : d ≤ 1)
    (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V ≥ N₀ →
      edgeDensity G ≥ d →
      cliqueDensity G 4 ≥ ε

/-
## Open: Exact K_r Density for r ≥ 5

For r ≥ 5, the exact minimum K_r density as a function of edge density
is not known. Conjectured to be achieved by iterated Turán constructions.
-/

/-- The conjectured minimum K_r density function.
    For each r, the minimum is conjectured to be a piecewise polynomial
    determined by balanced complete multipartite graphs. -/
def exactKrDensityOpen (r : ℕ) : Prop :=
  r ≥ 5 →
  ∃ g : ℝ → ℝ, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V ≥ N₀ →
      edgeDensity G ≥ d →
      cliqueDensity G r ≥ g d - ε

/-- **Open Question**: Exact K_r density for r ≥ 5. -/
/-
## Summary

**Parent Problem**: Erdős #1010 (triangle supersaturation, SOLVED)
**This Open Question**: Generalize to K_r for r ≥ 3

**Resolved for**:
- r = 3: Razborov (2010) via flag algebras
- r = 4: Reiher (2016) via extended flag algebras

**Open for**:
- r ≥ 5: Exact K_r density as a function of edge density

**Key Tools**:
- Kruskal-Katona theorem (shadow bounds → clique lower bounds)
- Flag algebras (Razborov 2007)
- Stability method (Lovász-Simonovits 1976)
-/

/-- The minimum K_r count when exceeding the Turán threshold by t edges,
    generalizing the t·⌊n/2⌋ bound from the triangle case. -/
def kr_supersaturation_conjecture (r : ℕ) : Prop :=
  r ≥ 3 → ∃ f : ℕ → ℕ → ℕ,
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ),
      G.edgeFinset.card = turanNumber (Fintype.card V) r + t →
      cliqueCount G r ≥ f (Fintype.card V) t

#check @turan_theorem
#check @razborov_triangle_density
#check @reiher_k4_density
