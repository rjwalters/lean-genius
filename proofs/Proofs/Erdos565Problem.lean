/-
Erdős Problem #565: Induced Ramsey Numbers

Source: https://erdosproblems.com/565
Status: SOLVED by Aragão, Campos, Dahia, Filipe, and Marciano (2025)

Statement:
Let R*(G) be the induced Ramsey number: the minimal m such that there exists
a graph H on m vertices such that any 2-coloring of the edges of H contains
an induced monochromatic copy of G.

Is it true that R*(G) ≤ 2^{O(n)} for any graph G on n vertices?

Background:
This problem was posed by Erdős and Rödl. Unlike ordinary Ramsey numbers
where we seek monochromatic subgraphs (not necessarily induced), induced
Ramsey numbers require that the monochromatic copy be an induced subgraph.
Even the existence of R*(G) is non-trivial.

Historical Progress:
- 1973: Rödl proved existence for bipartite graphs
- 1975: Deuber, and independently Erdős-Hajnal-Pósa, proved existence in general
- 1998: Kohayakawa-Prömel-Rödl: R*(G) < 2^{O(n(log n)²)}
- 2008: Fox-Sudakov: Alternative proof of the same bound
- 2012: Conlon-Fox-Sudakov: R*(G) < 2^{O(n log n)}
- 2025: Aragão et al.: R*(G) < 2^{O(n)} ✓ (Solves the problem!)

Key Insight:
The induced constraint makes the problem much harder than ordinary Ramsey.
The breakthrough uses probabilistic methods and careful structural analysis.

References:
- Aragão et al. "An exponential upper bound for induced Ramsey numbers." (2025)
- Conlon-Fox-Sudakov. "On two problems in graph Ramsey theory." Combinatorica (2012)
- Kohayakawa-Prömel-Rödl. "Induced Ramsey numbers." Combinatorica (1998)

Tags: ramsey-theory, graph-theory, extremal-combinatorics

Formalization status: 0 sorries, 3 axioms (the deep upper/lower bounds of
Aragão et al. and the existence theorem of Deuber/EHP/Rödl, all legitimately
axiomatized). The comparison `induced_ramsey_ge_ordinary` (R*(G) ≥ R(G)) is now
proved from the definitions. The `EdgeColoring` definition was corrected to
index over `G.edgeSet` (so `c ⟨s(a,b), h⟩` typechecks via `mem_edgeSet`, which
is `Iff.rfl`); the previous `Sym2.out`-based predicate did not match the
`Adj`-typed witnesses at the application sites. Build-pending: the local olean
cache is unavailable (circular `proofs/.lake` symlink), so this is verified by
name-check against Mathlib v4.26.0 and gated by the deployer build.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real SimpleGraph

namespace Erdos565

/- ## Part I: Graph Basics
-/

/--
**Simple Graph:**
We work with simple graphs (undirected, no loops, no multi-edges).
-/
abbrev Graph (V : Type*) [Fintype V] [DecidableEq V] := SimpleGraph V

/--
**Number of vertices:**
-/
def numVertices {V : Type*} [Fintype V] [DecidableEq V] (_ : Graph V) : ℕ :=
  Fintype.card V

/- ## Part II: Induced Subgraphs
-/

/--
**Induced Subgraph:**
G' is an induced subgraph of G on vertex set S if:
- V(G') = S
- E(G') = all edges of G with both endpoints in S
-/
def IsInducedSubgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : Graph V) (S : Set V) (G' : Graph S) : Prop :=
  ∀ u v : S, G'.Adj u v ↔ G.Adj (↑u : V) (↑v : V)

/--
**Induced Copy:**
Graph H contains an induced copy of G if there exists a subset S of V(H)
with |S| = |V(G)| such that the induced subgraph on S is isomorphic to G.
-/
def ContainsInducedCopy {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H : Graph W) (G : Graph V) : Prop :=
  ∃ f : V ↪ W, ∀ u v : V, G.Adj u v ↔ H.Adj (f u) (f v)

/- ## Part III: Edge Colorings
-/

/--
**2-Edge-Coloring:**
A 2-coloring of edges assigns each edge one of two colors (Red or Blue).
-/
inductive EdgeColor : Type where
  | Red : EdgeColor
  | Blue : EdgeColor
deriving DecidableEq

/--
**Edge coloring of a graph:**
-/
def EdgeColoring {V : Type*} [Fintype V] [DecidableEq V] (G : Graph V) :=
  { e : Sym2 V // e ∈ G.edgeSet } → EdgeColor

/--
**Monochromatic induced subgraph:**
An induced subgraph is monochromatic if all its edges have the same color.
-/
def HasMonochromaticInducedCopy {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H : Graph W) (c : EdgeColoring H) (G : Graph V) : Prop :=
  ∃ color : EdgeColor,
    ∃ f : V ↪ W,
      (∀ u v : V, G.Adj u v ↔ H.Adj (f u) (f v)) ∧
      (∀ u v : V, G.Adj u v → ∃ he : H.Adj (f u) (f v),
        c ⟨⟦(f u, f v)⟧, he⟩ = color)

/- ## Part IV: Induced Ramsey Numbers
-/

/--
**Induced Ramsey Property:**
A graph H has the induced Ramsey property for G if every 2-coloring
of H's edges contains a monochromatic induced copy of G.
-/
def HasInducedRamseyProperty {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H : Graph W) (G : Graph V) : Prop :=
  ∀ c : EdgeColoring H, HasMonochromaticInducedCopy H c G

/--
**Induced Ramsey Number R*(G):**
The minimal number of vertices m such that there exists a graph H on m
vertices with the induced Ramsey property for G.
-/
noncomputable def inducedRamseyNumber (n : ℕ) (G : Graph (Fin n)) : ℕ :=
  sInf { m : ℕ | ∃ (H : Graph (Fin m)), HasInducedRamseyProperty H G }

/- ## Part V: Existence of R*(G)
-/

/--
**Existence Theorem (Deuber 1975, Erdős-Hajnal-Pósa 1975, Rödl 1973):**
For any graph G, the induced Ramsey number R*(G) exists (is finite).
-/
axiom induced_ramsey_exists :
  ∀ n : ℕ, ∀ G : Graph (Fin n),
    ∃ m : ℕ, ∃ H : Graph (Fin m), HasInducedRamseyProperty H G

/--
**Well-defined:**
The existence theorem implies the set in inducedRamseyNumber is non-empty.
-/
theorem induced_ramsey_number_finite (n : ℕ) (G : Graph (Fin n)) :
    { m : ℕ | ∃ (H : Graph (Fin m)), HasInducedRamseyProperty H G }.Nonempty := by
  obtain ⟨m, H, hH⟩ := induced_ramsey_exists n G
  exact ⟨m, H, hH⟩

/- ## Part VI: Historical Bounds
-/

/--
**Rödl's Bipartite Bound (1973):**
For bipartite graphs G on n vertices, R*(G) ≤ 2^{O(n)}.
-/
/--
**Kohayakawa-Prömel-Rödl Bound (1998):**
R*(G) < 2^{O(n(log n)²)} for all graphs G on n vertices.
-/
/--
**Conlon-Fox-Sudakov Bound (2012):**
R*(G) < 2^{O(n log n)} for all graphs G on n vertices.
-/
/- ## Part VII: The Solution - Aragão et al. (2025)
-/

/--
**Main Theorem (Aragão, Campos, Dahia, Filipe, Marciano 2025):**
R*(G) ≤ 2^{O(n)} for all graphs G on n vertices.

This resolves Erdős Problem #565 affirmatively!
-/
axiom aragao_et_al_theorem :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
      ∀ G : Graph (Fin n),
        (inducedRamseyNumber n G : ℝ) ≤ 2^(C * n)

/--
**Erdős Problem #565: Solution**
Is R*(G) ≤ 2^{O(n)} for all n-vertex graphs G? YES!
-/
theorem erdos_565_solution :
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n ≥ 1 →
        ∀ G : Graph (Fin n),
          (inducedRamseyNumber n G : ℝ) ≤ 2^(C * n) :=
  aragao_et_al_theorem

/- ## Part VIII: Comparison with Ordinary Ramsey Numbers
-/

/--
**Ordinary Ramsey Number R(G):**
The minimal m such that any 2-coloring of K_m contains a monochromatic
(not necessarily induced) copy of G.
-/
noncomputable def ordinaryRamseyNumber (n : ℕ) (G : Graph (Fin n)) : ℕ :=
  sInf { m : ℕ | ∀ c : EdgeColoring (completeGraph (Fin m)),
    ∃ color : EdgeColor,
      ∃ f : Fin n ↪ Fin m,
        ∀ u v : Fin n, G.Adj u v → ∃ he : (completeGraph (Fin m)).Adj (f u) (f v),
          c ⟨⟦(f u, f v)⟧, he⟩ = color }

/--
**R*(G) ≥ R(G):**
Induced Ramsey numbers are at least as large as ordinary Ramsey numbers.
-/
theorem induced_ramsey_ge_ordinary (n : ℕ) (G : Graph (Fin n)) :
    inducedRamseyNumber n G ≥ ordinaryRamseyNumber n G := by
  -- The set of orders realizing the induced Ramsey property is contained in the
  -- set realizing the ordinary one, so `sInf` monotonicity gives the inequality.
  -- Concretely: the induced Ramsey number `M = inducedRamseyNumber n G` is realized
  -- by some host graph `H` on `Fin M`; since `H ≤ ⊤ = completeGraph`, every
  -- monochromatic induced copy of `G` in `H` is a (not necessarily induced)
  -- monochromatic copy of `G` in `K_M`, so `K_M` realizes the ordinary property.
  rw [ge_iff_le]
  unfold ordinaryRamseyNumber
  apply Nat.sInf_le
  -- `M` is realized by a host graph `H`.
  have hne : { m : ℕ | ∃ H : Graph (Fin m), HasInducedRamseyProperty H G }.Nonempty := by
    obtain ⟨m, H, hH⟩ := induced_ramsey_exists n G
    exact ⟨m, H, hH⟩
  have hmem : inducedRamseyNumber n G ∈
      { m : ℕ | ∃ H : Graph (Fin m), HasInducedRamseyProperty H G } := Nat.sInf_mem hne
  obtain ⟨H, hH⟩ := hmem
  -- Show `K_M` has the ordinary Ramsey property.
  simp only [Set.mem_setOf_eq]
  intro c
  -- Restrict the complete-graph coloring to `H` (`H ≤ ⊤ = completeGraph`).
  have hsub : H.edgeSet ⊆ (completeGraph (Fin (inducedRamseyNumber n G))).edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr le_top
  obtain ⟨color, f, _hiso, hmono⟩ := hH (fun e => c ⟨e.1, hsub e.2⟩)
  refine ⟨color, f, ?_⟩
  intro u v huv
  obtain ⟨heH, hcol⟩ := hmono u v huv
  -- `H.Adj (f u) (f v)` forces `f u ≠ f v`, hence adjacency in the complete graph;
  -- the colour values agree by proof irrelevance of the edge-membership witness.
  exact ⟨heH.ne, hcol⟩

/--
**Gap can be large:**
There exist graphs where R*(G) is much larger than R(G).
For example, complete bipartite graphs can exhibit superpolynomial gaps.
-/
/- ## Part IX: Lower Bounds
-/

/--
**Exponential Lower Bound:**
There exist graphs G on n vertices with R*(G) ≥ 2^{cn} for some c > 0.
-/
axiom exponential_lower_bound :
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
      ∃ G : Graph (Fin n), (inducedRamseyNumber n G : ℝ) ≥ 2^(c * n)

/--
**Tightness:**
The 2^{O(n)} bound is essentially tight (up to constants in the exponent).
-/
theorem bound_essentially_tight :
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → ∀ G : Graph (Fin n),
      (inducedRamseyNumber n G : ℝ) ≤ 2^(C * n)) ∧
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → ∃ G : Graph (Fin n),
      (inducedRamseyNumber n G : ℝ) ≥ 2^(c * n)) := by
  exact ⟨aragao_et_al_theorem, exponential_lower_bound⟩

/- ## Part X: Summary
-/

/--
**Erdős Problem #565: Summary**

**Question (Erdős-Rödl):**
Is R*(G) ≤ 2^{O(n)} for all n-vertex graphs G?

**Answer:**
YES! Proved by Aragão, Campos, Dahia, Filipe, and Marciano (2025).

**Progress:**
- 1973-75: Existence proved (Deuber, EHP, Rödl)
- 1998: 2^{O(n(log n)²)} bound (KPR)
- 2012: 2^{O(n log n)} bound (CFS)
- 2025: 2^{O(n)} bound (ACDFM) ✓

**Key Points:**
- Induced Ramsey numbers require monochromatic INDUCED subgraphs
- Much harder than ordinary Ramsey numbers
- Exponential bound is tight (matching lower bounds exist)
-/
theorem erdos_565_summary :
    -- Upper bound: 2^{O(n)} (Aragão et al. 2025)
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → ∀ G : Graph (Fin n),
      (inducedRamseyNumber n G : ℝ) ≤ 2^(C * n)) ∧
    -- Lower bound exists: 2^{Ω(n)}
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → ∃ G : Graph (Fin n),
      (inducedRamseyNumber n G : ℝ) ≥ 2^(c * n)) :=
  ⟨aragao_et_al_theorem, exponential_lower_bound⟩

end Erdos565
