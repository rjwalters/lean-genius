/-
  Hypergraph Regularity Core Definitions

  Generalization of graph regularity (SzemerediCore.lean) to k-uniform
  hypergraphs, following Gowers (2007) and Rödl–Skokan (2004).

  For graphs (k=2), regularity says that large subsets of a bipartite
  pair have nearly the same edge density. For k-uniform hypergraphs,
  regularity is more subtle: it is defined relative to an underlying
  system of (k-1)-graphs (a "complex"), and asks that the k-edge
  density does not change when we restrict to a dense sub-complex.

  This module formalizes:
  - UHypergraph: centralized r-uniform hypergraph definition
  - kPartiteDensity: fraction of transversals that are edges
  - IsHypergraphRegular: naive ε-regularity for k-partite k-graphs
  - Basic lemmas: density bounds [0,1], non-negativity

  The full Gowers (2007) relative regularity (with respect to underlying
  simplicial complexes) is stated as a follow-up direction.

  References:
  - Gowers, W.T. "Hypergraph regularity and the multidimensional
    Szemerédi theorem" (2007)
  - Rödl, V. and Skokan, J. "Regularity lemma for k-uniform
    hypergraphs" (2004)
  - Nagle, B., Rödl, V., Schacht, M. "The counting lemma for regular
    k-uniform hypergraphs" (2006)
-/
import Mathlib

namespace Szemeredi.Hypergraph

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: k-UNIFORM HYPERGRAPH
-- ═══════════════════════════════════════════════════════════════════

/-- A k-uniform hypergraph on vertex set V.
    Each edge is a k-element subset of V. -/
structure UHypergraph (V : Type*) (k : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = k

/-- The number of edges in a hypergraph. -/
def UHypergraph.edgeCount {k : ℕ} (H : UHypergraph V k) : ℕ :=
  H.edges.card

/-- The empty hypergraph with no edges. -/
def UHypergraph.empty (V : Type*) [DecidableEq V] (k : ℕ) : UHypergraph V k where
  edges := ∅
  uniform := by simp

/-- Edge count of empty hypergraph is 0. -/
theorem UHypergraph.edgeCount_empty (k : ℕ) :
    (UHypergraph.empty V k).edgeCount = 0 := by
  simp [edgeCount, empty]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: k-PARTITE DENSITY
-- ═══════════════════════════════════════════════════════════════════

/-- The set of all transversals of a list of vertex sets: k-element subsets
    that pick exactly one vertex from each part. This generalizes the
    Cartesian product A × B from the graph (k=2) case.

    For parts [V₁, V₂, ..., Vₖ], a transversal is a set {v₁, v₂, ..., vₖ}
    with vᵢ ∈ Vᵢ for each i. -/
noncomputable def transversals
    (parts : List (Finset V)) : Finset (Finset V) :=
  let union := parts.foldl (· ∪ ·) ∅
  union.powerset.filter fun s =>
    s.card = parts.length ∧ ∀ P ∈ parts, (s ∩ P).card = 1

/-- k-partite density: fraction of transversals that are hypergraph edges.
    Generalizes edgeDensity G A B from SzemerediCore.lean.

    d_k(H; V₁,...,Vₖ) = |{e ∈ edges(H) : e is a transversal of (V₁,...,Vₖ)}|
                        / |transversals(V₁,...,Vₖ)|

    Returns 0 when there are no transversals (e.g., some part is empty). -/
noncomputable def kPartiteDensity {k : ℕ}
    (H : UHypergraph V k)
    (parts : List (Finset V)) : ℚ :=
  let T := transversals parts
  if (T.card : ℚ) = 0 then 0
  else (T.filter (· ∈ H.edges)).card / T.card

/-- k-partite density is non-negative. -/
theorem kPartiteDensity_nonneg {k : ℕ}
    (H : UHypergraph V k)
    (parts : List (Finset V)) :
    0 ≤ kPartiteDensity H parts := by
  unfold kPartiteDensity
  split_ifs
  · exact le_refl 0
  · positivity

/-- k-partite density is at most 1. -/
theorem kPartiteDensity_le_one {k : ℕ}
    (H : UHypergraph V k)
    (parts : List (Finset V)) :
    kPartiteDensity H parts ≤ 1 := by
  unfold kPartiteDensity
  split_ifs with h
  · exact zero_le_one
  · have hne : (transversals parts).card ≠ 0 := by
      intro h0
      exact h (by exact_mod_cast h0)
    have hpos : (0 : ℚ) < (transversals parts).card := by
      exact_mod_cast Nat.pos_of_ne_zero hne
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_filter_le _ _

-- ═══════════════════════════════════════════════════════════════════
-- PART III: HYPERGRAPH ε-REGULARITY (NAIVE VERSION)
-- ═══════════════════════════════════════════════════════════════════

/-- A k-tuple of vertex sets (V₁,...,Vₖ) is ε-regular for a k-uniform
    hypergraph H if for every choice of large subsets V'ᵢ ⊆ Vᵢ
    (each with |V'ᵢ| ≥ ε|Vᵢ|), the k-partite density changes by at
    most ε.

    This is the "naive" generalization of graph epsilon-regularity from
    SzemerediCore.IsEpsilonRegular. The full Gowers (2007) regularity
    defines regularity relative to an underlying (k-1)-complex — see
    the follow-up directions at the end of this file. -/
def IsHypergraphRegular {k : ℕ}
    (H : UHypergraph V k)
    (eps : ℚ) (parts : List (Finset V)) : Prop :=
  parts.length = k ∧
  ∀ parts' : List (Finset V),
    parts'.length = k →
    (∀ i : Fin k,
      parts'.get ⟨i.val, by omega⟩ ⊆ parts.get ⟨i.val, by omega⟩ ∧
      ((parts'.get ⟨i.val, by omega⟩).card : ℚ) ≥
        eps * (parts.get ⟨i.val, by omega⟩).card) →
    |kPartiteDensity H parts' - kPartiteDensity H parts| ≤ eps

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: DENSITY OF EMPTY HYPERGRAPH
-- ═══════════════════════════════════════════════════════════════════

/-- The density of an empty hypergraph is 0. -/
theorem kPartiteDensity_empty {k : ℕ}
    (parts : List (Finset V)) :
    kPartiteDensity (UHypergraph.empty V k) parts = 0 := by
  unfold kPartiteDensity
  split_ifs
  · rfl
  · simp [UHypergraph.empty]

-- ═══════════════════════════════════════════════════════════════════
-- PART V: LINK TO GRAPH CASE (k = 2)
-- ═══════════════════════════════════════════════════════════════════

/-- A 2-uniform hypergraph from a simple graph: each edge {u, v} where
    G.Adj u v becomes a 2-element set in the hypergraph. -/
noncomputable def fromSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    UHypergraph V 2 where
  edges := (Fintype.elems ×ˢ Fintype.elems).filter
    (fun p => G.Adj p.1 p.2) |>.image (fun p => {p.1, p.2})
  uniform := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
    obtain ⟨⟨a, b⟩, ⟨_, hadj⟩, rfl⟩ := he
    exact Finset.card_pair (G.ne_of_adj hadj)

/-
## Follow-Up Directions

### Full Gowers Hypergraph Regularity (2007)

The naive regularity defined above (IsHypergraphRegular) is insufficient
for most applications. Gowers (2007) introduced a relative version:

1. A "complex" on V is a nested family H₁ ⊆ H₂ ⊆ ... ⊆ Hₖ where
   Hⱼ is a j-uniform hypergraph and every j-edge of Hⱼ is contained
   in a (j+1)-edge of Hⱼ₊₁.

2. The density of a k-graph relative to the complex is measured by
   conditioning on the (k-1)-skeleton rather than raw transversals.

3. ε-regularity requires that density is stable when restricting to
   dense sub-complexes (not just large vertex subsets).

This relative regularity is what makes the hypergraph counting lemma
(Nagle–Rödl–Schacht 2006) work, analogous to how graph regularity
enables the graph counting lemma in SzemerediCounting.lean.

### Formalizing the Full Version

Key additional definitions needed:
- `SimplicialComplex`: nested family of j-graphs
- `relativeDensity`: density of k-graph conditioned on (k-1)-skeleton
- `IsGowersRegular`: regularity relative to simplicial complex
- `hypergraphCountingLemma`: dense regular k-graphs contain expected
  number of copies of any fixed k-graph

### References
- Gowers, W.T. (2007). "Hypergraph regularity and the multidimensional
  Szemerédi theorem." Annals of Mathematics 166(3), 897–946.
- Rödl, V. and Skokan, J. (2004). "Regularity lemma for k-uniform
  hypergraphs." Random Structures & Algorithms 25(1), 1–42.
- Nagle, B., Rödl, V., Schacht, M. (2006). "The counting lemma for
  regular k-uniform hypergraphs." Random Structures & Algorithms 28(2),
  113–179.
-/

end Szemeredi.Hypergraph
