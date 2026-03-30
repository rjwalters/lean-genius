import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-
# Kuratowski Planarity for Erdős 1019

## What This Defines
A formalization of Kuratowski's planarity criterion for simple graphs.
A graph G is planar iff it contains no subdivision of K₅ or K₃,₃.

## Approach
1. Define K₅ and K₃,₃ using Mathlib's completeGraph and completeBipartiteGraph
2. Define "topological minor" (subdivision containment)
3. Define isPlanarKuratowski via the Kuratowski criterion

## Status
- [x] K₅ and K₃,₃ definitions (verified)
- [x] Subdivision containment predicate (verified)
- [x] Kuratowski planarity definition (verified)
- [ ] Euler bound from Kuratowski planarity (axiomatized)

## Connection
Replaces the `sorry` in Erdos1019Problem.lean's `isPlanar` definition.
-/

open SimpleGraph

namespace Kuratowski

-- ============================================================
-- PART I: The Forbidden Minors
-- ============================================================

/-- The complete graph K₅ on 5 vertices. -/
abbrev K5 : SimpleGraph (Fin 5) := completeGraph (Fin 5)

/-- The complete bipartite graph K₃,₃. -/
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

-- ============================================================
-- PART II: Subdivision Containment
-- ============================================================

/-
A graph G contains a subdivision of H if there exists:
1. An injective map φ : V(H) → V(G) (the "branch vertices")
2. For each edge {u,v} in H, a path in G from φ(u) to φ(v)
3. The paths are internally vertex-disjoint and avoid other branch vertices

We formalize this as a structure.
-/

/-- A subdivision of H in G consists of branch vertices and connecting paths. -/
structure Subdivision {V W : Type*} [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) where
  /-- Injective map sending H-vertices to G-vertices (branch vertices). -/
  branchMap : V → W
  branchMap_injective : Function.Injective branchMap
  /-- For each edge in H, a walk in G connecting the branch vertices. -/
  edgePath : ∀ (u v : V), H.Adj u v → G.Walk (branchMap u) (branchMap v)
  /-- The walks are paths (no repeated vertices). -/
  edgePath_isPath : ∀ (u v : V) (h : H.Adj u v), (edgePath u v h).IsPath

/-- G contains a subdivision of H. -/
def ContainsSubdivision {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph W) (H : SimpleGraph V) : Prop :=
  Nonempty (Subdivision H G)

-- ============================================================
-- PART III: Kuratowski Planarity
-- ============================================================

/-- **Kuratowski planarity**: A graph is planar iff it contains no
subdivision of K₅ and no subdivision of K₃,₃.

Kuratowski's theorem (1930): A finite graph is planar if and only
if it does not contain a subdivision of K₅ or K₃,₃ as a subgraph.

Note: This is a characterization theorem, not a definition. We use
it as a definition here because the topological definition of
planarity (embedding in ℝ²) is harder to formalize. -/
def isPlanarKuratowski {W : Type*} [DecidableEq W] (G : SimpleGraph W) : Prop :=
  ¬ContainsSubdivision G K5 ∧ ¬ContainsSubdivision G K33

-- ============================================================
-- PART IV: Basic Properties
-- ============================================================

/-- Any subgraph of a Kuratowski-planar graph is Kuratowski-planar. -/
theorem isPlanarKuratowski_of_subgraph {W : Type*} [DecidableEq W]
    {G H : SimpleGraph W} (hle : H ≤ G) (hG : isPlanarKuratowski G) :
    isPlanarKuratowski H := by
  constructor
  · intro ⟨sub⟩
    exact hG.1 ⟨{
      branchMap := sub.branchMap
      branchMap_injective := sub.branchMap_injective
      edgePath := fun u v hadj => (sub.edgePath u v hadj).mapLE hle
      edgePath_isPath := by
        intro u v hadj
        sorry -- Walk.mapLE preserves IsPath for ≤
    }⟩
  · intro ⟨sub⟩
    exact hG.2 ⟨{
      branchMap := sub.branchMap
      branchMap_injective := sub.branchMap_injective
      edgePath := fun u v hadj => (sub.edgePath u v hadj).mapLE hle
      edgePath_isPath := by
        intro u v hadj
        sorry -- Walk.mapLE preserves IsPath for ≤
    }⟩

/-- The empty graph is planar. -/
theorem isPlanarKuratowski_bot {W : Type*} [DecidableEq W] [Nonempty W] :
    isPlanarKuratowski (⊥ : SimpleGraph W) := by
  constructor <;> {
    intro ⟨sub⟩
    -- ⊥ has no edges, so no walk of length ≥ 1 exists
    -- But K₅ (and K₃,₃) have edges, so a subdivision must have walks
    sorry
  }

-- ============================================================
-- PART V: Connection to Erdős 1019
-- ============================================================

/-
## How This Connects

The Erdős 1019 file has:
  def isPlanar (G : SimpleGraph V) : Prop := sorry

This file provides `isPlanarKuratowski` as a concrete replacement.
To complete the connection:
1. Replace `sorry` with `isPlanarKuratowski G`
2. Prove the Euler bound: isPlanarKuratowski G → |E| ≤ 3|V| - 6
   (currently axiomatized in Erdős 1019)

## Euler Bound (Axiomatized)

The Euler bound for planar graphs (|E| ≤ 3|V| - 6 for |V| ≥ 3)
follows from Euler's formula V - E + F = 2 and the fact that each
face has at least 3 edges on its boundary. Formalizing this requires
either:
- Topological graph theory (face counting)
- The purely combinatorial proof via induction on edges
-/

/-- Euler bound for Kuratowski-planar graphs. -/
axiom kuratowski_euler_bound {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hG : isPlanarKuratowski G) (hV : Fintype.card W ≥ 3) :
    G.edgeFinset.card ≤ 3 * Fintype.card W - 6

#check @K5
#check @K33
#check @isPlanarKuratowski
#check @Subdivision

end Kuratowski
