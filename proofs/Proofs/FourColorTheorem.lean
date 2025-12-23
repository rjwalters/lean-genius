import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Four Color Theorem

## What This Proves
Every planar graph can be colored with at most four colors such that
no two adjacent vertices share the same color.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `SimpleGraph` and
  `Coloring` definitions from the combinatorics library.
- **Original Contributions:** This file provides the conceptual framework:
  Euler's formula, the Five Color Theorem sketch, and Kempe chain ideas.
  The full proof requires computer verification of 1,936 configurations.
- **Proof Techniques Demonstrated:** Graph coloring definitions, working
  with Mathlib's graph API, induction on vertices.

## Status
- [ ] Complete proof
- [ ] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [x] Incomplete (has sorries)

## Mathlib Dependencies
- `SimpleGraph` : Undirected graphs without self-loops
- `SimpleGraph.Coloring` : Graph coloring with k colors
- `Fintype` : Finite types for vertex sets

Note: 5 sorries remain. The complete proof (Appel-Haken 1976) requires
computer verification; it was formally verified in Coq by Gonthier (2005)
but is not yet in Mathlib.

Historical Note: First posed in 1852, proved in 1976, and formally
verified in Coq in 2005 by Georges Gonthier.
-/

set_option linter.unusedVariables false

namespace FourColor

-- ============================================================
-- PART 1: Graph Theory Foundations
-- ============================================================

-- We use Mathlib's SimpleGraph which represents undirected graphs without self-loops
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is k-colorable if we can assign one of k colors to each vertex
    such that adjacent vertices have different colors -/
def Colorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  Nonempty (G.Coloring (Fin k))

-- Every graph with n vertices is n-colorable (assign each vertex a unique color)
theorem colorable_of_card_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    Colorable G (Fintype.card V) := by
  unfold Colorable
  -- Use the equivalence V ≃ Fin (Fintype.card V) to assign unique colors
  let e := Fintype.equivFin V
  -- Construct a coloring by mapping each vertex to its index
  exact ⟨SimpleGraph.Coloring.mk e (fun {v w} hadj heq =>
    -- Adjacent vertices have different indices since they are different vertices
    (G.ne_of_adj hadj) (e.injective heq))⟩

-- ============================================================
-- PART 2: Planar Graphs
-- ============================================================

/-- A graph is planar if it can be embedded in the plane without edge crossings.
    This is a complex topological property. We axiomatize planarity along with
    its key consequence: the edge bound from Euler's formula.

    Euler's formula states V - E + F = 2 for connected planar graphs.
    From this, we derive E ≤ 3V - 6 (when V ≥ 3):
    - Each face has ≥ 3 edges, so 2E ≥ 3F, hence F ≤ 2E/3
    - Substituting: V - E + 2E/3 ≥ 2 → E ≤ 3V - 6 -/
class Planar (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  edge_bound : ∀ (hcard : 3 ≤ Fintype.card V), G.edgeFinset.card ≤ 3 * Fintype.card V - 6

-- Planarity is preserved under subgraphs
theorem planar_of_subgraph {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    [hG : Planar G] (h : ∀ u v, H.Adj u v → G.Adj u v) : Planar H := by
  constructor
  intro hcard
  have hle : H.edgeFinset.card ≤ G.edgeFinset.card := by
    apply Finset.card_le_card
    intro e he
    simp only [SimpleGraph.mem_edgeFinset] at he ⊢
    -- Use Sym2.ind to handle the unordered pair
    exact Sym2.ind (fun u v huv => h u v huv) e he
  exact Nat.le_trans hle (hG.edge_bound hcard)

-- ============================================================
-- PART 4: Degree Bound for Planar Graphs
-- ============================================================

/-- In a planar graph, there exists a vertex of degree at most 5.
    This follows from Euler's formula and the handshaking lemma.

    Proof sketch:
    1. Handshaking lemma: Σ degree(v) = 2|E|
    2. Edge bound: |E| ≤ 3|V| - 6
    3. So Σ degree(v) ≤ 6|V| - 12
    4. Average degree < 6, so minimum degree ≤ 5 -/
theorem exists_degree_le_five (G : SimpleGraph V) [DecidableRel G.Adj] [Planar G]
    (hne : Nonempty V) :
    ∃ v : V, G.degree v ≤ 5 := by
  -- By contradiction: if all vertices have degree ≥ 6, then sum of degrees ≥ 6|V|
  by_contra h
  push_neg at h
  -- Every vertex has degree ≥ 6
  have hdeg : ∀ v : V, 6 ≤ G.degree v := fun v => h v
  -- Sum of degrees = 2 * |E| (handshaking lemma)
  have hsum : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  -- Sum of degrees ≥ 6 * |V|
  have hsum_lower : 6 * Fintype.card V ≤ ∑ v, G.degree v := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
    linarith
  -- Handle small cases separately
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hne
  -- For the main argument: if |V| ≥ 3, use edge bound
  by_cases hlarge : 3 ≤ Fintype.card V
  · -- Main case: |V| ≥ 3
    haveI : Planar G := inferInstance
    have hedge := Planar.edge_bound (G := G) hlarge
    -- 6|V| ≤ 2|E| and |E| ≤ 3|V| - 6, so 6|V| ≤ 6|V| - 12, contradiction
    have hbound : ∑ v, G.degree v ≤ 6 * Fintype.card V - 12 := by
      calc ∑ v, G.degree v = 2 * G.edgeFinset.card := hsum
        _ ≤ 2 * (3 * Fintype.card V - 6) := by linarith
        _ = 6 * Fintype.card V - 12 := by omega
    -- 6|V| ≤ sum ≤ 6|V| - 12 with |V| ≥ 3 is impossible
    omega
  · -- Small cases: |V| ∈ {1, 2}
    push_neg at hlarge
    have hsmall : Fintype.card V ≤ 2 := by omega
    -- Any vertex can have degree at most |V| - 1
    have v := hne.some
    have hdeg_bound : G.degree v < Fintype.card V := G.degree_lt_card_verts v
    -- But degree v ≥ 6 and |V| ≤ 2, so degree v ≥ 6 > 2 ≥ |V|, contradiction
    have : G.degree v ≥ 6 := hdeg v
    omega

-- ============================================================
-- PART 5: The Five Color Theorem
-- ============================================================

/-- The Five Color Theorem: Every planar graph is 5-colorable.

    Proof sketch (by induction on vertices):
    1. Base case: Empty graph is trivially 5-colorable
    2. Find a vertex v of degree ≤ 5 (exists by exists_degree_le_five)
    3. Remove v, the resulting graph G - v is still planar
    4. By induction, G - v is 5-colorable
    5. v has at most 5 neighbors, so at least one of 5 colors is available for v
    6. Assign that color to v

    The full formalization requires:
    - Vertex deletion for SimpleGraph (creating G - v)
    - Showing planarity is preserved under vertex deletion
    - Induction on Fintype.card V

    This was proved by Heawood in 1890 after finding the flaw in Kempe's
    attempted proof of the four color theorem. -/
theorem five_color_theorem (G : SimpleGraph V) [DecidableRel G.Adj] [Planar G] :
    Colorable G 5 := by
  -- We proceed by strong induction on the number of vertices
  -- The key insight: exists_degree_le_five gives us a vertex v with degree ≤ 5
  -- After removing v and coloring by induction, v has at most 5 neighbors
  -- so at least one of 5 colors is available
  cases' isEmpty_or_nonempty V with hempty hne
  · -- Empty graph is trivially 5-colorable
    exact ⟨SimpleGraph.Coloring.mk (fun v => (IsEmpty.false v).elim) (fun {u} _ => (IsEmpty.false u).elim)⟩
  · -- Non-empty graph: use induction argument
    -- Full proof requires vertex deletion which is complex in Mathlib
    -- The structure would be:
    -- 1. obtain ⟨v, hv⟩ := exists_degree_le_five G hne
    -- 2. let G' := G.deleteVertex v
    -- 3. have ih : Colorable G' 5 := five_color_theorem G'
    -- 4. extend coloring from G' to G by assigning available color to v
    sorry

-- ============================================================
-- PART 6: Kempe Chains
-- ============================================================

/-- A Kempe chain is a maximal connected subgraph using only two colors.
    Swapping colors in a Kempe chain preserves proper coloring. -/
def KempeChain (G : SimpleGraph V) (c : G.Coloring (Fin k))
    (color1 color2 : Fin k) : Set V :=
  { v | c v = color1 ∨ c v = color2 }

-- ============================================================
-- PART 7: The Four Color Theorem
-- ============================================================

/-- The Four Color Theorem: Every planar graph is 4-colorable.

    The proof requires:
    1. Showing certain configurations are "reducible" (633 configurations)
    2. Showing the set of reducible configurations is "unavoidable"
    3. Computer verification of 1,936 configurations in the discharging argument

    This was first proved by Appel and Haken (1976) using 1,200 hours of
    computer time. It was formally verified in Coq by Georges Gonthier (2005)
    in approximately 60,000 lines of Coq code.

    The formal proof uses hypermaps rather than planar graphs, as hypermaps
    provide a more tractable combinatorial representation for the proof.

    A full Lean formalization would require porting Gonthier's approach,
    which is a substantial undertaking beyond the scope of this proof sketch.

    Note: This theorem is an axiom in this formalization. The statement
    is mathematically true (proven by Appel-Haken and verified by Gonthier). -/
theorem four_color_theorem (G : SimpleGraph V) [DecidableRel G.Adj] [Planar G] :
    Colorable G 4 := by
  -- This theorem requires computer-assisted proof (1,936 configurations)
  -- Formally verified in Coq by Gonthier (2005)
  -- A full Lean port would require ~60,000 lines of formalization
  sorry

-- The four color theorem implies five-colorability
theorem four_implies_five (G : SimpleGraph V) [DecidableRel G.Adj] [Planar G] :
    Colorable G 4 → Colorable G 5 := by
  intro h
  -- A 4-coloring can be converted to a 5-coloring by embedding Fin 4 into Fin 5
  unfold Colorable at *
  obtain ⟨c⟩ := h
  -- Compose the coloring with Fin.castSucc : Fin 4 → Fin 5
  exact ⟨SimpleGraph.Coloring.mk (fun v => Fin.castSucc (c v)) (fun {u v} hadj heq =>
    (c.valid hadj) (Fin.castSucc_injective _ heq))⟩

-- ============================================================
-- PART 8: Historical Significance
-- ============================================================

/-!
### Historical Notes

The Four Color Problem has a remarkable history:

- **1852**: Francis Guthrie poses the question while coloring a map of England
- **1879**: Kempe publishes an "proof" using his chain argument
- **1890**: Heawood finds an error in Kempe's proof, but salvages 5-color theorem
- **1976**: Appel and Haken prove the theorem using 1,200 hours of computer time
- **2005**: Gonthier formally verifies the proof in Coq

This was one of the first major theorems proved with essential computer assistance,
and the first to be formally verified in a proof assistant.

### The Gonthier Formalization

The Coq formalization by Georges Gonthier:
- Uses hypermaps instead of planar graphs
- Verifies all 633 reducibility arguments
- The proof is approximately 60,000 lines of Coq
- It was later extracted to a verified program

The formal proof provides absolute certainty about a result that
was controversial due to its computer-assisted nature.
-/

end FourColor

-- Export main theorems
#check FourColor.four_color_theorem
#check FourColor.five_color_theorem
