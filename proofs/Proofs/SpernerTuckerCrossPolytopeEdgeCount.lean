/-
  Sperner → Tucker program, `sperner-mathlib4-oq-02`.

  # Exact closed-form door (edge) counts of the cross-polytope graph, and their
  # hemisphere transport

  The cross-polytope door graph `crossGraph n` (facets `Facet n = Fin (n+1) → Bool`,
  cube-adjacency `Q_{n+1}`) has been shown `(n+1)`-regular (`facet_degree`) with
  `2^{n+1}` vertices (`card_facet`, below).  Prior sessions packaged the geometry
  around it — the equatorial perfect matching and *vertex* doubling recursion
  `card (Facet (n+1)) = 2 · card (Facet n)` (`SpernerTuckerCrossPolytopeEquator`), and
  the hemisphere graph isomorphism `hemisphereIso : (crossGraph (n+1))|hemisphere ≃g
  crossGraph n` (`SpernerTuckerCrossPolytopeHemisphereIso`) — but never the actual
  **edge count** the door-counting recursion tracks.

  This file supplies it, in exact closed form, via the handshake lemma
  (`sum_degrees_eq_twice_card_edges`) and regularity:

    * `crossGraph_card_edgeFinset` — the cross-polytope door graph has exactly
      `#(crossGraph n).edgeFinset = (n+1) · 2^n` interior doors (edges).  This is the
      **total interior-door count** the `TuckerTower.bridge` dimension induction must
      account for, now a closed form rather than a per-facet local split.

    * `crossGraph_card_edgeFinset_succ` — the **prism edge recursion**
      `#edges (crossGraph (n+1)) = 2 · #edges (crossGraph n) + card (Facet n)`.
      This is the edge-level form of the `Q_{n+2} = Q_{n+1} □ K₂` prism
      decomposition: two copies of the lower door graph (the `2 · #edges` term) joined
      by the equatorial boundary-door matching — whose cardinality is exactly
      `card (Facet n)` (`SpernerTuckerCrossPolytopeEquator.card_posHemisphere_eq_facet`:
      each hemisphere has `card (Facet n)` facets, matched perfectly across the equator
      by `equatorFlip`).  So the `+ card (Facet n)` term *is* the global boundary-door
      count, tying this edge recursion back to the equatorial matching.

    * `hemisphere_card_edgeFinset` — transport of the door count along `hemisphereIso`:
      one hemisphere of `∂◊^{n+1}` carries exactly `(n+1) · 2^n` interior doors, i.e.
      the *entire* door count of the lower cross-polytope `∂◊^{n}`.  This is the
      count-level statement of the dimension bridge — "the level-`n` interior door
      graph lives inside a level-`(n+1)` hemisphere" — now as an edge-cardinality
      equality, the shape a count-tracking `bridge` induction consumes directly.

  Honest status: exact enumerative infrastructure for `bridge` (door counts, the prism
  edge recursion, hemisphere transport), **not** a proof of `bridge`.  It does not
  install the Tucker *labelling* turning cube edges into complementary doors — the
  asymmetric almost-complementary structure carrying the odd interior seed remains the
  open frontier.  Everything here is dimension-free (no `decide` / `native_decide`) and
  0-axiom (`propext` / `Classical.choice` / `Quot.sound` only), as the `#print axioms`
  guards confirm.
-/
import Mathlib
import Proofs.SpernerTuckerCrossPolytopeHemisphereIso
import Proofs.SpernerTuckerCrossPolytopeEquator

namespace SpernerTuckerCrossPolytopeEdgeCount

open Finset SimpleGraph SpernerTuckerCrossPolytopeBoundary
  SpernerTuckerCrossPolytopeHemisphereIso SpernerTuckerCrossPolytopeEquator

variable (n : ℕ)

/-! ## Vertex count of the cross-polytope graph -/

/-- **The cross-polytope has `2^{n+1}` facets.**  `Facet n = Fin (n+1) → Bool`, so the
number of sign vectors is `2^{n+1}`.  (Stated here for use in the edge-count formulae;
`SpernerTuckerCrossPolytopeEquator.card_facet_succ` derives the *structural* doubling
`card (Facet (n+1)) = 2 · card (Facet n)` from the equatorial matching.) -/
theorem card_facet : Fintype.card (Facet n) = 2 ^ (n + 1) := by
  show Fintype.card (Fin (n + 1) → Bool) = 2 ^ (n + 1)
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-! ## Exact door (edge) count of the cross-polytope graph -/

/-- **The cross-polytope door graph has exactly `(n+1)·2^n` interior doors (edges).**
Proof by the handshake lemma: `2 · #edges = ∑_v deg v = (n+1) · card (Facet n) =
(n+1) · 2^{n+1}`, whence `#edges = (n+1) · 2^n`.  This is the total interior-door count
the dimension recursion tracks, in closed form. -/
theorem crossGraph_card_edgeFinset :
    #(crossGraph n).edgeFinset = (n + 1) * 2 ^ n := by
  have hsum : ∑ v : Facet n, (crossGraph n).degree v = 2 ^ (n + 1) * (n + 1) := by
    simp only [facet_degree, Finset.sum_const, Finset.card_univ, card_facet, smul_eq_mul]
  have h := (crossGraph n).sum_degrees_eq_twice_card_edges
  rw [hsum] at h
  -- h : 2 ^ (n + 1) * (n + 1) = 2 * #(crossGraph n).edgeFinset
  have h2 : 2 * ((n + 1) * 2 ^ n) = 2 * #(crossGraph n).edgeFinset := by
    rw [← h]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h2).symm

/-- **The prism edge recursion.**  `#edges (crossGraph (n+1)) = 2 · #edges (crossGraph n)
+ card (Facet n)`: the `(n+2)`-cube door graph has twice the interior doors of the
`(n+1)`-cube door graph, *plus* one boundary door per lower facet.  This is the
edge-level `Q_{n+2} = Q_{n+1} □ K₂` prism decomposition — two copies of the lower door
graph joined by the equatorial matching, whose size is exactly `card (Facet n)`
(`SpernerTuckerCrossPolytopeEquator.card_posHemisphere_eq_facet`). -/
theorem crossGraph_card_edgeFinset_succ :
    #(crossGraph (n + 1)).edgeFinset
      = 2 * #(crossGraph n).edgeFinset + Fintype.card (Facet n) := by
  rw [crossGraph_card_edgeFinset, crossGraph_card_edgeFinset, card_facet]
  ring

/-! ## Transport of the door count onto one hemisphere -/

/-- **One hemisphere of `∂◊^{n+1}` carries the full door count of `∂◊^{n}`.**  Transport
of `crossGraph_card_edgeFinset` along the hemisphere graph isomorphism `hemisphereIso`:
the induced subgraph on the positive hemisphere `{s | s 0 = true}` has exactly
`(n+1)·2^n` edges — the *entire* interior-door count of the lower cross-polytope
`crossGraph n`.  This is the count-level statement of the dimension bridge, as an
edge-cardinality equality. -/
theorem hemisphere_card_edgeFinset :
    #((crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = true}).edgeFinset
      = (n + 1) * 2 ^ n := by
  rw [(hemisphereIso n).card_edgeFinset_eq, crossGraph_card_edgeFinset]

/-! ## Axiom audit — all results are 0-axiom (no `sorryAx`, no `Lean.ofReduceBool`),
dimension-free (no `decide` / `native_decide`). -/

#check @card_facet
#check @crossGraph_card_edgeFinset
#check @crossGraph_card_edgeFinset_succ
#check @hemisphere_card_edgeFinset

#print axioms card_facet
#print axioms crossGraph_card_edgeFinset
#print axioms crossGraph_card_edgeFinset_succ
#print axioms hemisphere_card_edgeFinset

end SpernerTuckerCrossPolytopeEdgeCount
