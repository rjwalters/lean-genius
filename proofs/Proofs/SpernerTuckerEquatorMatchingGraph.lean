/-
  Sperner → Tucker program, `sperner-mathlib4-oq-02`.

  # The equatorial boundary-door matching as a genuine `SimpleGraph`, in the
  #   abstract door-counting vocabulary

  ## Where this sits

  Two previously-separate pieces of infrastructure meet here.

  * `SpernerTuckerCrossPolytopeEquator` proves the coordinate-`0` flip
    `equatorFlip` is a fixed-point-free involution and graph automorphism of the
    cube `crossGraph n = Q_{n+1}` that pairs each positive-hemisphere facet with
    exactly one negative-hemisphere facet — the *equatorial boundary door* of every
    facet at once (`equatorFlip_swaps`, `equatorFlip_maps_pos_neg`,
    `card_posHemisphere_eq_negHemisphere`).

  * `SpernerTuckerDoorGraphTower` isolates the reusable fact that in a **1-regular**
    door graph (a perfect matching) the abstract `boundaryEndpoints` /
    `interiorEndpoints` of `SpernerTuckerInductiveTower` collapse to the boundary /
    non-boundary vertices (`boundaryEndpoints_of_oneRegular`,
    `interiorEndpoints_of_oneRegular`).

  The knowledge base's stated next step was: *"apply `boundaryEndpoints_of_oneRegular`
  to the actual `equatorFlip` matching to state the cross-polytope boundary-door
  count in `boundaryEndpoints` form."*  That is exactly what this file does.

  ## What this file proves

  The equatorial boundary doors form a `SimpleGraph` in their own right:
  `equatorGraph n` on the facets `Facet n`, with `s` adjacent to `t` iff
  `t = equatorFlip n s`.  Because `equatorFlip` is a fixed-point-free involution this
  is a well-defined **perfect matching** — one disjoint edge per hemisphere pair —
  hence **1-regular** (`equatorGraph_degree`).  Feeding it to the door-counting
  collapse identifies its abstract endpoint sets with the geometric hemispheres:

    * `boundaryEndpoints (equatorGraph n) (· 0 = true) = posHemisphere n`,
    * `interiorEndpoints (equatorGraph n) (· 0 = true) = negHemisphere n`,

  so the abstract boundary-door count equals the interior-door count
  (`card_boundaryEndpoints_eq_interior_equatorGraph`, via the equatorial matching
  bijection), and at level `n+1` both equal the *lower* cross-polytope facet count
  `Fintype.card (Facet n)` (`card_boundaryEndpoints_equatorGraph_succ`) — the
  doubling recursion re-expressed in the vocabulary the tower engine
  `exists_interior_of_graph_tower` actually consumes.

  ## Honest status

  This is a **translation layer**, not new Tucker geometry.  It carries the already-
  proved equatorial matching into the abstract `boundaryEndpoints`/`interiorEndpoints`
  language and confirms the hemisphere identification is definitional under the
  1-regular collapse.  Crucially the boundary predicate here is the *raw* sign of
  coordinate `0`, for which boundary and interior counts are trivially *equal* (the
  matching is symmetric across the equator); it is **not** the asymmetric
  almost-complementary Tucker labelling whose interior count is *odd*.  Producing that
  labelling — the odd interior seed — remains the open geometric frontier, exactly as
  every prior session flagged.

  Self-contained.  Dimension-free (no `decide` / `native_decide`), 0 sorries, 0
  `axiom` declarations; the `#print axioms` guards confirm `propext` /
  `Classical.choice` / `Quot.sound` only.
-/
import Mathlib.Tactic
import Proofs.SpernerTuckerCrossPolytopeEquator
import Proofs.SpernerTuckerDoorGraphTower

namespace SpernerTuckerEquatorMatchingGraph

open Finset SimpleGraph
open SpernerTuckerCrossPolytopeBoundary
open SpernerTuckerCrossPolytopeEquator
open SpernerTuckerInductiveTower
open SpernerTuckerDoorGraphTower

variable (n : ℕ)

/-! ## The equatorial boundary-door graph -/

/-- **The equatorial boundary-door graph.**  Vertices are the facets `Facet n`; `s`
is adjacent to `t` exactly when `t` is the equatorial flip of `s`.  Since `equatorFlip`
is a fixed-point-free involution, this is a well-defined perfect matching: one edge per
hemisphere pair. -/
def equatorGraph : SimpleGraph (Facet n) where
  Adj s t := t = equatorFlip n s
  symm := by
    intro s t h
    subst h
    exact (equatorFlip_involutive n s).symm
  loopless := by
    intro s h
    exact equatorFlip_free n s h.symm

instance : DecidableRel (equatorGraph n).Adj :=
  fun s t => inferInstanceAs (Decidable (t = equatorFlip n s))

/-- The neighbor set of a facet `s` in the equatorial matching graph is the singleton
`{equatorFlip n s}`. -/
theorem equatorGraph_neighborFinset (s : Facet n) :
    (equatorGraph n).neighborFinset s = {equatorFlip n s} := by
  ext t
  simp only [mem_neighborFinset, mem_singleton]
  rfl

/-- **The equatorial matching graph is 1-regular.**  Every facet is matched to exactly
one partner — its equatorial flip. -/
theorem equatorGraph_degree (s : Facet n) : (equatorGraph n).degree s = 1 := by
  rw [← card_neighborFinset_eq_degree, equatorGraph_neighborFinset, card_singleton]

/-! ## Endpoint sets in the abstract door-counting vocabulary -/

/-- The equatorial boundary predicate reused as a `DecidablePred`: a facet is a
boundary vertex iff coordinate `0` is `true` (it lies in the positive hemisphere). -/
instance : DecidablePred (fun s : Facet n => s 0 = true) :=
  fun s => inferInstanceAs (Decidable (s 0 = true))

/-- **The abstract boundary endpoints are the positive hemisphere.**  Under the
1-regular collapse, the door-counting `boundaryEndpoints` of the equatorial matching
graph are exactly the facets on the positive hemisphere. -/
theorem boundaryEndpoints_equatorGraph :
    boundaryEndpoints (equatorGraph n) (fun s => s 0 = true) = posHemisphere n := by
  rw [boundaryEndpoints_of_oneRegular _ _ (equatorGraph_degree n)]
  rfl

/-- **The abstract interior endpoints are the negative hemisphere.**  The
complementary endpoint of each equatorial door lies on the opposite hemisphere. -/
theorem interiorEndpoints_equatorGraph :
    interiorEndpoints (equatorGraph n) (fun s => s 0 = true) = negHemisphere n := by
  rw [interiorEndpoints_of_oneRegular _ _ (equatorGraph_degree n)]
  apply Finset.filter_congr
  intro s _
  cases s 0 <;> simp

/-! ## Counts: the doubling recursion in `boundaryEndpoints` form -/

/-- **Boundary-door count equals interior-door count.**  For the raw sign predicate the
equatorial matching is symmetric across the equator, so the abstract boundary and
interior endpoint counts coincide — via the perfect matching bijection
`card_posHemisphere_eq_negHemisphere`. -/
theorem card_boundaryEndpoints_eq_interior_equatorGraph :
    #(boundaryEndpoints (equatorGraph n) (fun s => s 0 = true))
      = #(interiorEndpoints (equatorGraph n) (fun s => s 0 = true)) := by
  rw [boundaryEndpoints_equatorGraph, interiorEndpoints_equatorGraph,
    card_posHemisphere_eq_negHemisphere]

/-- **The boundary-door count at level `n+1` is the lower cross-polytope facet count.**
The abstract `boundaryEndpoints` of the equatorial matching on `∂◊^{n+2}` number
`Fintype.card (Facet n)` — the hemisphere identification of the doubling recursion,
now stated in the vocabulary `exists_interior_of_graph_tower` consumes. -/
theorem card_boundaryEndpoints_equatorGraph_succ :
    #(boundaryEndpoints (equatorGraph (n + 1)) (fun s => s 0 = true))
      = Fintype.card (Facet n) := by
  rw [boundaryEndpoints_equatorGraph, card_posHemisphere_eq_facet]

/-- The same for interior endpoints: at level `n+1` the interior-door count is also the
lower cross-polytope facet count. -/
theorem card_interiorEndpoints_equatorGraph_succ :
    #(interiorEndpoints (equatorGraph (n + 1)) (fun s => s 0 = true))
      = Fintype.card (Facet n) := by
  rw [← card_boundaryEndpoints_eq_interior_equatorGraph,
    card_boundaryEndpoints_equatorGraph_succ]

/-! ## Axiom audit — all results are 0-axiom (no `sorryAx`, no `Lean.ofReduceBool`),
dimension-free (no `decide` / `native_decide`). -/

#check @equatorGraph
#check @equatorGraph_degree
#check @boundaryEndpoints_equatorGraph
#check @card_boundaryEndpoints_equatorGraph_succ

#print axioms equatorGraph_degree
#print axioms boundaryEndpoints_equatorGraph
#print axioms interiorEndpoints_equatorGraph
#print axioms card_boundaryEndpoints_eq_interior_equatorGraph
#print axioms card_boundaryEndpoints_equatorGraph_succ

end SpernerTuckerEquatorMatchingGraph
