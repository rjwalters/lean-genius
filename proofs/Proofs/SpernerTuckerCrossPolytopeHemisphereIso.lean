/-
  Sperner → Tucker program, `sperner-mathlib4-oq-02`.

  # The hemisphere ↔ lower-dimension GRAPH ISOMORPHISM of the cross-polytope door graph

  `SpernerTuckerCrossPolytopeHemisphere` established the coordinate-`0` drop/lift bijection
  `hemisphereEquiv : {s : Facet (n+1) // s 0 = true} ≃ Facet n` and proved, *pointwise*, that
  it preserves cube-adjacency (`hemisphere_adj_iff`: for facets in the positive hemisphere,
  `(crossGraph (n+1)).Adj s t ↔ (crossGraph n).Adj (drop s) (drop t)`).  That is the raw
  ingredient of the dimension recursion the open `TuckerTower.bridge` runs on — but a *pointwise*
  adjacency-iff is not yet a first-class object one can transport global graph properties along.

  This file packages it as a genuine **graph isomorphism**

    `hemisphereIso : (crossGraph (n+1)).induce {s | s 0 = true} ≃g crossGraph n`,

  the induced subgraph on the positive hemisphere mapped isomorphically onto the *entire* lower
  cross-polytope graph `crossGraph n`.  With the isomorphism in hand, the level-`n` structure is
  transported into a single hemisphere of the level-`(n+1)` sphere as first-class facts, exactly
  the shape `bridge` consumes:

    * `hemisphere_induce_connected` — the induced hemisphere door graph is **connected**, in
      every dimension (transport of `crossGraph_connected` along `hemisphereIso`).  This is the
      pseudomanifold-connectivity the path-following engine needs *localised to one hemisphere
      fundamental domain* — the global counterpart, inside the symmetry-broken half, of the
      ambient `SpernerTuckerCrossPolytopeConnected.crossGraph_connected`.
    * `hemisphere_induce_degree` / `hemisphere_induce_regular` — the induced hemisphere door
      graph is **`(n+1)`-regular** (transport of `facet_degree`): every hemisphere facet has, as
      *interior* doors, exactly the `n+1` neighbours of its drop in `crossGraph n`.  This is the
      graph-level upgrade of the pointwise `hemisphere_degree_split` (`#interior doors = n+1`).

  So one hemisphere of `∂◊^{n+1}` carries an `(n+1)`-regular connected graph isomorphic to the
  full lower cross-polytope `∂◊^{n}` — the precise "the level-`n` interior door graph lives inside
  a level-`(n+1)` hemisphere" statement, now as a `≃g` rather than a bare adjacency-iff.

  Honest status: geometric/graph-theoretic infrastructure for `bridge`, not a proof of `bridge`.
  It does not install the Tucker labelling that turns the cube edges into *complementary* doors
  (that labelling-broken almost-complementary structure carrying the odd interior seed remains the
  open frontier).  Everything here is dimension-free (no `decide` / `native_decide`) and 0-axiom
  (`propext` / `Classical.choice` / `Quot.sound` only), as the `#print axioms` guards confirm.
-/
import Mathlib
import Proofs.SpernerTuckerCrossPolytopeHemisphere
import Proofs.SpernerTuckerCrossPolytopeConnected

namespace SpernerTuckerCrossPolytopeHemisphereIso

open Finset SimpleGraph SpernerTuckerCrossPolytopeBoundary
  SpernerTuckerCrossPolytopeHemisphere SpernerTuckerCrossPolytopeConnected

variable (n : ℕ)

/-! ## The hemisphere as an induced subgraph, isomorphic to the lower cross-polytope -/

/-- **The hemisphere graph isomorphism.**  The subgraph of the `(n+2)`-cube `crossGraph (n+1)`
induced on the positive hemisphere `{s | s 0 = true}` is isomorphic, via the coordinate-`0` drop
`hemisphereEquiv`, to the *entire* lower cross-polytope graph `crossGraph n`.  This upgrades the
pointwise adjacency-iff `hemisphere_adj_iff` to a first-class `≃g`, so that global graph properties
(connectivity, regularity) transport between the two dimensions. -/
def hemisphereIso :
    (crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = true} ≃g crossGraph n where
  toEquiv := hemisphereEquiv n
  map_rel_iff' {a b} := by
    -- `(induce _).Adj a b` is defeq to `(crossGraph (n+1)).Adj a.1 b.1`; the map sends
    -- `a ↦ drop a.1`, so this is exactly `hemisphere_adj_iff`.
    change (crossGraph n).Adj (drop n a.1) (drop n b.1) ↔ (crossGraph (n + 1)).Adj a.1 b.1
    exact (hemisphere_adj_iff n a.2 b.2).symm

@[simp] theorem hemisphereIso_apply (a : {s : Facet (n + 1) | s 0 = true}) :
    hemisphereIso n a = drop n a.1 := rfl

/-! ## Transported global structure: connectivity and regularity of one hemisphere -/

/-- **The induced hemisphere door graph is connected, in every dimension.**  Transport of the
ambient `crossGraph_connected` along `hemisphereIso`.  Path-following needs the ambient
triangulated sphere connected so a walk from a boundary door can reach an interior complementary
simplex; this supplies that connectivity *within a single hemisphere fundamental domain* — the
symmetry-broken half on which the odd seed lives. -/
theorem hemisphere_induce_connected :
    ((crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = true}).Connected :=
  (hemisphereIso n).connected_iff.mpr (crossGraph_connected n)

/-- **Every hemisphere facet has exactly `n+1` interior doors.**  The degree of a facet in the
induced hemisphere graph equals the degree of its coordinate-`0` drop in `crossGraph n`, namely
`n+1` (`facet_degree`).  The graph-level form of `hemisphere_degree_split`'s `#interior = n+1`,
transported along the neighbour-set equivalence of `hemisphereIso`. -/
theorem hemisphere_induce_degree (a : {s : Facet (n + 1) | s 0 = true}) :
    ((crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = true}).degree a = n + 1 := by
  rw [← card_neighborSet_eq_degree,
      Fintype.card_congr ((hemisphereIso n).mapNeighborSet a),
      card_neighborSet_eq_degree]
  exact facet_degree n _

/-- **The induced hemisphere door graph is `(n+1)`-regular, in every dimension.**  So one
hemisphere of `∂◊^{n+1}` carries a full `(n+1)`-regular connected copy of the lower cross-polytope
`∂◊^{n}` — the interior door graph the dimension recursion identifies. -/
theorem hemisphere_induce_regular :
    ((crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = true}).IsRegularOfDegree (n + 1) :=
  fun a => hemisphere_induce_degree n a

/-! ## Axiom audit -- all results are 0-axiom (no `sorryAx`, no `Lean.ofReduceBool`),
dimension-free (no `decide` / `native_decide`). -/

#print axioms hemisphereIso
#print axioms hemisphere_induce_connected
#print axioms hemisphere_induce_degree
#print axioms hemisphere_induce_regular

end SpernerTuckerCrossPolytopeHemisphereIso
