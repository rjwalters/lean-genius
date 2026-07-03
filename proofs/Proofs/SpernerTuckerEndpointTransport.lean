/-
  Sperner → Tucker program, `sperner-mathlib4-oq-02`
  ("Tucker's Lemma and Borsuk–Ulam from abstract door-counting").

  # Door-graph endpoint counts are graph-isomorphism invariants

  ## Where this sits

  The whole door-counting reduction hangs on the single open input
  `SpernerTuckerInductiveTower.TuckerTower.bridge`:

    `bridge n : Odd #(boundaryEndpoints (G (n+1)) (B (n+1)))
                  ↔ Odd #(interiorEndpoints (G n) (B n))`,

  the geometric identification of the level-`(n+1)` boundary doors with the
  level-`n` interior (complementary) simplices.  Companion files supply the two
  *shapes* this identification takes on the cross-polytope model:

  * `SpernerTuckerCrossPolytopeHemisphereIso.hemisphereIso` — one hemisphere of the
    level-`(n+1)` sphere `∂◊^{n+1}` is a **graph isomorphism** onto the *entire* lower
    cross-polytope `∂◊^{n}` (`(crossGraph (n+1)).induce {s | s 0 = true} ≃g crossGraph n`);
  * `SpernerTuckerInductiveTower.{boundary,interior}Endpoints` — the abstract
    degree-1 endpoint sets whose *parities* the tower recursion propagates.

  What was missing is the lemma that lets the first transport the second: **a graph
  isomorphism carries endpoint counts across unchanged** (a door-graph iso is a
  degree isomorphism, and the endpoint sets are cut out purely by "degree = 1" and a
  boundary predicate).  Without it, `hemisphereIso` sits one step away from the
  count statements the bridge consumes; with it, any labelling on `∂◊^{n}` and its
  transport onto a hemisphere of `∂◊^{n+1}` have *equal* interior-endpoint counts —
  so an odd interior seed at level `n` becomes an odd hemisphere count at level `n+1`
  for free, whatever labelling eventually supplies that seed.

  ## What this file proves

  * `interiorEndpoints_card_congr` / `boundaryEndpoints_card_congr` — for a graph
    isomorphism `f : G ≃g G'` whose boundary predicates correspond
    (`∀ v, B v ↔ B' (f v)`), the interior / boundary endpoint counts are equal.
    Proof: `f` is a bijection preserving degree (`SimpleGraph.Iso.degree_eq`), so it
    is a bijection between the two endpoint finsets (`Finset.card_equiv`).
  * `odd_interiorEndpoints_congr` / `odd_boundaryEndpoints_congr` — the parity
    corollaries, in the exact `Odd #(…) ↔ Odd #(…)` shape the tower `bridge`/`step`
    fields are stated in.
  * `hemisphere_interiorEndpoints_count` — the concrete payoff on the cross-polytope:
    for **any** labelling `B` of the lower sphere `∂◊^{n}`, its interior-endpoint
    count equals that of the transported labelling on the positive hemisphere of
    `∂◊^{n+1}` (via `hemisphereIso`).  This is a genuine *factor* of the geometric
    bridge — the "level-`n` interior count lives inside a level-`(n+1)` hemisphere"
    equality, now for the endpoint *counts*, not merely the adjacency structure.

  ## Honest status

  Reusable parity infrastructure, **not** a proof of `bridge`.  It supplies the
  transport half of the bridge (interior count of `∂◊^n` ↔ interior count inside one
  hemisphere of `∂◊^{n+1}`); the *other* half — identifying that hemisphere's
  interior doors with the level-`(n+1)` boundary doors under an **asymmetric,
  almost-complementary Tucker labelling carrying an odd interior seed** — remains the
  open geometric frontier, exactly as every prior session flagged.  In particular this
  file installs no labelling: it is stated for an arbitrary boundary predicate `B`.

  Self-contained.  Dimension-free (no `decide` / `native_decide`), 0 sorries, 0
  `axiom` declarations (`propext` / `Classical.choice` / `Quot.sound` only), as the
  `#print axioms` guards confirm.
-/
import Proofs.SpernerTuckerInductiveTower
import Proofs.SpernerTuckerCrossPolytopeHemisphereIso

namespace SpernerTuckerEndpointTransport

open Finset SimpleGraph SpernerTuckerInductiveTower

/-! ## Endpoint counts transport along a graph isomorphism -/

section Transport

variable {V W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {G' : SimpleGraph W}
variable [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-- **Interior endpoint counts are graph-isomorphism invariants.**  If `f : G ≃g G'`
is a door-graph isomorphism whose boundary predicates correspond
(`∀ v, B v ↔ B' (f v)`), then the two interior-endpoint finsets have equal cardinality.

`f` is a degree isomorphism (`SimpleGraph.Iso.degree_eq`), so it restricts to a
bijection of the "degree `= 1` and not on the boundary" vertices. -/
theorem interiorEndpoints_card_congr (f : G ≃g G')
    (B : V → Prop) (B' : W → Prop) [DecidablePred B] [DecidablePred B']
    (hB : ∀ v, B v ↔ B' (f v)) :
    #(interiorEndpoints G B) = #(interiorEndpoints G' B') := by
  apply Finset.card_equiv f.toEquiv
  intro v
  simp only [interiorEndpoints, Finset.mem_filter, Finset.mem_univ, true_and,
    RelIso.coe_fn_toEquiv]
  rw [f.degree_eq v, ← hB v]

/-- **Boundary endpoint counts are graph-isomorphism invariants** (the positive-predicate
companion of `interiorEndpoints_card_congr`). -/
theorem boundaryEndpoints_card_congr (f : G ≃g G')
    (B : V → Prop) (B' : W → Prop) [DecidablePred B] [DecidablePred B']
    (hB : ∀ v, B v ↔ B' (f v)) :
    #(boundaryEndpoints G B) = #(boundaryEndpoints G' B') := by
  apply Finset.card_equiv f.toEquiv
  intro v
  simp only [boundaryEndpoints, Finset.mem_filter, Finset.mem_univ, true_and,
    RelIso.coe_fn_toEquiv]
  rw [f.degree_eq v, ← hB v]

/-- Parity corollary: an odd interior-endpoint count transports across a door-graph
isomorphism — the exact `Odd #(…) ↔ Odd #(…)` shape the tower `bridge` consumes. -/
theorem odd_interiorEndpoints_congr (f : G ≃g G')
    (B : V → Prop) (B' : W → Prop) [DecidablePred B] [DecidablePred B']
    (hB : ∀ v, B v ↔ B' (f v)) :
    Odd #(interiorEndpoints G B) ↔ Odd #(interiorEndpoints G' B') := by
  rw [interiorEndpoints_card_congr f B B' hB]

/-- Parity corollary for boundary endpoints. -/
theorem odd_boundaryEndpoints_congr (f : G ≃g G')
    (B : V → Prop) (B' : W → Prop) [DecidablePred B] [DecidablePred B']
    (hB : ∀ v, B v ↔ B' (f v)) :
    Odd #(boundaryEndpoints G B) ↔ Odd #(boundaryEndpoints G' B') := by
  rw [boundaryEndpoints_card_congr f B B' hB]

end Transport

/-! ## Concrete payoff on the cross-polytope: the level-`n` interior count lives
inside a level-`(n+1)` hemisphere -/

open SpernerTuckerCrossPolytopeBoundary SpernerTuckerCrossPolytopeHemisphere
  SpernerTuckerCrossPolytopeHemisphereIso

/-- **The level-`n` interior-endpoint count equals the hemisphere interior count at
level `n+1`.**  For *any* labelling `B` of the lower cross-polytope sphere `∂◊^{n}`,
its interior-endpoint count in `crossGraph n` equals the interior-endpoint count of
the transported labelling `B ∘ hemisphereIso` on the positive hemisphere of
`crossGraph (n+1)` (the induced subgraph on `{s | s 0 = true}`).

This is the transport half of the tower `bridge`: whatever labelling eventually
carries the odd interior seed on `∂◊^{n}`, that odd count reappears verbatim inside
one hemisphere of `∂◊^{n+1}`.  Obtained by transporting `interiorEndpoints_card_congr`
along the hemisphere graph isomorphism `hemisphereIso`; installs no labelling of its
own. -/
theorem hemisphere_interiorEndpoints_count (n : ℕ)
    (B : Facet n → Prop) [DecidablePred B] :
    #(interiorEndpoints (crossGraph n) B)
      = #(interiorEndpoints
            ((crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = true})
            (fun a => B (hemisphereIso n a))) := by
  refine interiorEndpoints_card_congr (hemisphereIso n).symm B
    (fun a => B (hemisphereIso n a)) ?_
  intro v
  simp

#check @interiorEndpoints_card_congr
#check @boundaryEndpoints_card_congr
#check @odd_interiorEndpoints_congr
#check @hemisphere_interiorEndpoints_count

/-! ## Axiom audit — all results are 0-axiom (no `sorryAx`, no `Lean.ofReduceBool`),
dimension-free (no `decide` / `native_decide`). -/

#print axioms interiorEndpoints_card_congr
#print axioms boundaryEndpoints_card_congr
#print axioms odd_interiorEndpoints_congr
#print axioms odd_boundaryEndpoints_congr
#print axioms hemisphere_interiorEndpoints_count

end SpernerTuckerEndpointTransport
