/-
  Sperner → Tucker program, `sperner-mathlib4-oq-02`.

  # The equatorial automorphism and the NEGATIVE hemisphere graph isomorphism

  `SpernerTuckerCrossPolytopeHemisphereIso` (Insight 9) packaged the *positive* hemisphere
  `{s | s 0 = true}` of the cross-polytope door graph as a genuine graph isomorphism onto the
  whole lower graph,

    `hemisphereIso : (crossGraph (n+1)).induce {s | s 0 = true} ≃g crossGraph n`,

  and transported connectivity and `(n+1)`-regularity into that one hemisphere.
  `SpernerTuckerCrossPolytopeEquator` proved, separately, that the coordinate-`0` flip
  `equatorFlip` is a fixed-point-free involution and a graph *automorphism* of the cube (a bare
  adjacency-iff `equatorFlip_aut`), and gave the equatorial matching / doubling recursion at the
  `Finset` level.

  Two structural gaps remained, both filled here:

    * **The negative hemisphere had no first-class `≃g`.**  Insight 9 handled only `s 0 = true`;
      the odd Tucker seed lives in *one* symmetry-broken hemisphere, but the `bridge` needs the
      full sphere understood as *two* labelled copies of `crossGraph n`.  This file builds the
      mirror isomorphism

        `negHemisphereIso : (crossGraph (n+1)).induce {s | s 0 = false} ≃g crossGraph n`

      (from the same coordinate-`0` drop, whose adjacency reduction `crossAdj_drop` never used the
      sign) and transports connectivity (`neg_hemisphere_induce_connected`) and `(n+1)`-regularity
      (`neg_hemisphere_induce_regular`) into the negative half.

    * **`equatorFlip` was only a bare adjacency-iff, not a transportable object.**  Here it is
      packaged as a bona-fide graph automorphism `equatorAut : crossGraph n ≃g crossGraph n`
      (its own inverse, as it is an involution).

  The structural payoff (`negHemisphereIso_equatorFlip`) is the **gluing identity of the prism**:
  a positive-hemisphere facet `s` and its equatorial boundary-door partner `equatorFlip s` drop to
  the *same* facet of `crossGraph n`.  So the equatorial matching between the two hemispheres is
  precisely the identity identification of the two `≃g` copies of the lower cross-polytope — the
  `crossGraph (n+1) = crossGraph n □ K₂` gluing map made explicit at the graph-isomorphism level,
  the substrate on which the (still open) asymmetric Tucker labelling carrying the odd seed lives.

  Honest status: geometric/graph-theoretic infrastructure for `bridge`, not a proof of `bridge`.
  It installs no Tucker labelling; the labelling-broken almost-complementary structure carrying the
  odd interior seed remains the open frontier.  Everything here is dimension-free
  (no `decide` / `native_decide`) and 0-axiom (`propext` / `Classical.choice` / `Quot.sound` only),
  as the `#print axioms` guards at the end confirm.
-/
import Mathlib
import Proofs.SpernerTuckerCrossPolytopeHemisphereIso
import Proofs.SpernerTuckerCrossPolytopeEquator

namespace SpernerTuckerCrossPolytopeEquatorAut

open Finset SimpleGraph SpernerTuckerCrossPolytopeBoundary
  SpernerTuckerCrossPolytopeHemisphere SpernerTuckerCrossPolytopeHemisphereIso
  SpernerTuckerCrossPolytopeEquator SpernerTuckerCrossPolytopeConnected

variable (n : ℕ)

/-! ## The equatorial flip as a graph automorphism -/

/-- **The equatorial flip as a graph automorphism.**  Flipping the sign of coordinate `0` is a
fixed-point-free involution (`equatorFlip_involutive`) and preserves cube-adjacency
(`equatorFlip_aut`), so it is a self-inverse graph isomorphism of the cross-polytope door graph
`crossGraph n` onto itself.  Packaging the bare adjacency-iff as a first-class `≃g` makes the
symmetry transportable. -/
def equatorAut : crossGraph n ≃g crossGraph n where
  toEquiv :=
    { toFun := equatorFlip n
      invFun := equatorFlip n
      left_inv := equatorFlip_involutive n
      right_inv := equatorFlip_involutive n }
  map_rel_iff' {a b} := equatorFlip_aut n a b

@[simp] theorem equatorAut_apply (s : Facet n) : equatorAut n s = equatorFlip n s := rfl

/-! ## The negative hemisphere as an induced subgraph, isomorphic to the lower cross-polytope -/

/-- Embed an `n`-facet into the **negative** hemisphere of the `(n+1)`-facets by prepending a
negative (`false`) sign in coordinate `0` (mirror of `lift`). -/
def negLift (t : Facet n) : Facet (n + 1) := Fin.cons false t

theorem drop_negLift (t : Facet n) : drop n (negLift n t) = t := by
  funext i; simp [drop, negLift]

theorem negLift_drop {s : Facet (n + 1)} (hs : s 0 = false) : negLift n (drop n s) = s := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp only [negLift, Fin.cons_zero]; exact hs.symm
  · intro j; simp [negLift, drop]

/-- The negative hemisphere `{s // s 0 = false}` of `∂◊^{n+1}` is, by dropping the pinned
coordinate `0`, in bijection with the facets of `∂◊^{n}` (mirror of `hemisphereEquiv`). -/
def negHemisphereEquiv : {s : Facet (n + 1) // s 0 = false} ≃ Facet n where
  toFun s := drop n s.1
  invFun t := ⟨negLift n t, by simp [negLift]⟩
  left_inv s := Subtype.ext (negLift_drop n s.2)
  right_inv t := drop_negLift n t

/-- **The induced adjacency on the negative hemisphere descends to the drop.**  The reduction
`crossAdj_drop` only needs the two facets to agree in coordinate `0`, so it applies to the negative
hemisphere verbatim (as it did to the positive one in `hemisphere_adj_iff`). -/
theorem neg_hemisphere_adj_iff {s t : Facet (n + 1)} (hs : s 0 = false) (ht : t 0 = false) :
    (crossGraph (n + 1)).Adj s t ↔ (crossGraph n).Adj (drop n s) (drop n t) := by
  show CrossAdj (n + 1) s t ↔ CrossAdj n (drop n s) (drop n t)
  exact crossAdj_drop n (hs.trans ht.symm)

/-- **The negative hemisphere graph isomorphism.**  The subgraph of `crossGraph (n+1)` induced on
the negative hemisphere `{s | s 0 = false}` is isomorphic, via the coordinate-`0` drop, to the
entire lower cross-polytope graph `crossGraph n` — the mirror of `hemisphereIso`.  So *both*
hemispheres of `∂◊^{n+1}` are first-class `≃g` copies of `∂◊^{n}`, not just the positive one. -/
def negHemisphereIso :
    (crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = false} ≃g crossGraph n where
  toEquiv := negHemisphereEquiv n
  map_rel_iff' {a b} := by
    change (crossGraph n).Adj (drop n a.1) (drop n b.1) ↔ (crossGraph (n + 1)).Adj a.1 b.1
    exact (neg_hemisphere_adj_iff n a.2 b.2).symm

@[simp] theorem negHemisphereIso_apply (a : {s : Facet (n + 1) | s 0 = false}) :
    negHemisphereIso n a = drop n a.1 := rfl

/-! ## Transported global structure of the negative hemisphere -/

/-- **The induced negative hemisphere door graph is connected, in every dimension.**  Transport of
the ambient `crossGraph_connected` along `negHemisphereIso`, the negative-hemisphere counterpart of
`hemisphere_induce_connected`. -/
theorem neg_hemisphere_induce_connected :
    ((crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = false}).Connected :=
  (negHemisphereIso n).connected_iff.mpr (crossGraph_connected n)

/-- **Every negative-hemisphere facet has exactly `n+1` interior doors.**  Transport of
`facet_degree` along the neighbour-set equivalence of `negHemisphereIso`, the counterpart of
`hemisphere_induce_degree`. -/
theorem neg_hemisphere_induce_degree (a : {s : Facet (n + 1) | s 0 = false}) :
    ((crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = false}).degree a = n + 1 := by
  rw [← card_neighborSet_eq_degree,
      Fintype.card_congr ((negHemisphereIso n).mapNeighborSet a),
      card_neighborSet_eq_degree]
  exact facet_degree n _

/-- **The induced negative hemisphere door graph is `(n+1)`-regular, in every dimension.**  So the
negative hemisphere of `∂◊^{n+1}` also carries a full `(n+1)`-regular connected copy of the lower
cross-polytope `∂◊^{n}`. -/
theorem neg_hemisphere_induce_regular :
    ((crossGraph (n + 1)).induce {s : Facet (n + 1) | s 0 = false}).IsRegularOfDegree (n + 1) :=
  fun a => neg_hemisphere_induce_degree n a

/-! ## The prism gluing identity: the equatorial matching identifies both hemisphere copies -/

/-- **Dropping coordinate `0` is invariant under the equatorial flip.**  Because `equatorFlip`
changes only coordinate `0`, a facet and its equatorial partner have the same coordinate-`0` drop. -/
theorem drop_equatorFlip (s : Facet (n + 1)) :
    drop n (equatorFlip (n + 1) s) = drop n s := by
  funext i
  simp only [drop_apply]
  exact equatorFlip_apply_ne (n + 1) s (Fin.succ_ne_zero i)

/-- **The prism gluing identity.**  A positive-hemisphere facet `s` and its equatorial
boundary-door partner `equatorFlip s` (which lies in the negative hemisphere) map, under the two
hemisphere isomorphisms, to the *same* facet of `crossGraph n`:

  `negHemisphereIso ⟨equatorFlip s, _⟩ = hemisphereIso ⟨s, _⟩`.

So the equatorial matching between the two hemispheres is exactly the identity identification of
the two `≃g` copies of the lower cross-polytope — the `crossGraph (n+1) = crossGraph n □ K₂` gluing
map made explicit at the graph-isomorphism level. -/
theorem negHemisphereIso_equatorFlip (s : Facet (n + 1)) (hs : s 0 = true)
    (h : equatorFlip (n + 1) s 0 = false) :
    negHemisphereIso n ⟨equatorFlip (n + 1) s, h⟩ = hemisphereIso n ⟨s, hs⟩ := by
  have e1 : (negHemisphereIso n ⟨equatorFlip (n + 1) s, h⟩ : Facet n)
      = drop n (equatorFlip (n + 1) s) := rfl
  have e2 : (hemisphereIso n ⟨s, hs⟩ : Facet n) = drop n s := rfl
  rw [e1, e2, drop_equatorFlip]

/-! ## Axiom audit -- all results are 0-axiom (no `sorryAx`, no `Lean.ofReduceBool`),
dimension-free (no `decide` / `native_decide`). -/

#print axioms equatorAut
#print axioms negHemisphereIso
#print axioms neg_hemisphere_induce_connected
#print axioms neg_hemisphere_induce_degree
#print axioms neg_hemisphere_induce_regular
#print axioms negHemisphereIso_equatorFlip

end SpernerTuckerCrossPolytopeEquatorAut
