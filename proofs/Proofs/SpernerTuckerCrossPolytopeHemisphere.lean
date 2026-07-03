/-
  Sperner → Tucker program, `sperner-mathlib4-oq-02`.

  # The hemisphere ↔ lower-dimension recursion of the cross-polytope door graph

  `SpernerTuckerCrossPolytopeBoundary` builds the canonical general-`n` antipodally
  symmetric simplicial sphere `∂◊^{n+1}` — the cross-polytope / hyperoctahedron
  boundary underlying the *octahedral* Tucker–Borsuk–Ulam lemma — with facets
  `Facet n = Fin (n+1) → Bool` (sign vectors), antipode = flip-all-signs, and
  facet-adjacency graph the `(n+1)`-cube `Q_{n+1}` (`crossGraph n`).  That file proves
  the fully-symmetric graph can never supply Tucker's *odd* seed
  (`crossPolytope_not_tucker_level`): the odd seed is only available after the
  **hemisphere symmetry break**.

  This file supplies the missing geometric substrate of that symmetry break — the
  **dimension recursion** the open `TuckerTower.bridge` runs on.  Fix the sign of
  coordinate `0`: the *positive hemisphere* `{s : Facet (n+1) // s 0 = true}` is, under
  dropping coordinate `0`, in bijection with `Facet n`, and this bijection is a graph
  isomorphism of the *induced* hemisphere adjacency onto the whole lower cross-polytope
  graph `crossGraph n` (`hemisphere_adj_iff`).  Consequently every hemisphere facet `s`
  has, in the ambient cube `crossGraph (n+1)`,

    * exactly **one** neighbour leaving the hemisphere — the coordinate-`0` flip
      `flipAt (n+1) s 0`, whose coordinate `0` is `false` (`flipAt_zero_not_hemisphere`)
      — the single **boundary door**, and
    * exactly **`n+1`** neighbours staying inside, matching the neighbours of `drop s`
      in `crossGraph n` (`flipAt_succ_hemisphere`, `hemisphere_degree_split`) — the
      **interior doors**.

  This is precisely the door-count recursion `#interior doors (level n+1, one hemisphere)
  = degree in crossGraph n`, `#boundary doors = 1`, that `bridge` must exploit: it
  identifies the `n`-dimensional interior door graph inside one hemisphere of the
  `(n+1)`-dimensional antipodal sphere.  It does **not** yet install the Tucker labelling
  that turns those cube edges into *complementary* doors — that (the labelling-broken
  almost-complementary structure carrying the odd seed) remains the open frontier.

  Honest status: geometric infrastructure for `bridge`, not a proof of `bridge`.
  Everything here is dimension-free (no `decide` / `native_decide`) and 0-axiom
  (`propext` / `Classical.choice` / `Quot.sound` only), as the `#print axioms` guards
  at the end confirm.
-/
import Mathlib
import Proofs.SpernerTuckerCrossPolytopeBoundary

namespace SpernerTuckerCrossPolytopeHemisphere

open Finset SimpleGraph SpernerTuckerCrossPolytopeBoundary

variable (n : ℕ)

/-! ## The coordinate-`0` drop / lift bijection -/

/-- Drop coordinate `0` of an `(n+1)`-facet, yielding an `n`-facet. -/
def drop (s : Facet (n + 1)) : Facet n := fun i => s i.succ

/-- Prepend a positive (`true`) sign in coordinate `0`, embedding an `n`-facet into the
positive hemisphere of the `(n+1)`-facets. -/
def lift (t : Facet n) : Facet (n + 1) := Fin.cons true t

@[simp] theorem drop_apply (s : Facet (n + 1)) (i : Fin (n + 1)) :
    drop n s i = s i.succ := rfl

@[simp] theorem lift_zero (t : Facet n) : lift n t 0 = true := by simp [lift]

@[simp] theorem lift_succ (t : Facet n) (i : Fin (n + 1)) :
    lift n t i.succ = t i := by simp [lift]

theorem drop_lift (t : Facet n) : drop n (lift n t) = t := by
  funext i; simp [drop, lift]

theorem lift_drop {s : Facet (n + 1)} (hs : s 0 = true) : lift n (drop n s) = s := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp only [lift, Fin.cons_zero]; exact hs.symm
  · intro j; simp [lift, drop]

/-- The positive hemisphere `{s // s 0 = true}` of `∂◊^{n+1}` is, by dropping the pinned
coordinate `0`, in bijection with the facets of `∂◊^{n}`. -/
def hemisphereEquiv : {s : Facet (n + 1) // s 0 = true} ≃ Facet n where
  toFun s := drop n s.1
  invFun t := ⟨lift n t, by simp⟩
  left_inv s := Subtype.ext (lift_drop n s.2)
  right_inv t := drop_lift n t

/-! ## The induced hemisphere adjacency is the lower cross-polytope graph -/

/-- **Coordinate-`0` reduction of the Hamming distance.**  If two `(n+1)`-facets agree in
coordinate `0`, their number of differing coordinates equals that of their coordinate-`0`
drops.  (Coordinate `0` contributes nothing; the remaining coordinates are `Fin.succ` of
the `n`-facet coordinates.) -/
theorem card_filter_ne_succ {s t : Facet (n + 1)} (h0 : s 0 = t 0) :
    (univ.filter fun i => s i ≠ t i).card
      = (univ.filter fun i : Fin (n + 1) => s i.succ ≠ t i.succ).card := by
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_succ]
  simp [h0]

/-- **The Hamming/cube adjacency descends to the drop.**  For facets agreeing in
coordinate `0`, cube-adjacency in dimension `n+1` is equivalent to cube-adjacency of the
drops in dimension `n`. -/
theorem crossAdj_drop {s t : Facet (n + 1)} (h0 : s 0 = t 0) :
    CrossAdj (n + 1) s t ↔ CrossAdj n (drop n s) (drop n t) := by
  unfold CrossAdj
  rw [card_filter_ne_succ n h0]
  exact Iff.rfl

/-- **Graph isomorphism onto the lower cross-polytope graph.**  The *induced* adjacency of
the positive hemisphere of `crossGraph (n+1)` is exactly the whole graph `crossGraph n`,
transported along the coordinate-`0` drop. -/
theorem hemisphere_adj_iff {s t : Facet (n + 1)} (hs : s 0 = true) (ht : t 0 = true) :
    (crossGraph (n + 1)).Adj s t ↔ (crossGraph n).Adj (drop n s) (drop n t) := by
  show CrossAdj (n + 1) s t ↔ CrossAdj n (drop n s) (drop n t)
  exact crossAdj_drop n (hs.trans ht.symm)

/-! ## The hemisphere door split: one boundary door, `n+1` interior doors -/

/-- The coordinate-`0` flip carries a positive-hemisphere facet **out** of the hemisphere:
its coordinate `0` becomes `false`.  This is the unique cube neighbour leaving the
hemisphere — the single **boundary door**. -/
theorem flipAt_zero_not_hemisphere {s : Facet (n + 1)} (hs : s 0 = true) :
    flipAt (n + 1) s 0 0 = false := by
  simp [flipAt, hs]

/-- Every other cube neighbour (flipping a coordinate `i.succ ≠ 0`) **stays** in the
positive hemisphere: coordinate `0` is untouched, still `true`.  These are the `n+1`
**interior doors**, matching the neighbours of `drop s` in `crossGraph n`. -/
theorem flipAt_succ_hemisphere {s : Facet (n + 1)} (hs : s 0 = true) (i : Fin (n + 1)) :
    flipAt (n + 1) s i.succ 0 = true := by
  rw [flipAt, Function.update_of_ne (Fin.succ_ne_zero i).symm]; exact hs

/-- The positive hemisphere as a `Finset` of facets. -/
def hemisphere : Finset (Facet (n + 1)) := univ.filter fun s => s 0 = true

/-- **The hemisphere is a full lower-dimensional copy.**  It has exactly
`Fintype.card (Facet n) = 2^{n+1}` facets — half of the `2^{n+2}` facets of
`∂◊^{n+1}` — via the drop bijection. -/
theorem card_hemisphere : (hemisphere n).card = Fintype.card (Facet n) := by
  rw [hemisphere, ← Fintype.card_subtype]
  exact Fintype.card_congr (hemisphereEquiv n)

/-- **Hemisphere door split (summary).**  For a facet `s` in the positive hemisphere:
its coordinate-`0` flip leaves the hemisphere (the one **boundary door**), while its
interior doors number `n+1` — the degree of `drop s` in the lower cross-polytope graph
`crossGraph n`.  Together with `crossGraph (n+1)`'s degree `n+2` this is the door-count
recursion `#interior = n+1`, `#boundary = 1` that the open `bridge` runs the dimension
induction on. -/
theorem hemisphere_degree_split {s : Facet (n + 1)} (hs : s 0 = true) :
    flipAt (n + 1) s 0 0 = false ∧ (crossGraph n).degree (drop n s) = n + 1 :=
  ⟨flipAt_zero_not_hemisphere n hs, facet_degree n (drop n s)⟩

/-- The ambient cube degree of any facet is `n+2`, splitting as the `n+1` interior doors
plus the single boundary door of the hemisphere picture. -/
theorem ambient_degree (s : Facet (n + 1)) :
    (crossGraph (n + 1)).degree s = (n + 1) + 1 :=
  facet_degree (n + 1) s

/-! ## Axiom audit -- all results are 0-axiom (no `sorryAx`, no `Lean.ofReduceBool`),
dimension-free (no `decide` / `native_decide`). -/

#print axioms hemisphere_adj_iff
#print axioms hemisphere_degree_split
#print axioms card_hemisphere
#print axioms flipAt_zero_not_hemisphere

end SpernerTuckerCrossPolytopeHemisphere
