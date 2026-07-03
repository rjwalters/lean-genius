/-
  Sperner → Tucker program, `sperner-mathlib4-oq-02`.

  # The equatorial matching and doubling recursion of the cross-polytope door graph

  `SpernerTuckerCrossPolytopeBoundary` builds the canonical general-`n` antipodally
  symmetric simplicial sphere `∂◊^{n+1}` — the cross-polytope / hyperoctahedron
  boundary — with facets `Facet n = Fin (n+1) → Bool` (sign vectors) and
  facet-adjacency the `(n+1)`-cube `crossGraph n = Q_{n+1}`.
  `SpernerTuckerCrossPolytopeHemisphere` fixes the sign of coordinate `0` and shows the
  positive hemisphere `{s // s 0 = true}` is, under dropping coordinate `0`, a graph-
  isomorphic copy of the whole lower graph `crossGraph n`, and that each hemisphere facet
  has exactly **one** cube neighbour leaving the hemisphere (the coordinate-`0` flip — the
  single *boundary door*) and `n+1` neighbours staying inside (the *interior doors*).

  That per-facet split is stated one facet at a time.  This file makes it **global and
  structural**: the coordinate-`0` flip `equatorFlip` is a single fixed-point-free
  involution and *graph automorphism* of the whole cube, and it is exactly the boundary
  door of **every** facet at once.  Consequently

    * `equatorFlip` is a **perfect matching** across the equator: it pairs each
      positive-hemisphere facet with exactly one negative-hemisphere facet
      (`equatorFlip_swaps`, `equatorFlip_maps_pos_neg`), and
    * the two hemispheres **partition** all `2^{n+2}` facets into two equal halves
      (`hemispheres_partition`, `card_posHemisphere_eq_negHemisphere`), giving the
      structural **doubling recursion** `card (Facet (n+1)) = 2 · card (Facet n)`
      (`card_facet_succ`) — proved from the geometric matching, not from `2^{n+1}`
      arithmetic.

  This is precisely the `Q_{n+2} = Q_{n+1} □ K₂` prism decomposition of the hypercube: two
  copies of the lower cross-polytope graph joined by the equatorial boundary-door matching.
  It is the global form of the door-count recursion `#interior = n`, `#boundary = 1`
  (per facet, in `crossGraph n`) that the open `TuckerTower.bridge` runs the dimension
  induction on.  It does **not** install the Tucker labelling that turns cube edges into
  *complementary* doors (that is `SpernerTuckerCrossPolytopeLabelling`); the
  labelling-broken almost-complementary structure carrying the odd seed remains the open
  frontier.

  Honest status: geometric infrastructure for `bridge`, not a proof of `bridge`.
  Everything here is dimension-free (no `decide` / `native_decide`) and 0-axiom
  (`propext` / `Classical.choice` / `Quot.sound` only), as the `#print axioms` guards at
  the end confirm.
-/
import Mathlib
import Proofs.SpernerTuckerCrossPolytopeHemisphere

namespace SpernerTuckerCrossPolytopeEquator

open Finset SimpleGraph SpernerTuckerCrossPolytopeBoundary
open SpernerTuckerCrossPolytopeHemisphere

variable (n : ℕ)

/-! ## The equatorial boundary-door map: flip coordinate `0` -/

/-- The **equatorial boundary door**: flip the sign of coordinate `0`.  On the positive
hemisphere this is the unique cube neighbour leaving the hemisphere; globally it is the
single boundary door of *every* facet at once. -/
def equatorFlip (s : Facet n) : Facet n := flipAt n s 0

@[simp] theorem equatorFlip_apply_zero (s : Facet n) : equatorFlip n s 0 = !(s 0) := by
  simp [equatorFlip, flipAt]

theorem equatorFlip_apply_ne (s : Facet n) {i : Fin (n + 1)} (hi : i ≠ 0) :
    equatorFlip n s i = s i := by
  simp [equatorFlip, flipAt, Function.update_of_ne hi]

/-- The equatorial flip is an involution (flipping coordinate `0` twice is the identity). -/
theorem equatorFlip_involutive : Function.Involutive (equatorFlip n) := by
  intro s
  funext i
  by_cases hi : i = 0
  · subst hi; simp [equatorFlip_apply_zero]
  · rw [equatorFlip_apply_ne n _ hi, equatorFlip_apply_ne n _ hi]

/-- The equatorial flip is fixed-point-free: no facet equals its coordinate-`0` flip. -/
theorem equatorFlip_free (s : Facet n) : equatorFlip n s ≠ s := by
  intro h
  have h0 : (!(s 0)) = s 0 := by rw [← equatorFlip_apply_zero n s, h]
  cases s 0 <;> simp_all

/-- The boundary door is a **genuine cube edge**: every facet is adjacent to its
equatorial flip. -/
theorem equatorFlip_adj (s : Facet n) : (crossGraph n).Adj s (equatorFlip n s) := by
  rw [← SimpleGraph.mem_neighborFinset, mem_neighbor_iff]
  exact ⟨0, rfl⟩

/-- **The equatorial flip crosses the equator**: it always changes the sign of
coordinate `0`, so it swaps the two hemispheres `{s 0 = true}` and `{s 0 = false}`. -/
theorem equatorFlip_swaps (s : Facet n) : equatorFlip n s 0 ≠ s 0 := by
  rw [equatorFlip_apply_zero]; cases s 0 <;> simp

/-- **The equatorial flip is a graph automorphism of the cube.**  Flipping coordinate `0`
of *both* facets leaves "differ in exactly one coordinate" unchanged. -/
theorem equatorFlip_aut (s t : Facet n) :
    (crossGraph n).Adj (equatorFlip n s) (equatorFlip n t) ↔ (crossGraph n).Adj s t := by
  have hset : (univ.filter fun i => equatorFlip n s i ≠ equatorFlip n t i)
            = (univ.filter fun i => s i ≠ t i) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    by_cases hi : i = 0
    · subst hi
      rw [equatorFlip_apply_zero, equatorFlip_apply_zero]
      cases s 0 <;> cases t 0 <;> simp
    · rw [equatorFlip_apply_ne n _ hi, equatorFlip_apply_ne n _ hi]
  show CrossAdj n (equatorFlip n s) (equatorFlip n t) ↔ CrossAdj n s t
  unfold CrossAdj
  rw [hset]

/-! ## The boundary door is the unique equator-crossing neighbour -/

/-- **The equatorial flip is the unique boundary door.**  Among the `n+1` cube neighbours
of a facet `s`, exactly one — namely `equatorFlip s` — changes the sign of coordinate `0`.
The others all agree with `s` in coordinate `0` (the interior doors). -/
theorem boundary_door_unique (s : Facet n) :
    ((crossGraph n).neighborFinset s).filter (fun t => t 0 ≠ s 0)
      = {equatorFlip n s} := by
  ext t
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hmem, h0⟩
    rw [mem_neighbor_iff] at hmem
    obtain ⟨i, rfl⟩ := hmem
    by_cases hi : i = 0
    · subst hi; rfl
    · exact absurd (by rw [flipAt, Function.update_of_ne (Ne.symm hi)]) h0
  · rintro rfl
    refine ⟨?_, equatorFlip_swaps n s⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact equatorFlip_adj n s

/-- **Exactly one boundary door per facet** (cardinality form of `boundary_door_unique`). -/
theorem boundary_door_count (s : Facet n) :
    (((crossGraph n).neighborFinset s).filter (fun t => t 0 ≠ s 0)).card = 1 := by
  rw [boundary_door_unique, card_singleton]

/-- **The remaining `n` cube neighbours are interior doors.**  Of the `n+1` neighbours of
`s`, one is the boundary door and the other `n` agree with `s` in coordinate `0`. -/
theorem interior_door_count (s : Facet n) :
    (((crossGraph n).neighborFinset s).filter (fun t => t 0 = s 0)).card = n := by
  have hdeg : ((crossGraph n).neighborFinset s).card = n + 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, facet_degree]
  have hsplit :
      (((crossGraph n).neighborFinset s).filter (fun t => t 0 = s 0)).card
        + (((crossGraph n).neighborFinset s).filter (fun t => ¬ t 0 = s 0)).card
        = ((crossGraph n).neighborFinset s).card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  have hbdry : (((crossGraph n).neighborFinset s).filter (fun t => ¬ t 0 = s 0)).card = 1 :=
    boundary_door_count n s
  omega

/-! ## The equatorial matching between the two hemispheres -/

/-- The positive hemisphere `{s : Facet n // s 0 = true}` as a `Finset`. -/
def posHemisphere : Finset (Facet n) := univ.filter fun s => s 0 = true

/-- The negative hemisphere `{s : Facet n // s 0 = false}` as a `Finset`. -/
def negHemisphere : Finset (Facet n) := univ.filter fun s => s 0 = false

theorem mem_posHemisphere {s : Facet n} : s ∈ posHemisphere n ↔ s 0 = true := by
  simp [posHemisphere]

theorem mem_negHemisphere {s : Facet n} : s ∈ negHemisphere n ↔ s 0 = false := by
  simp [negHemisphere]

/-- **The equatorial flip maps the positive hemisphere into the negative hemisphere.** -/
theorem equatorFlip_maps_pos_neg {s : Facet n} (hs : s ∈ posHemisphere n) :
    equatorFlip n s ∈ negHemisphere n := by
  rw [mem_negHemisphere, equatorFlip_apply_zero, (mem_posHemisphere n).mp hs]; rfl

/-- **The equatorial flip maps the negative hemisphere into the positive hemisphere.** -/
theorem equatorFlip_maps_neg_pos {s : Facet n} (hs : s ∈ negHemisphere n) :
    equatorFlip n s ∈ posHemisphere n := by
  rw [mem_posHemisphere, equatorFlip_apply_zero, (mem_negHemisphere n).mp hs]; rfl

/-- **Perfect matching across the equator.**  The equatorial flip restricts to a bijection
of the positive hemisphere onto the negative hemisphere; in particular the two hemispheres
have equal cardinality. -/
theorem card_posHemisphere_eq_negHemisphere :
    (posHemisphere n).card = (negHemisphere n).card := by
  apply Finset.card_bij (fun s _ => equatorFlip n s)
  · intro s hs; exact equatorFlip_maps_pos_neg n hs
  · intro s _ t _ h
    have hcong := congrArg (equatorFlip n) h
    rwa [equatorFlip_involutive n s, equatorFlip_involutive n t] at hcong
  · intro t ht
    exact ⟨equatorFlip n t, equatorFlip_maps_neg_pos n ht, equatorFlip_involutive n t⟩

/-! ## The hemispheres partition the facets — the doubling recursion -/

/-- The two hemispheres are disjoint (`s 0` cannot be both `true` and `false`). -/
theorem hemispheres_disjoint : Disjoint (posHemisphere n) (negHemisphere n) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  rw [mem_posHemisphere] at hs
  rw [mem_negHemisphere] at hs'
  rw [hs] at hs'
  exact Bool.noConfusion hs'

/-- **The two hemispheres partition all facets.**  Every facet lies in exactly one
hemisphere according to the sign of coordinate `0`. -/
theorem hemispheres_partition :
    posHemisphere n ∪ negHemisphere n = (univ : Finset (Facet n)) := by
  ext s
  simp only [mem_union, mem_posHemisphere, mem_negHemisphere, mem_univ, iff_true]
  cases s 0 <;> simp

/-- **Each hemisphere has half the facets.**  The positive hemisphere of `∂◊^{n+2}` has
exactly `Fintype.card (Facet n)` facets — matching the lower-dimensional cross-polytope,
via the coordinate-`0` drop bijection. -/
theorem card_posHemisphere_eq_facet :
    (posHemisphere (n + 1)).card = Fintype.card (Facet n) := by
  have hpe : posHemisphere (n + 1) = hemisphere n := rfl
  rw [hpe, card_hemisphere]

/-- **The doubling recursion, proved from the equatorial matching.**
`card (Facet (n+1)) = 2 · card (Facet n)`: the `(n+1)`-cross-polytope has twice the facets
of the `n`-cross-polytope, because its facets partition into two hemispheres, each a copy
of the lower cross-polytope, matched perfectly by the equatorial boundary door.  (Concretely
`2^{n+2} = 2 · 2^{n+1}`, but established structurally rather than by arithmetic on powers.) -/
theorem card_facet_succ :
    Fintype.card (Facet (n + 1)) = 2 * Fintype.card (Facet n) := by
  have hcard : Fintype.card (Facet (n + 1))
      = (posHemisphere (n + 1)).card + (negHemisphere (n + 1)).card := by
    rw [← Finset.card_union_of_disjoint (hemispheres_disjoint (n + 1)),
        hemispheres_partition, Finset.card_univ]
  rw [hcard, ← card_posHemisphere_eq_negHemisphere (n + 1), card_posHemisphere_eq_facet n]
  ring

/-! ## Axiom audit — all results are 0-axiom (no `sorryAx`, no `Lean.ofReduceBool`),
dimension-free (no `decide` / `native_decide`). -/

#check @equatorFlip_aut
#check @boundary_door_unique
#check @card_posHemisphere_eq_negHemisphere
#check @card_facet_succ

#print axioms equatorFlip_involutive
#print axioms equatorFlip_aut
#print axioms boundary_door_unique
#print axioms interior_door_count
#print axioms card_posHemisphere_eq_negHemisphere
#print axioms card_facet_succ

end SpernerTuckerCrossPolytopeEquator
