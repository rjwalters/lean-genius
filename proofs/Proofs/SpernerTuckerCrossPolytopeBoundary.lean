/-
# The cross-polytope boundary `∂◊^{n+1}`: the antipodally-symmetric simplicial `n`-sphere,
# in every dimension

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits — the missing *general-`n`* antipodal base

The door-counting program has, over many iterations, built an abstract engine whose
central structural fact is the **antipodal no-go** of
`SpernerTuckerAntipodalSymmetry.symmetric_graph_not_tucker_level`: when the antipodal
map is a *free involution* that is also a *graph automorphism* and preserves the boundary
predicate, the interior-endpoint count is forced **even**, so such a graph can never
supply Tucker's *odd* interior seed.  The resolution is that the odd count only appears
once the symmetry is **broken** on a hemisphere fundamental domain
(`SpernerTuckerHemisphere`).

Every prior *concrete* instantiation of that engine used one of two models:

* the **`n = 2` hexagon + centre** triangulation of `B²` (`SpernerTuckerHexagon*`), which
  is antipodally symmetric but pinned to dimension two; or
* the boundary of the **simplex** `∂Δ^{n+1}` (`SpernerTuckerSimplexBoundaryDoorGraph`),
  which *is* dimension-free but is **not** antipodally symmetric (a simplex has no free
  central involution), so it cannot exhibit the antipodal no-go at all.

There was **no general-`n` antipodally-symmetric triangulation** on which the program's
own no-go could be run — even though the whole abstract machinery
(`even_card_of_free_involution`, `degree_eq_of_aut`, `symmetric_graph_not_tucker_level`,
the hemisphere double cover) was built precisely to consume one.

This file supplies it: the **boundary of the cross-polytope** (hyperoctahedron)
`◊^{n+1} = conv{±e₀,…,±eₙ}`, the standard combinatorial model underlying the *octahedral*
Tucker / Borsuk–Ulam lemma.

## The model

The top cells (facets) of `∂◊^{n+1}` are the `2^{n+1}` orthants: one simplex
`conv{(-1)^{s i}·eᵢ : i}` per sign vector `s : Fin (n+1) → Bool`.  So

> `Facet n := Fin (n+1) → Bool`,   `Fintype.card (Facet n) = 2^{n+1}`.

The antipodal map is the central symmetry `x ↦ -x`, which on sign vectors is
**flip every sign**:

> `antipode s := fun i => !(s i)`.

Two facets share a *ridge* (codimension-1 face) iff their sign vectors differ in
**exactly one** coordinate, so the facet-adjacency graph is the **`(n+1)`-cube** `Q_{n+1}`
— an `(n+1)`-regular, vertex-transitive graph — and the antipodal map is the
antipode-of-the-cube "flip all bits", a fixed-point-free automorphism.

## What this file proves (all `0` axioms — `propext` / `Classical.choice` / `Quot.sound`
only; **no** `decide` / `native_decide` / `ofReduceBool`, and **no** per-dimension case
split)

* `antipode_involutive`, `antipode_free` — the antipodal map is a fixed-point-free
  involution on the facets, in every dimension.
* `even_card_facets` — hence `2^{n+1}` facets is even (via the program's own
  `even_card_of_free_involution`), the dimension-free analogue of the boundary-ring
  parity used throughout.
* `crossGraph` + `facet_degree` — the facet-adjacency graph is `Q_{n+1}`, exactly
  `(n+1)`-regular: a genuinely non-trivial (growing-degree) graph, not a vacuous one.
* `antipode_aut` — the antipodal flip is a graph automorphism.
* `crossPolytope_interiorEndpoints_even` / `crossPolytope_not_tucker_level` — running the
  program's no-go on this concrete general-`n` object: the fully antipodally-symmetric
  cross-polytope door graph has an **even** interior-endpoint count and so is **never** a
  Tucker level, **in every dimension**.  This lifts the `n = 2` hexagon obstruction
  (`SpernerTuckerHexagonDoorObstruction`, `SpernerTuckerHexagonFullDoorGraph`) to all `n`
  on the canonical octahedral model, and re-confirms — now dimension-free — that the odd
  seed is *only* available after the hemisphere symmetry break.

This is infrastructure, not new Tucker geometry: it does not construct the labelling-broken
almost-complementary door graph (the open `bridge`).  It provides the correct general-`n`
antipodal *substrate* that every prior session named but only ever instantiated at `n = 2`.
-/
import Mathlib
import Proofs.SpernerTuckerAntipodalSymmetry

namespace SpernerTuckerCrossPolytopeBoundary

open Finset SimpleGraph SpernerTuckerInductiveTower SpernerTuckerAntipodalSymmetry

variable (n : ℕ)

/-! ## Facets and the antipodal map -/

/-- Top cells (facets) of `∂◊^{n+1}`: one per sign vector.  Facet `s` is the orthant
simplex `conv{(-1)^{s i}·eᵢ : i}`. -/
abbrev Facet (n : ℕ) : Type := Fin (n + 1) → Bool

/-- The antipodal central symmetry `x ↦ -x`, expressed on sign vectors as "flip every
sign". -/
def antipode (s : Facet n) : Facet n := fun i => !(s i)

@[simp] theorem antipode_apply (s : Facet n) (i : Fin (n + 1)) :
    antipode n s i = !(s i) := rfl

/-- The antipodal map is an involution. -/
theorem antipode_involutive : Function.Involutive (antipode n) := by
  intro s; funext i; simp

/-- The antipodal map is fixed-point-free: no orthant is its own antipode.  (Uses
coordinate `0`, which exists because `Fin (n+1)` is nonempty.) -/
theorem antipode_free (s : Facet n) : antipode n s ≠ s := by
  intro h
  have h0 : (!(s 0)) = s 0 := congrFun h 0
  cases s 0 <;> simp_all

/-- **The number of facets is even, in every dimension** — via the program's own
free-involution parity lemma applied to the antipodal map.  (Concretely
`Fintype.card (Facet n) = 2^{n+1}`.) -/
theorem even_card_facets : Even (Fintype.card (Facet n)) :=
  even_card_of_free_involution (antipode_involutive n) (antipode_free n)

/-! ## The facet-adjacency graph is the `(n+1)`-cube -/

/-- Two facets are adjacent iff their sign vectors differ in **exactly one** coordinate —
the `(n+1)`-cube adjacency. -/
def CrossAdj (s t : Facet n) : Prop :=
  (univ.filter fun i => s i ≠ t i).card = 1

instance : DecidableRel (CrossAdj n) := fun s t =>
  inferInstanceAs (Decidable ((univ.filter fun i => s i ≠ t i).card = 1))

theorem crossAdj_symm : Symmetric (CrossAdj n) := by
  intro s t h
  have hset : (univ.filter fun i => t i ≠ s i) = (univ.filter fun i => s i ≠ t i) := by
    ext i; simp [ne_comm]
  unfold CrossAdj at h ⊢
  rwa [hset]

theorem crossAdj_irrefl : Irreflexive (CrossAdj n) := by
  intro s h
  have hset : (univ.filter fun i => s i ≠ s i) = (∅ : Finset (Fin (n + 1))) := by
    ext i; simp
  unfold CrossAdj at h
  rw [hset] at h
  simp at h

/-- The facet-adjacency graph of `∂◊^{n+1}`: the `(n+1)`-cube `Q_{n+1}`. -/
def crossGraph : SimpleGraph (Facet n) where
  Adj := CrossAdj n
  symm := crossAdj_symm n
  loopless := crossAdj_irrefl n

instance : DecidableRel (crossGraph n).Adj :=
  inferInstanceAs (DecidableRel (CrossAdj n))

/-- Flipping the sign of `s` at coordinate `i` — the unique neighbour of `s` across
coordinate `i`. -/
def flipAt (s : Facet n) (i : Fin (n + 1)) : Facet n :=
  Function.update s i (!(s i))

theorem flipAt_injective (s : Facet n) : Function.Injective (flipAt n s) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simp only [flipAt, Function.update_self, Function.update_of_ne hij] at hi
  cases s i <;> simp_all

/-- A facet `t` neighbours `s` in the cube iff `t = flipAt s i` for a (unique) coordinate
`i`. -/
theorem mem_neighbor_iff (s t : Facet n) :
    t ∈ (crossGraph n).neighborFinset s ↔ ∃ i, flipAt n s i = t := by
  rw [SimpleGraph.mem_neighborFinset]
  constructor
  · intro hadj
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hadj
    refine ⟨i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      have hjmem : j ∈ univ.filter fun k => s k ≠ t k := by rw [hi]; simp
      rw [mem_filter] at hjmem
      have hne : s j ≠ t j := hjmem.2
      have : t j = !(s j) := by cases hsj : s j <;> cases htj : t j <;> simp_all
      rw [flipAt, Function.update_self, this]
    · have hjnot : j ∉ univ.filter fun k => s k ≠ t k := by rw [hi]; simp [hj]
      rw [mem_filter] at hjnot
      have heq : s j = t j := by
        by_contra hc; exact hjnot ⟨mem_univ j, hc⟩
      rw [flipAt, Function.update_of_ne hj, heq]
  · rintro ⟨i, rfl⟩
    show (univ.filter fun k => s k ≠ flipAt n s i k).card = 1
    rw [Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    by_cases hk : k = i
    · subst hk
      constructor
      · intro _; rfl
      · intro _
        rw [flipAt, Function.update_self]
        cases s k <;> simp
    · have : flipAt n s i k = s k := by rw [flipAt, Function.update_of_ne hk]
      rw [this]
      simp [hk]

theorem neighborFinset_eq_image (s : Facet n) :
    (crossGraph n).neighborFinset s = univ.image (flipAt n s) := by
  ext t
  rw [mem_neighbor_iff, mem_image]
  simp only [mem_univ, true_and]

/-- **The cube is `(n+1)`-regular.**  Every facet has exactly `n+1` neighbours — one per
coordinate to flip.  A genuinely non-trivial (growing-degree) graph, the analogue of
`SpernerTuckerSimplexBoundaryDoorGraph.simplex_degree`. -/
theorem facet_degree (s : Facet n) : (crossGraph n).degree s = n + 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq_image,
      Finset.card_image_of_injective _ (flipAt_injective n s)]
  simp

/-- **The antipodal flip is a graph automorphism of the cube.**  Flipping all signs
preserves "differ in exactly one coordinate". -/
theorem antipode_aut (s t : Facet n) :
    (crossGraph n).Adj (antipode n s) (antipode n t) ↔ (crossGraph n).Adj s t := by
  have hset : (univ.filter fun i => antipode n s i ≠ antipode n t i)
            = (univ.filter fun i => s i ≠ t i) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, antipode_apply]
    cases s i <;> cases t i <;> simp
  show CrossAdj n (antipode n s) (antipode n t) ↔ CrossAdj n s t
  unfold CrossAdj
  rw [hset]

/-! ## Running the program's antipodal no-go, dimension-free -/

/-- **The interior-endpoint count of the symmetric cross-polytope door graph is even, in
every dimension.**  For any boundary predicate `B` invariant under the antipodal flip, the
degree-1 interior vertices split into antipodal 2-orbits.  Direct instantiation of
`SpernerTuckerAntipodalSymmetry.even_card_interiorEndpoints`. -/
theorem crossPolytope_interiorEndpoints_even
    (B : Facet n → Prop) [DecidablePred B] (hB : ∀ s, B (antipode n s) ↔ B s) :
    Even #(interiorEndpoints (crossGraph n) B) :=
  even_card_interiorEndpoints (crossGraph n) B
    (antipode_involutive n) (antipode_free n) (antipode_aut n) hB

/-- **No-go, all dimensions: the antipodally-symmetric cross-polytope door graph is never a
Tucker level.**  A Tucker level needs an **odd** interior-endpoint count; the free
antipodal automorphism forces it **even**.  Hence the fully symmetric octahedral door graph
cannot, in any dimension, supply the odd seed — the symmetry must be broken on a hemisphere
(`SpernerTuckerHemisphere`).  This generalises the `n = 2` hexagon obstruction to every
dimension on the canonical octahedral model. -/
theorem crossPolytope_not_tucker_level
    (B : Facet n → Prop) [DecidablePred B] (hB : ∀ s, B (antipode n s) ↔ B s)
    (hodd : Odd #(interiorEndpoints (crossGraph n) B)) : False :=
  symmetric_graph_not_tucker_level (crossGraph n) B
    (antipode_involutive n) (antipode_free n) (antipode_aut n) hB hodd

#check @even_card_facets
#check @facet_degree
#check @antipode_aut
#check @crossPolytope_not_tucker_level

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide`.
#print axioms even_card_facets
#print axioms facet_degree
#print axioms antipode_aut
#print axioms crossPolytope_not_tucker_level

end SpernerTuckerCrossPolytopeBoundary
