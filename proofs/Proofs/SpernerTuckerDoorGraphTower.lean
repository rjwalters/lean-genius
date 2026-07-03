/-
# A concrete `SimpleGraph` realization of the Tucker door-counting tower

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

`SpernerTuckerInductiveTower.lean` abstracts the dimension recursion of the
door-counting proof to its parity content and exposes a **concrete-graph API**:

* `TuckerTower.ofGraphs` — assemble a tower from a family of max-degree-`≤ 2`
  door graphs `G n` with boundary predicates `B n`, discharging the single-level
  `step` field automatically;
* `exists_interior_of_graph_tower` — run the recursion to extract, in every
  dimension, a degree-1 *interior* (complementary) vertex.

That API is the interface the eventual cross-polytope door graphs must plug into.
But every tower exhibited so far — `trivialTower`, `growingTower` — lives at the
bare-`ℕ` count level (`boundary, interior : ℕ → ℕ`); **none is realized by an
actual `SimpleGraph` family**, so the graph-level hypotheses of
`exists_interior_of_graph_tower` (`Fintype`, `DecidableRel (G n).Adj`, the degree
bound, and the endpoint-count `bridge`, *simultaneously*) had never been
discharged by a genuine graph.

## What this file proves

**(1) Endpoint sets of a 1-regular door graph (reusable).**  In a *perfect
matching* — a graph where every vertex has degree exactly `1` — every vertex is a
degree-1 endpoint, so the abstract `boundaryEndpoints` / `interiorEndpoints`
collapse to the boundary / non-boundary vertices:

  `boundaryEndpoints_of_oneRegular` : `boundaryEndpoints G B = univ.filter B`,
  `interiorEndpoints_of_oneRegular` : `interiorEndpoints G B = univ.filter (¬ B ·)`.

These are dimension-free and directly relevant to the cross-polytope: the
equatorial boundary doors (`SpernerTuckerCrossPolytopeEquator.equatorFlip`) form a
free-involution perfect matching, so an eventual bridge count runs through exactly
this collapse.

**(2) A growing perfect-matching family + the tower realized on it.**  For each
level `n` we take `matchingGraph (2n+1)` on `Fin (2n+1) × Bool` — `2n+1` disjoint
edges — with the boundary predicate "second coordinate is `true`".  Each level is
1-regular (`matching_degree`), its boundary and interior endpoint counts are both
`2n+1` (`card_boundaryEndpoints_matching` / `card_interiorEndpoints_matching`), and
feeding the family through `exists_interior_of_graph_tower` yields, in **every
dimension**, an interior degree-1 vertex on a genuine `SimpleGraph` whose vertex
count grows without bound — the first concrete-graph witness that the abstract API
fires end-to-end (`matchingTower_exists_interior`).

## Honest status

This is **infrastructure and validation, not new Tucker geometry**.  Part (1) is a
small reusable lemma pair characterizing endpoint sets of perfect-matching door
graphs.  Part (2) exercises the previously-uninstantiated concrete-graph API on a
real growing graph family, catching the `Fintype`/`DecidableRel`/degree/`bridge`
hypotheses at once and providing the exact template the cross-polytope door graphs
will follow.  It does **not** build the asymmetric almost-complementary labelling
carrying the odd interior seed — the geometric `bridge` remains the open frontier,
exactly as every prior session flagged.

Self-contained.  0 sorries, 0 axioms (propext / Classical.choice / Quot.sound only).
-/
import Mathlib.Tactic
import Proofs.SpernerTuckerInductiveTower

namespace SpernerTuckerDoorGraphTower

open Finset SimpleGraph SpernerTuckerInductiveTower

/-! ## (1) Endpoint sets of a 1-regular (perfect-matching) door graph -/

section OneRegular

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (B : V → Prop) [DecidablePred B]

/-- In a **1-regular** door graph (a perfect matching: every vertex has degree
exactly `1`), the degree condition is vacuous, so the boundary endpoints are exactly
the boundary vertices. -/
theorem boundaryEndpoints_of_oneRegular (h1 : ∀ v, G.degree v = 1) :
    boundaryEndpoints G B = univ.filter B := by
  unfold boundaryEndpoints
  apply Finset.filter_congr
  intro v _
  simp [h1 v]

/-- In a **1-regular** door graph the interior endpoints are exactly the
non-boundary vertices. -/
theorem interiorEndpoints_of_oneRegular (h1 : ∀ v, G.degree v = 1) :
    interiorEndpoints G B = univ.filter (fun v => ¬ B v) := by
  unfold interiorEndpoints
  apply Finset.filter_congr
  intro v _
  simp [h1 v]

end OneRegular

/-! ## (2) A growing perfect-matching family -/

/-- The perfect matching on `Fin m × Bool`: `(i, a)` is joined to `(j, b)` iff they
share the first coordinate and differ in the second.  This is `m` disjoint edges;
the unique neighbor of `(i, a)` is `(i, !a)`. -/
def matchingGraph (m : ℕ) : SimpleGraph (Fin m × Bool) where
  Adj p q := p.1 = q.1 ∧ p.2 ≠ q.2
  symm := by
    rintro p q ⟨h1, h2⟩
    exact ⟨h1.symm, fun h => h2 h.symm⟩
  loopless := by
    rintro p ⟨_, h2⟩
    exact h2 rfl

instance (m : ℕ) : DecidableRel (matchingGraph m).Adj :=
  fun p q => inferInstanceAs (Decidable (p.1 = q.1 ∧ p.2 ≠ q.2))

/-- The neighbor set of `(i, a)` in the matching graph is the singleton `{(i, !a)}`. -/
theorem matching_neighborFinset (m : ℕ) (p : Fin m × Bool) :
    (matchingGraph m).neighborFinset p = {(p.1, !p.2)} := by
  ext q
  simp only [mem_neighborFinset, mem_singleton]
  obtain ⟨q1, q2⟩ := p
  obtain ⟨r1, r2⟩ := q
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Prod.mk.injEq]
    refine ⟨h1.symm, ?_⟩
    revert h2
    cases q2 <;> cases r2 <;> simp
  · rintro h
    rw [Prod.mk.injEq] at h
    obtain ⟨hr1, hr2⟩ := h
    refine ⟨hr1.symm, ?_⟩
    rw [hr2]
    cases q2 <;> simp

/-- Every vertex of the matching graph has degree exactly `1`: it is 1-regular. -/
theorem matching_degree (m : ℕ) (p : Fin m × Bool) :
    (matchingGraph m).degree p = 1 := by
  rw [← card_neighborFinset_eq_degree, matching_neighborFinset, card_singleton]

/-- The boundary predicate: a vertex is a boundary vertex iff its second coordinate
is `true`.  Under the matching this picks one endpoint of each edge. -/
def matchingB (m : ℕ) : Fin m × Bool → Prop := fun p => p.2 = true

instance (m : ℕ) : DecidablePred (matchingB m) :=
  fun p => inferInstanceAs (Decidable (p.2 = true))

/-- There are exactly `m` vertices with a fixed second coordinate. -/
theorem card_snd_eq (m : ℕ) (b : Bool) :
    #((univ : Finset (Fin m × Bool)).filter (fun p => p.2 = b)) = m := by
  have h : ((univ : Finset (Fin m × Bool)).filter (fun p => p.2 = b))
      = (univ : Finset (Fin m)).image (fun i => (i, b)) := by
    ext ⟨i, c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro rfl; exact ⟨i, rfl, rfl⟩
    · rintro ⟨j, _, h⟩; exact h.symm
  rw [h, Finset.card_image_of_injective _ (by intro x y hxy; simpa using hxy),
    card_univ, Fintype.card_fin]

/-- The boundary endpoint count of level `m` is `m`. -/
theorem card_boundaryEndpoints_matching (m : ℕ) :
    #(boundaryEndpoints (matchingGraph m) (matchingB m)) = m := by
  rw [boundaryEndpoints_of_oneRegular _ _ (matching_degree m)]
  exact card_snd_eq m true

/-- The interior endpoint count of level `m` is `m`. -/
theorem card_interiorEndpoints_matching (m : ℕ) :
    #(interiorEndpoints (matchingGraph m) (matchingB m)) = m := by
  rw [interiorEndpoints_of_oneRegular _ _ (matching_degree m)]
  have : (univ.filter (fun p : Fin m × Bool => ¬ matchingB m p))
      = (univ.filter (fun p : Fin m × Bool => p.2 = false)) := by
    apply Finset.filter_congr
    intro ⟨i, c⟩ _
    cases c <;> simp [matchingB]
  rw [this]
  exact card_snd_eq m false

/-! ### The tower on the growing matching family

Level `n` is `matchingGraph (2n+1)`: `2n+1` disjoint edges, an odd number.  Both the
boundary and interior endpoint counts are `2n+1` (odd), so the `bridge` parity
equivalence holds by `iff_of_true`, the base case is `Odd 1`, and every level is
1-regular hence max-degree-`≤ 2`.  The vertex count `2·(2n+1)` grows without bound. -/

/-- Level-`n` vertex type: `2n+1` disjoint edges. -/
abbrev towerV (n : ℕ) : Type := Fin (2 * n + 1) × Bool

/-- Level-`n` graph. -/
abbrev towerG (n : ℕ) : SimpleGraph (towerV n) := matchingGraph (2 * n + 1)

/-- Level-`n` boundary predicate. -/
abbrev towerB (n : ℕ) : towerV n → Prop := matchingB (2 * n + 1)

/-- **Tucker's conclusion on a genuine growing graph family.**  Running the abstract
door-counting engine `exists_interior_of_graph_tower` on the perfect-matching family
`towerG` yields, in every dimension `n`, an interior degree-1 vertex — a vertex of
degree `1` whose second coordinate is `false`.  The vertex type `Fin (2n+1) × Bool`
grows without bound, so this is a non-trivial concrete-graph realization of the
recursion, not a constant placeholder. -/
theorem matchingTower_exists_interior (n : ℕ) :
    ∃ v : towerV n, (towerG n).degree v = 1 ∧ ¬ towerB n v :=
  exists_interior_of_graph_tower towerG towerB
    (fun n v => by rw [matching_degree]; omega)
    (fun n => by
      rw [card_boundaryEndpoints_matching, card_interiorEndpoints_matching]
      exact iff_of_true ⟨n + 1, by ring⟩ ⟨n, by ring⟩)
    (by rw [card_interiorEndpoints_matching]; exact ⟨0, by ring⟩)
    n

/-- The recovered interior vertex is genuinely interior (not on the boundary): its
second coordinate is `false`, the complementary endpoint of its edge. -/
example (n : ℕ) : ∃ v : towerV n, v.2 = false := by
  obtain ⟨v, _, hv⟩ := matchingTower_exists_interior n
  exact ⟨v, by simpa [towerB, matchingB] using hv⟩

#check @boundaryEndpoints_of_oneRegular
#check @interiorEndpoints_of_oneRegular
#check @matchingTower_exists_interior

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms matching_degree
#print axioms card_boundaryEndpoints_matching
#print axioms matchingTower_exists_interior

end SpernerTuckerDoorGraphTower
