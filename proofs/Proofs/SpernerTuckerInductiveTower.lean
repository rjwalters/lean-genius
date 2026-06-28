/-
# The dimension recursion for Tucker's lemma: an abstract induction tower (n ≥ 1)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

The door-counting program for Tucker's lemma is, at its heart, an **induction on
the dimension** `n`.  The companion files have machine-checked every *single-level*
piece of the parity bookkeeping:

* `SpernerTuckerPathFollowing.lean` — in a max-degree-≤2 "door graph" the number of
  degree-1 path endpoints is even, and an odd number of *boundary* endpoints forces
  an interior one (`exists_interior_degree_one`);
* `SpernerTuckerDoorIncidenceParity.lean` — at the incidence level, an odd number of
  *boundary doors* forces a cell of odd door-count;
* `SpernerTuckerBoundaryParity.lean` — the boundary parity the engine needs cannot
  come from the raw boundary ring (always even); it must come from the lower
  dimension.

What every prior session flagged in prose but **left unformalized** is the step that
ties the levels together: the boundary doors of the dimension-`n` complex are the
*interior complementary simplices of the dimension-`(n−1)` complex* (the boundary of
`Bⁿ` is `Sⁿ⁻¹`, on which the antipodal labelling is an `(n−1)`-Tucker instance).  So
the odd interior count at level `n−1` *is* the odd boundary count at level `n`, and
the induction closes.

## What this file proves

Two things.

**(1) The engine's count form (a strengthening).**  The path-following engine only
extracted *existence* of an interior endpoint.  Here we prove the sharper parity
*equivalence*

  `odd_boundary_iff_odd_interior` :
    in a max-degree-≤2 graph, `Odd #{boundary endpoints} ↔ Odd #{interior endpoints}`,

because the two endpoint classes partition the (even-cardinality) set of all degree-1
vertices, so their parities must agree.  This is exactly the quantitative statement
the induction needs: it lets an odd *interior* count propagate, not merely a witness.

**(2) The dimension recursion itself.**  A `TuckerTower` bundles, for every level
`n`, an interior-endpoint count `interior n` and a boundary-endpoint count
`boundary n`, together with three hypotheses:

* `step n   : Odd (boundary n) ↔ Odd (interior n)`     — the single-level engine,
  discharged for any concrete level by `odd_boundary_iff_odd_interior` above;
* `bridge n : Odd (boundary (n+1)) ↔ Odd (interior n)` — the **geometric boundary
  bijection** (boundary doors of level `n+1` ↔ interior simplices of level `n`); the
  one remaining dimension-specific input;
* `base     : Odd (interior 0)`                         — the base case, supplied by
  the already-verified 1-D Tucker (`SpernerTuckerOneDim.exists_complementary_edge`).

From these, `tower_interior_odd : ∀ n, Odd (interior n)` follows by a one-line
induction, and `tower_exists_interior : ∀ n, 0 < interior n` gives Tucker (a
complementary simplex exists) in every dimension.

## Honest status

This is the **organizing skeleton** of the induction, not new Tucker mathematics.
`step` is a theorem (proved here in its graph form); `base` is already verified
(n = 1).  The single genuinely open input is `bridge` — the geometric identification
of level-`n` boundary doors with level-`(n−1)` interior simplices — which is the
dimension-specific construction every prior session named as the frontier.  This file
makes precise that *once `bridge` is supplied, full-dimensional Tucker is a
two-hypothesis induction*, and provides an inhabited `example` showing the recursion
is non-vacuous and computes.

Self-contained.  0 sorries, 0 axioms.
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace SpernerTuckerInductiveTower

open Finset SimpleGraph

/-! ## (1) The count form of the path-following engine -/

section GraphLevel

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
variable (B : V → Prop) [DecidablePred B]

/-- The **boundary endpoints** of a door graph: degree-1 vertices lying on the
antipodal boundary. -/
def boundaryEndpoints : Finset V := {v | G.degree v = 1 ∧ B v}

/-- The **interior endpoints** of a door graph: degree-1 vertices *not* on the
boundary — these are the complementary simplices Tucker asserts. -/
def interiorEndpoints : Finset V := {v | G.degree v = 1 ∧ ¬ B v}

/-- In a max-degree-≤2 graph, having odd degree is the same as having degree
exactly 1.  (Degrees lie in `{0, 1, 2}`.) -/
theorem odd_degree_iff_eq_one (h : ∀ v, G.degree v ≤ 2) (v : V) :
    Odd (G.degree v) ↔ G.degree v = 1 := by
  rw [Nat.odd_iff]; have := h v; omega

/-- The number of degree-1 vertices of a max-degree-≤2 graph is even (handshaking
lemma specialised to paths-and-cycles). -/
theorem even_card_degree_one (h : ∀ v, G.degree v ≤ 2) :
    Even #{v | G.degree v = 1} := by
  have hset : ({v | G.degree v = 1} : Finset V) = ({v | Odd (G.degree v)} : Finset V) := by
    apply Finset.filter_congr; intro v _; exact (odd_degree_iff_eq_one G h v).symm
  rw [hset]; exact G.even_card_odd_degree_vertices

/-- The boundary and interior endpoints partition the degree-1 vertices: their
cardinalities sum to the number of degree-1 vertices. -/
theorem card_boundary_add_card_interior :
    #(boundaryEndpoints G B) + #(interiorEndpoints G B) = #{v | G.degree v = 1} := by
  unfold boundaryEndpoints interiorEndpoints
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := ({v | G.degree v = 1} : Finset V)) (p := B)
  simpa [Finset.filter_filter] using h

/-- **The engine in count form.**  In a max-degree-≤2 door graph the number of
boundary endpoints and the number of interior endpoints have the **same parity**:
they partition the degree-1 vertices, whose total is even.

This strengthens `SpernerTuckerPathFollowing.exists_interior_degree_one` (which
only extracted a single interior witness) to the quantitative statement the
dimension induction needs — an *odd interior count* propagating upward. -/
theorem odd_boundary_iff_odd_interior (h : ∀ v, G.degree v ≤ 2) :
    Odd #(boundaryEndpoints G B) ↔ Odd #(interiorEndpoints G B) := by
  have heven : Even #{v | G.degree v = 1} := even_card_degree_one G h
  have hsum := card_boundary_add_card_interior G B
  rw [← hsum] at heven
  rw [Nat.odd_iff, Nat.odd_iff]
  rw [Nat.even_add] at heven
  -- `heven : Even a ↔ Even b`; convert to a statement about `% 2`.
  rw [Nat.even_iff, Nat.even_iff] at heven
  omega

/-- An odd interior-endpoint count is in particular nonzero, so a complementary
simplex exists — the existence conclusion of Tucker at this level. -/
theorem exists_interior_of_odd (hodd : Odd #(interiorEndpoints G B)) :
    ∃ v, G.degree v = 1 ∧ ¬ B v := by
  have hpos : 0 < #(interiorEndpoints G B) := hodd.pos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  unfold interiorEndpoints at hv
  rw [Finset.mem_filter] at hv
  exact ⟨v, hv.2⟩

end GraphLevel

/-! ## (2) The dimension recursion -/

/-- A **Tucker tower** is the dimension recursion of the door-counting proof,
abstracted to its parity content.  For each level `n` it records the number of
boundary endpoints `boundary n` and interior endpoints `interior n` of that level's
door graph, with:

* `step`   — the single-level engine (`odd_boundary_iff_odd_interior`);
* `bridge` — the geometric boundary bijection linking level `n+1`'s boundary doors
  to level `n`'s interior simplices;
* `base`   — the verified 1-D Tucker base case.

`bridge` is the sole genuinely-open input; everything else is a theorem. -/
structure TuckerTower where
  /-- Number of boundary endpoints (boundary doors) of the level-`n` door graph. -/
  boundary : ℕ → ℕ
  /-- Number of interior (complementary) endpoints of the level-`n` door graph. -/
  interior : ℕ → ℕ
  /-- Single-level engine: an odd boundary count ⇔ an odd interior count.  Supplied
  for any concrete level by `odd_boundary_iff_odd_interior`. -/
  step : ∀ n, Odd (boundary n) ↔ Odd (interior n)
  /-- Geometric boundary bijection: the boundary doors of level `n+1` are the
  interior complementary simplices of level `n`. -/
  bridge : ∀ n, Odd (boundary (n + 1)) ↔ Odd (interior n)
  /-- Base case: 1-D Tucker (`SpernerTuckerOneDim.exists_complementary_edge`) gives
  an odd interior count at level 0. -/
  base : Odd (interior 0)

namespace TuckerTower

variable (T : TuckerTower)

/-- **The dimension recursion.**  In every dimension the interior (complementary)
count is odd.  Proof: induction on `n`; the base is `T.base`, and the step chains
`Odd (interior (n+1)) ↔ Odd (boundary (n+1)) ↔ Odd (interior n)` via `step` and
`bridge`, closing with the inductive hypothesis. -/
theorem tower_interior_odd : ∀ n, Odd (T.interior n)
  | 0 => T.base
  | n + 1 => by
      rw [← T.step (n + 1), T.bridge n]
      exact tower_interior_odd n

/-- **Tucker in every dimension.**  An odd count is positive, so a complementary
simplex exists at every level. -/
theorem tower_exists_interior (n : ℕ) : 0 < T.interior n :=
  (T.tower_interior_odd n).pos

/-- The boundary count is odd in every dimension `≥ 1` too (the antipodal boundary
condition), a corollary of `tower_interior_odd` through `bridge`. -/
theorem tower_boundary_odd (n : ℕ) : Odd (T.boundary (n + 1)) :=
  (T.bridge n).mpr (T.tower_interior_odd n)

end TuckerTower

/-! ## Non-vacuity: an inhabited tower on which the recursion computes

To witness that the structure is inhabited and the induction is not arguing about an
empty hypothesis, we build the simplest possible tower: every level has exactly one
boundary endpoint and one interior endpoint.  `step` and `bridge` then read
`Odd 1 ↔ Odd 1` and `base` reads `Odd 1`, all decidable.  `tower_interior_odd`
returns `Odd 1` at every level. -/

/-- The constant-1 tower: each level has one boundary and one interior endpoint. -/
def trivialTower : TuckerTower where
  boundary := fun _ => 1
  interior := fun _ => 1
  step := fun _ => Iff.rfl
  bridge := fun _ => Iff.rfl
  base := ⟨0, rfl⟩

example : ∀ n, Odd (trivialTower.interior n) := trivialTower.tower_interior_odd
example : ∀ n, 0 < trivialTower.interior n := trivialTower.tower_exists_interior

#check @odd_boundary_iff_odd_interior
#check @TuckerTower.tower_interior_odd
#check @TuckerTower.tower_exists_interior

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms odd_boundary_iff_odd_interior
#print axioms TuckerTower.tower_interior_odd
#print axioms TuckerTower.tower_exists_interior

end SpernerTuckerInductiveTower
