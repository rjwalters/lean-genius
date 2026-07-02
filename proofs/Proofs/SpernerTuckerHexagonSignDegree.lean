/-
# The oriented boundary seed on the hexagon is the hemisphere sign-degree (ODD)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — closing a gap left open by two negative results

The abstract path-following engine (`SpernerTuckerPathFollowing.exists_interior_degree_one`)
produces an interior complementary simplex from an **odd** count of boundary path
endpoints.  The whole n ≥ 2 program hinges on supplying that odd boundary seed for a
concrete triangulation.

Two prior sessions established, on the standard hexagon + centre triangulation of `B²`
(labels `{±1,±2}` encoded as `Fin 4`, antipodal on the boundary), that the seed is **not**
any unsigned complementary-edge count:

* `SpernerTuckerHexagonFullDoorGraph.boundary_door_count_even` — the number of
  complementary *boundary* edges is always **even**; and
* `SpernerTuckerHexagonFullDoorGraph.half_boundary_parity_not_invariant` — even passing
  to a fundamental domain of the antipodal action does not fix a parity: the half-ring
  complementary-edge count is even on some labellings and odd on others.

Those sessions concluded — but did **not** construct — that the missing input must be an
*oriented / antipodally-signed* count (a discrete Borsuk–Ulam degree on `S¹`), not a
door-counting parity.  This file supplies exactly that count and proves it is odd.

## What this file proves (all by kernel `decide`, 0 axioms)

The correct oriented object is obtained by pushing the labelling through the **sign map**
`sgn : Fin 4 → ZMod 2` collapsing `{+1,+2} ↦ 0` and `{-1,-2} ↦ 1`.  This map is the
`ZMod 2` reduction underlying the antipodal action:

* `sgn_negL` — `sgn (negL x) = sgn x + 1` for every label: the sign map is **antipodal**
  (label negation flips the sign bit), so a hemisphere arc `v₀ → v₁ → v₂ → v₃ = -v₀`
  becomes a `ZMod 2` path with **distinct endpoints** — precisely the boundary condition
  of the already-verified one-dimensional Tucker lemma (`SpernerTuckerOneDim`).

Hence the **hemisphere sign-degree** — the number of edges of that arc across which the
sign bit flips — is odd, exactly by the telescoping ("discrete FTC") argument of n = 1
Tucker, now realised on the boundary of real n = 2 geometry:

* `arc_sign_changes_odd` — the hemisphere-arc sign-change count is **ODD** for **every**
  antipodal labelling (verified over all `4³ = 64` free labellings).  This is the first
  **positive** odd boundary seed for the hexagon; every prior boundary result was negative
  (even, or not parity-invariant).
* `full_sign_changes_even` — the sign-change count around the **whole** boundary ring is
  always **even**: the odd seed lives on the antipodal *fundamental domain* (a hemisphere),
  not on the full circle — the discrete analogue of "the degree is read off half the loop".

## Why the sign-degree, and not the complementary-edge count

The two objects genuinely differ, which is why the earlier unsigned counts failed:

* `sign_change_not_complementary_witness` — there is a boundary edge whose two labels have
  **opposite signs** (a sign-degree edge, e.g. `+2` then `-1`) yet are **not complementary**
  (`λ(v_{i+1}) ≠ -λ(v_i)`).  So a sign flip need not be a complementary edge; the
  complementary-edge count misses exactly these, which is why it is even / non-invariant
  while the sign-degree is odd.

## Honest status

A **positive scoping result**: it constructs the odd oriented boundary seed the previous
two negative results only pointed at, and pins it to the hemisphere sign-degree, connecting
the n = 2 boundary directly to the verified n = 1 Tucker via the sign-reduction map.  It is
**not** a full proof of n = 2 Tucker: the odd sign-degree counts boundary *sign flips*,
whereas the interior target is a *complementary* simplex; bridging the two is the 2-D
almost-complementary path-following (the genuine open lever every prior session flagged).
This result identifies the seed that path-following must consume.

Self-contained.  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Nat.Even

namespace SpernerTuckerHexagonSignDegree

open Finset

/-! ## Labelling model (same encoding as `SpernerTuckerHexagon` / `…FullDoorGraph`) -/

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The six boundary labels from three free labels `a,b,c` on `v0,v1,v2`, with the
antipodal condition `v(i+3) = -v(i)` built in. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- Cyclic successor around the hexagon boundary. -/
def rot (i : Fin 6) : Fin 6 := i + 1

/-- **Sign map** `sgn : Fin 4 → ZMod 2` collapsing magnitude: `{+1,+2} ↦ 0`,
`{-1,-2} ↦ 1`.  This is the `ZMod 2` reduction underlying the antipodal action. -/
def sgn : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

/-- **The sign map is antipodal.**  Label negation flips the sign bit:
`sgn (negL x) = sgn x + 1` for every label.  Hence a hemisphere arc
`v₀ → … → v₃ = -v₀` has sign-distinct endpoints — the n = 1 Tucker boundary condition. -/
theorem sgn_negL : ∀ x : Fin 4, sgn (negL x) = sgn x + 1 := by decide

/-! ## The hemisphere sign-degree is odd -/

/-- **Hemisphere sign-degree.**  The number of edges of the fundamental-domain arc
`v₀ → v₁ → v₂ → v₃` (three consecutive boundary edges, `v₃ = -v₀`) across which the sign
bit flips. -/
def arcSignChanges (a b c : Fin 4) : ℕ :=
  (([0, 1, 2] : List (Fin 6)).filter
    (fun i => decide (sgn (V a b c (rot i)) ≠ sgn (V a b c i)))).length

/-- **The hemisphere sign-degree is ODD** for every antipodal labelling.  This is the
positive odd boundary seed the path-following engine needs — obtained as the n = 1 Tucker
count of the sign-reduced labelling on the antipodal arc, whose endpoints `sgn v₀` and
`sgn v₃ = sgn v₀ + 1` differ (`sgn_negL`).  Verified over all `4³ = 64` free labellings
(the centre label is irrelevant to the boundary). -/
theorem arc_sign_changes_odd : ∀ a b c : Fin 4, Odd (arcSignChanges a b c) := by decide

/-- Sign flips around the **whole** boundary ring `v₀ → v₁ → ⋯ → v₅ → v₀`. -/
def fullSignChanges (a b c : Fin 4) : ℕ :=
  ((List.finRange 6).filter
    (fun i => decide (sgn (V a b c (rot i)) ≠ sgn (V a b c i)))).length

/-- **The full-ring sign-change count is EVEN.**  The odd seed lives on the antipodal
fundamental domain (a hemisphere arc), not on the whole circle: the loop returns to its
starting sign, so its total sign-change count is even.  The discrete analogue of reading
the degree off half the loop. -/
theorem full_sign_changes_even : ∀ a b c : Fin 4, Even (fullSignChanges a b c) := by decide

/-! ## The sign-degree is a genuinely different object from the complementary count -/

/-- **A sign flip need not be a complementary edge.**  There is a boundary edge whose two
labels have opposite signs (`sgn (V (rot i)) ≠ sgn (V i)`) yet are **not** complementary
(`V (rot i) ≠ negL (V i)`) — e.g. `+2` followed by `-1`.  This is exactly the discrepancy
that makes the unsigned complementary-edge count even / non-parity-invariant while the
signed sign-degree is odd. -/
theorem sign_change_not_complementary_witness :
    ∃ a b c : Fin 4, ∃ i : Fin 6,
      sgn (V a b c (rot i)) ≠ sgn (V a b c i) ∧
      V a b c (rot i) ≠ negL (V a b c i) := by decide

#print axioms sgn_negL
#print axioms arc_sign_changes_odd
#print axioms full_sign_changes_even
#print axioms sign_change_not_complementary_witness

end SpernerTuckerHexagonSignDegree
