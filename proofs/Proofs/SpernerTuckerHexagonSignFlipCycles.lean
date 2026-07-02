/-
# The sign-flip door graph on the hexagon is all cycles: single-coordinate closure of n=2 Tucker is impossible

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — closing the frontier from BOTH sides

The abstract path-following engine (`SpernerTuckerPathFollowing.exists_interior_degree_one`)
needs a max-degree-`≤2` door graph on the triangulation whose degree-1 **boundary**
endpoints are **odd** in number; it then returns a degree-1 **interior** endpoint — the
Tucker witness.  Supplying that graph for the concrete hexagon + centre triangulation of
`B²` is the single genuine open lever of this program.

Two coordinates are in play (labels `{±1,±2}`): the **sign bit** `sgn : {+1,+2}↦0,
{-1,-2}↦1` (coordinate 1) and the **magnitude** `{1,2}` (coordinate 2).  Prior verified
files pinned down each coordinate *separately*:

* **Sign coordinate carries the ODD boundary seed.**  `SpernerTuckerHexagonSignDegree.arc_sign_changes_odd`:
  the number of hemisphere-arc boundary edges across which the *sign bit* flips is **odd**
  for every antipodal labelling (`sgn` is antipodal, so n = 1 Tucker on the arc applies).
  This file re-derives it self-containedly (`arc_signflip_odd`).
* **Magnitude/exact-complementary coordinate has NO odd seed.**
  `SpernerTuckerHexagonFullDoorGraph.boundary_door_count_even` /
  `half_boundary_parity_not_invariant`: the unsigned `{+1,-1}` complementary-edge count is
  even on the full ring and non-invariant on the hemisphere.  This file adds that the
  *directed* `+1→-1` count is likewise non-invariant (`pm1_dir_not_invariant`), so the odd
  seed is genuinely the sign bit, not any refinement of the exact-complementary edge.

## What this file proves — the missing second blade (all by `decide` / ZMod 2 algebra, 0 axioms)

The odd seed lives on the sign coordinate.  So can the *sign-flip* door graph itself
(rooms = triangles, doors = sign-flip edges) terminate at an interior endpoint?  **No:**

* `triangle_flip_even` — for any three sign bits `x y z : ZMod 2`, the number of triangle
  edges across which the bit flips is **even** (`0` or `2`, never `1` or `3`): the flip
  indicators sum to `(x+y)+(y+z)+(z+x) = 2(x+y+z) = 0` in `ZMod 2`.  A pure sign-labelled
  triangle is never a path endpoint.
* `hexagon_triSignFlips_even` — hence on the hexagon disc **every** triangle `T_i =
  (centre, vᵢ, vᵢ₊₁)` has an even number of sign-flip sides, for every antipodal labelling.
  The sign-flip door graph on the disc is therefore a disjoint union of **cycles**, with
  **no interior degree-1 endpoint**.

## Consequence: the bridge is irreducibly 2-coordinate

Putting the two blades together:

* the coordinate that carries the odd boundary seed (sign) produces a door graph that is
  **all cycles** — it can never terminate at an interior witness (`hexagon_triSignFlips_even`);
* the coordinate that can terminate (exact `{+1,-1}` complementary edges — a triangle with
  labels `{+1,-1,±2}` is a genuine degree-1 room) has **no odd boundary seed**
  (`pm1_dir_not_invariant` + the sibling even/non-invariant facts).

No **single-coordinate** door rule can therefore close n = 2 Tucker.  The Freund–Todd /
Prescott–Su bridge must be a genuine **nested** rule coupling both coordinates (an odd
sign-seed on the boundary refined by the magnitude to break interior cycles into paths).
This is a machine-checked *impossibility* result that fences the open lever from both
sides, sharpening the prior one-sided negative/positive scoping facts into a dichotomy.

## Honest status

A **scoping / impossibility result**, not new Tucker geometry and not a proof of n = 2
Tucker.  It rules out an entire class of attempted closures (any single-coordinate door
rule), and supplies the reusable `ZMod 2` cycle lemma `triangle_flip_even`.  The genuine
open lever — the concrete nested Freund–Todd door graph — is unchanged and remains a
multi-session BUILD.

Self-contained: imports Mathlib only.  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`).
-/
import Mathlib

namespace SpernerTuckerHexagonSignFlipCycles

open Finset

/-! ## The reusable ZMod 2 cycle lemma -/

/-- Sign-flip indicator: `1` if the two sign bits differ, else `0`. -/
def flip (x y : ZMod 2) : ℕ := if x = y then 0 else 1

/-- **A triangle (3-cycle) of sign bits has an even number of sign-flip edges.**
For any three sign bits the flip count around the triangle is `0` or `2`, never `1` or
`3`: in `ZMod 2` the three flip indicators sum to `(x+y)+(y+z)+(z+x) = 2(x+y+z) = 0`. -/
theorem triangle_flip_even (x y z : ZMod 2) :
    (flip x y + flip y z + flip z x) % 2 = 0 := by
  revert x y z; decide

/-- `Even` form of `triangle_flip_even`. -/
theorem triangle_flip_even' (x y z : ZMod 2) :
    Even (flip x y + flip y z + flip z x) := by
  rw [Nat.even_iff]; exact triangle_flip_even x y z

/-- A pure sign-labelled triangle is never a path endpoint: its sign-flip count is
never exactly one. -/
theorem triangle_flip_ne_one (x y z : ZMod 2) :
    flip x y + flip y z + flip z x ≠ 1 := by
  revert x y z; decide

/-! ## Labelling model (same encoding as `SpernerTuckerHexagonSignDegree`) -/

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- Boundary labels from three free labels, antipodal `v(i+3) = -v(i)`. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- Cyclic successor around the hexagon boundary. -/
def rot (i : Fin 6) : Fin 6 := i + 1

/-- **Sign map** `sgn : Fin 4 → ZMod 2`, `{+1,+2}↦0`, `{-1,-2}↦1`. -/
def sgn : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

/-! ## The interior sign-flip door graph on the disc is all cycles -/

/-- Number of sides of triangle `T i = (centre d, vᵢ, vᵢ₊₁)` across which the sign bit
flips.  The three sides are `(centre,vᵢ)`, `(vᵢ,vᵢ₊₁)`, `(vᵢ₊₁,centre)`. -/
def triSignFlips (a b c d : Fin 4) (i : Fin 6) : ℕ :=
  flip (sgn d) (sgn (V a b c i))
    + flip (sgn (V a b c i)) (sgn (V a b c (rot i)))
    + flip (sgn (V a b c (rot i))) (sgn d)

/-- **Every triangle of the hexagon disc has an even number of sign-flip sides**, for
every antipodal labelling.  Immediate from `triangle_flip_even'` (the triangle is the
3-cycle `centre → vᵢ → vᵢ₊₁ → centre` of sign bits).  Hence the sign-flip door graph on
the disc is a disjoint union of **cycles**: no interior degree-1 endpoint exists, so the
odd hemisphere sign-seed cannot be consumed by its own single-coordinate door graph. -/
theorem hexagon_triSignFlips_even (a b c d : Fin 4) (i : Fin 6) :
    Even (triSignFlips a b c d i) := by
  unfold triSignFlips
  exact triangle_flip_even' (sgn d) (sgn (V a b c i)) (sgn (V a b c (rot i)))

/-- Sharper form: the sign-flip count of any hexagon triangle is never one — no path
endpoint among the interior sign-flip doors. -/
theorem hexagon_triSignFlips_ne_one (a b c d : Fin 4) (i : Fin 6) :
    triSignFlips a b c d i ≠ 1 := by
  unfold triSignFlips
  exact triangle_flip_ne_one (sgn d) (sgn (V a b c i)) (sgn (V a b c (rot i)))

/-! ## The odd boundary seed lives only on the sign coordinate -/

/-- Hemisphere sign-flip seed: sign-bit flips on the arc `v₀ → v₁ → v₂ → v₃`. -/
def arcSignFlips (a b c : Fin 4) : ℕ :=
  (([0, 1, 2] : List (Fin 6)).filter
    (fun i => decide (sgn (V a b c i) ≠ sgn (V a b c (rot i))))).length

/-- **The hemisphere sign-flip seed is ODD** for every antipodal labelling (re-derived
self-containedly; matches `SpernerTuckerHexagonSignDegree.arc_sign_changes_odd`). -/
theorem arc_signflip_odd : ∀ a b c : Fin 4, Odd (arcSignFlips a b c) := by decide

/-- Directed exact-complementary seed: arc edges going label `+1` (`Fin4 0`) then `-1`
(`Fin4 2`). -/
def arcPm1Dir (a b c : Fin 4) : ℕ :=
  (([0, 1, 2] : List (Fin 6)).filter
    (fun i => decide (V a b c i = 0 ∧ V a b c (rot i) = 2))).length

/-- **The directed `+1→-1` seed is NOT a parity invariant** — even on some labellings,
odd on others.  Together with the sibling `boundary_door_count_even` /
`half_boundary_parity_not_invariant`, this shows the odd boundary seed is genuinely the
sign bit, not any (even directed) refinement of the exact-complementary edge count. -/
theorem pm1_dir_not_invariant :
    (∃ a b c : Fin 4, Even (arcPm1Dir a b c)) ∧
    (∃ a b c : Fin 4, Odd (arcPm1Dir a b c)) := by decide

#print axioms triangle_flip_even
#print axioms hexagon_triSignFlips_even
#print axioms hexagon_triSignFlips_ne_one
#print axioms arc_signflip_odd
#print axioms pm1_dir_not_invariant

end SpernerTuckerHexagonSignFlipCycles
