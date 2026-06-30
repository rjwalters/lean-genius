/-
# Why the naive door choices fail for n = 2 Tucker: two machine-checked obstructions

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

The door-counting program for Tucker is, by now, **abstractly complete up to one
geometric input**.  The single-level path-following engine
(`SpernerTuckerPathFollowing.exists_interior_degree_one`) and the dimension
recursion (`SpernerTuckerInductiveTower.TuckerTower`) are fully verified; the sole
open obligation is the *geometric construction of the door graph* — concretely, a
family of max-degree-≤2 graphs on "almost-complementary" simplices whose
**interior degree-1 vertices are exactly the complementary simplices** Tucker
asserts (the Freund–Todd 1981 / Prescott–Su construction).

A natural hope is that this graph is something simple: pick one *fixed* sign `k`,
declare the **doors** to be the complementary edges of type `{+k,-k}`, and run the
engine on the triangles that carry such an edge.  The companion
`SpernerTuckerHexagon.lean` already kills the *first* naive simplification (the
**complementary-edge count is not a parity invariant** for n = 2, so "count the
target object and show it is odd" — the n = 1 route — cannot work).

This file kills the *second* naive simplification, on the same fully concrete
hexagon+centre triangulation of `B²`, entirely by kernel `decide` (0 axioms):

> **A door graph built from one fixed complementary sign is not a complete
> certificate.**  For a suitable antipodal labelling the entire "complementary
> spoke" door graph is *empty* (every triangle has door-degree 0, so the engine
> produces nothing) while Tucker's conclusion still holds — the complementary edge
> lives on the *boundary*, invisible to that door choice.

Together with `count_parity_not_invariant`, this pins down precisely why the
remaining geometric construction is genuine work: the correct Freund–Todd door
structure must (i) range over *all* signs, not a fixed one, and (ii) account for
boundary edges, rather than reading off a single interior door type.

## Model

The standard small antipodally-symmetric triangulation of `B²`: a hexagon with its
centre.  Boundary vertices `v 0,…,v 5` in antipodal pairs (`v (i+3) = -v i`), an
interior centre with label `d`, and six triangles `T i = (centre, v i, v (i+1))`.
Labels lie in `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1, 1↦+2, 2↦-1, 3↦-2`); `negL`
is label negation; an edge is **complementary** when its labels are negatives of
each other.  The boundary labelling is forced antipodal by setting the second
triple to the negations of the first.  (Same encoding as `SpernerTuckerHexagon`.)

The **spoke-door graph** picks the centre-incident edges (the *spokes*
`centre — v i`) that are complementary to `d` as its doors.  A triangle `T i` owns
the two spokes to `v i` and `v (i+1)`, each shared with the neighbouring triangle,
so its door-degree is the number of those two spokes that are complementary to `d`
— automatically `≤ 2` (`degSpoke_le_two`), exactly the engine's hypothesis.  The
obstruction is that this degree can be identically `0`.

## What this file proves

* `degSpoke_le_two` — the spoke-door graph has max degree ≤ 2 on *every* antipodal
  labelling: the engine's structural hypothesis `∀ v, G.degree v ≤ 2` is genuinely
  realized by a hexagon-derived graph (the engine is not vacuous on real geometry).
* `spoke_graph_empty_yet_complementary` — **the obstruction**: there is an antipodal
  labelling whose spoke-door graph is *empty* (no complementary spoke at all) yet a
  complementary boundary edge exists.  A single-sign interior door graph therefore
  cannot be a complete Tucker certificate.
* `hexagon_tucker` — Tucker's conclusion holds for *every* antipodal labelling
  (reproduced here so the obstruction is read against the true statement, not an
  assumption).

## Honest status

This is a **scoping / negative result**, not new Tucker geometry: it rules out a
tempting shortcut and sharpens what the open geometric construction must do.  It is
fully concrete (n = 2, kernel `decide`) and self-contained.  0 sorries, 0 axioms
(propext / Classical.choice / Quot.sound only — no `sorryAx`, no `Lean.ofReduceBool`).
-/
import Mathlib

namespace SpernerTuckerHexagonDoorObstruction

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`):
`+1 ↔ -1`, `+2 ↔ -2`.  An involution. -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- Two labels are **complementary** when one is the negation of the other. -/
def Compl (x y : Fin 4) : Prop := x = negL y

instance (x y : Fin 4) : Decidable (Compl x y) := inferInstanceAs (Decidable (x = negL y))

/-- The six boundary labels from three free labels `a, b, c` of `v 0, v 1, v 2`,
with the antipodal condition `v (i+3) = -v i` built in for `v 3, v 4, v 5`. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- The next boundary vertex around the hexagon (cyclic successor). -/
def rot (i : Fin 6) : Fin 6 := i + 1

/-- **Spoke-door degree** of triangle `T i = (centre, v i, v (i+1))`: the number of
its two spokes (`centre — v i`, `centre — v (i+1)`) that are complementary to the
centre label `d`.  Each spoke is shared with the neighbouring triangle, so this is
the degree of `T i` in the "complementary-spoke" door graph. -/
def degSpoke (a b c d : Fin 4) (i : Fin 6) : ℕ :=
  (if Compl d (V a b c i) then 1 else 0) + (if Compl d (V a b c (rot i)) then 1 else 0)

/-- **The spoke-door graph has max degree ≤ 2** on every antipodal labelling: the
engine's structural hypothesis `∀ v, G.degree v ≤ 2` (paths-and-cycles) is realized
by an actual hexagon-derived graph.  A triangle owns exactly two spokes, so it has
at most two complementary-spoke doors.  Verified over all `4⁴ = 256` antipodal
labellings × 6 triangles. -/
theorem degSpoke_le_two : ∀ a b c d : Fin 4, ∀ i : Fin 6, degSpoke a b c d i ≤ 2 := by
  decide

/-- **The obstruction: a single-sign door graph is not a complete certificate.**
There is an antipodal labelling on which the complementary-spoke door graph is
entirely empty — *no* spoke is complementary to the centre, so every triangle has
door-degree `0` and the path-following engine yields nothing — yet Tucker still
holds, the complementary edge living on the *boundary* of the hexagon.

(Witness: centre `d = +2` with all boundary vertices labelled `±1`.  Then no spoke
can be complementary, `negL (+2) = -2` appearing on no boundary vertex, while a
boundary edge `v i — v (i+1)` with labels `+1, -1` is complementary.)

Consequently the correct Freund–Todd door structure cannot read off a single fixed
interior door type: it must range over all signs and account for boundary edges. -/
theorem spoke_graph_empty_yet_complementary :
    ∃ a b c d : Fin 4,
      (∀ i : Fin 6, ¬ Compl d (V a b c i)) ∧
      (∃ i : Fin 6, Compl (V a b c i) (V a b c (rot i))) := by
  decide

/-- **n = 2 Tucker on the hexagon** (reproduced from `SpernerTuckerHexagon`, so the
obstruction above is read against the true conclusion).  For every antipodal
labelling and every centre label `d`, the triangulation has a complementary edge —
a boundary edge `v i — v (i+1)` or a spoke `centre — v i`.  Verified exhaustively
over all `256` antipodal labellings. -/
theorem hexagon_tucker :
    ∀ a b c d : Fin 4,
      (∃ i : Fin 6, Compl (V a b c i) (V a b c (rot i))) ∨
      (∃ i : Fin 6, Compl d (V a b c i)) := by
  decide

#check @degSpoke_le_two
#check @spoke_graph_empty_yet_complementary
#check @hexagon_tucker

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms degSpoke_le_two
#print axioms spoke_graph_empty_yet_complementary
#print axioms hexagon_tucker

end SpernerTuckerHexagonDoorObstruction
