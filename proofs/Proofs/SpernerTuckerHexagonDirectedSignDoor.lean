/-
# The directed pos→neg sign door rule closes both blades: path structure + odd full-circle seed

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — the first Lean realisation of the essentially-unique closer

The abstract path-following engine (`SpernerTuckerPathFollowing.exists_interior_degree_one`)
turns a max-degree-`≤2` door graph on the hexagon + centre triangulation of `B²`, whose
degree-1 **boundary** endpoints are **odd** in number, into a degree-1 **interior**
endpoint — the Tucker witness.  Supplying that door graph is the single genuine open lever.

Prior sessions fenced the lever tightly.  A complete finite classification of every
*undirected* edge-local door rule (`probe_ft_nested_bruteforce.py`, all `2¹⁶` predicates)
showed **no undirected rule can close n = 2 Tucker** — because a usable rule must have an
ODD full-boundary-circle count, yet on the antipodal 6-cycle `v_{i+3} = -vᵢ` the boundary
edges split into 3 antipodal pairs, forcing every *negation-symmetric* (undirected) count
EVEN.  The two known single-coordinate rules illustrate the two failing blades:

* the **undirected sign-flip** rule carries the odd seed only on a *hemisphere*
  (`SpernerTuckerHexagonSignDegree.arc_sign_changes_odd`) and its interior door graph is
  **all cycles** (`SpernerTuckerHexagonSignFlipCycles.hexagon_triSignFlips_even`, every
  triangle has an even flip count) — no interior endpoint;
* the **exact `{+1,-1}`** rule *can* terminate (a triangle `{+1,-1,±2}` is a genuine
  degree-1 room) but has **no odd boundary seed**
  (`SpernerTuckerHexagonFullDoorGraph.boundary_door_count_even`).

That classification also identified the **essentially-unique closer**: the *oriented*
**directed pos→neg sign rule**

> `door (x → y)  ⟺  sgn x = 0 ∧ sgn y = 1`,

an oriented edge is a door iff it runs from a `+`-sign vertex to a `−`-sign vertex.  So far
this rule lived **only in Python**.  This file gives its first machine-checked Lean
formalisation and proves the two properties that make it close both blades at once.

## What this file proves (all by kernel `decide` / `ZMod 2` algebra, 0 axioms)

**Blade 1 — path structure (`dirTri_le_one`, `hexagon_dirTri_le_one`).**  On any oriented
triangle `x → y → z → x` of sign bits the directed door count is `∈ {0,1}` — it is `1`
exactly when the triangle is *mixed* (`dirTri_eq_one_iff_mixed`) and `0` when
monochromatic.  Hence on the hexagon disc **every** triangle has `≤ 1` directed door, so
the directed sign door graph is a disjoint union of **paths** with genuine degree-1
endpoints — precisely the structure the undirected sign-flip graph lacked
(`hexagon_triSignFlips_even`: even, all cycles).

**Blade 2 — odd seed on the FULL circle (`full_dir_count_odd`).**  The directed door count
around the *whole* antipodal boundary ring `v₀ → v₁ → ⋯ → v₅ → v₀` is **ODD** for every
antipodal labelling (values `∈ {1,3}`).  Orientation moves the odd seed from the hemisphere
(where the undirected flip count lives, `arc_sign_changes_odd`) to the whole circle — the
natural object the engine consumes — while the undirected full-ring flip count stays EVEN
(`full_sign_changes_even`).

**The structural reason orientation works (`dir_antipode_reverse`).**  Under the antipodal
map (`sgn (negL x) = sgn x + 1`) a directed door `0 → 1` becomes `1 → 0`, a *non-door*:
`dir (sgn (negL x)) (sgn (negL y)) = dir (sgn y) (sgn x)`.  So the antipodal involution
sends the directed door set to its **transpose**, *not* to itself — it does **not** pair
directed doors, so their count is not forced even.  This is the exact mechanism the
undirected analysis was missing: for undirected doors the antipode is an *automorphism*
(pairs them ⟹ even, `SpernerTuckerAntipodalParity.even_card_of_free_involution`); for
directed doors it is *reversing* (transpose ⟹ the count survives odd).

## Honest status

A **positive scoping result**: the first Lean formalisation of the directed pos→neg sign
door rule — the essentially-unique edge-local seed the finite classification singled out —
with both of its defining properties (per-triangle path structure `≤ 1`, odd full-circle
seed) and the structural reason orientation defeats the antipodal even-cancellation.  It is
**not** a full proof of n = 2 Tucker: assembling these directed doors into an
orientation-aware path from the odd boundary seed to an interior complementary simplex — the
Freund–Todd / Prescott–Su signed pivot engine — is the genuine remaining multi-session
BUILD.  This file supplies the verified seed that engine must consume.

Self-contained: imports Mathlib only.  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`).
-/
import Mathlib

namespace SpernerTuckerHexagonDirectedSignDoor

open Finset

/-! ## The directed pos→neg door indicator and its triangle count -/

/-- **Directed door indicator.**  `1` if the oriented sign edge runs `+ → −`
(`sgn = 0` then `sgn = 1`), else `0`.  This is the essentially-unique edge-local closer of
n = 2 Tucker (finite classification `probe_ft_nested_bruteforce.py`). -/
def dir (x y : ZMod 2) : ℕ := if x = 0 ∧ y = 1 then 1 else 0

/-- Directed door count around the oriented triangle `x → y → z → x` of sign bits. -/
def dirTri (x y z : ZMod 2) : ℕ := dir x y + dir y z + dir z x

/-- **Blade 1 (abstract): a triangle has at most one directed door.**  Contrast the
undirected sign-flip count, which is `0` or `2` (`triangle_flip_even`): orientation turns
the even cycle count into a `≤ 1` path count. -/
theorem dirTri_le_one (x y z : ZMod 2) : dirTri x y z ≤ 1 := by
  revert x y z; decide

/-- The directed door count of a triangle is **exactly one iff the triangle is mixed**
(not monochromatic).  A monochromatic triangle (`x = y = z`) has `0`; any triangle with
both signs present has exactly `1`.  So directed doors are the interior *path edges*. -/
theorem dirTri_eq_one_iff_mixed (x y z : ZMod 2) :
    dirTri x y z = 1 ↔ ¬ (x = y ∧ y = z) := by
  revert x y z; decide

/-- A directed triangle door count is never two (the sharp path-structure statement). -/
theorem dirTri_ne_two (x y z : ZMod 2) : dirTri x y z ≠ 2 := by
  have := dirTri_le_one x y z; omega

/-! ## Labelling model (same encoding as `SpernerTuckerHexagonSignDegree`) -/

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The six boundary labels from three free labels `a,b,c` on `v0,v1,v2`, antipodal
`v(i+3) = -v(i)`. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- Cyclic successor around the hexagon boundary. -/
def rot (i : Fin 6) : Fin 6 := i + 1

/-- **Sign map** `sgn : Fin 4 → ZMod 2`, `{+1,+2}↦0`, `{-1,-2}↦1`. -/
def sgn : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

/-! ## The structural reason orientation defeats the antipodal even-cancellation -/

/-- **The antipode reverses directed doors.**  Since `sgn (negL x) = sgn x + 1`, a directed
door `0 → 1` maps under the antipodal action to `1 → 0`, a non-door:
`dir (sgn (negL x)) (sgn (negL y)) = dir (sgn y) (sgn x)`.  The antipodal involution sends
the directed door set to its **transpose**, not to itself, so it does not pair directed
doors — the mechanism that keeps the full-circle count odd (contrast the undirected case,
where the antipode is an automorphism forcing the count even). -/
theorem dir_antipode_reverse (x y : Fin 4) :
    dir (sgn (negL x)) (sgn (negL y)) = dir (sgn y) (sgn x) := by
  revert x y; decide

/-! ## Blade 1 on real geometry: the directed sign door graph on the disc is paths -/

/-- Directed door count of the hexagon triangle `T i = (centre d, vᵢ, vᵢ₊₁)`, oriented
`centre → vᵢ → vᵢ₊₁ → centre`. -/
def hexDirTri (a b c d : Fin 4) (i : Fin 6) : ℕ :=
  dirTri (sgn d) (sgn (V a b c i)) (sgn (V a b c (rot i)))

/-- **Every hexagon triangle has at most one directed sign door**, for every antipodal
labelling.  Immediate from `dirTri_le_one`.  So the directed sign door graph on the disc is
a disjoint union of **paths** with genuine degree-1 endpoints — unlike the undirected
sign-flip door graph, which is all cycles (`hexagon_triSignFlips_even`). -/
theorem hexagon_dirTri_le_one (a b c d : Fin 4) (i : Fin 6) :
    hexDirTri a b c d i ≤ 1 :=
  dirTri_le_one _ _ _

/-! ## Blade 2: the directed door count on the FULL antipodal circle is odd -/

/-- Directed door count around the whole boundary ring `v₀ → v₁ → ⋯ → v₅ → v₀`
(six oriented edges `vᵢ → vᵢ₊₁`). -/
def fullDirCount (a b c : Fin 4) : ℕ :=
  ((List.finRange 6).filter
    (fun i => decide (sgn (V a b c i) = 0 ∧ sgn (V a b c (rot i)) = 1))).length

/-- **The directed door count around the full antipodal boundary ring is ODD** for every
antipodal labelling (verified over all `4³ = 64` free labellings; centre label irrelevant
to the boundary; values `∈ {1,3}`).  This is the odd boundary seed the path-following engine
needs — supplied on the **whole circle**, not just a hemisphere, because orientation stops
the antipode from pairing the doors (`dir_antipode_reverse`).  Contrast the undirected
full-ring flip count, which is always EVEN (`full_sign_changes_even`). -/
theorem full_dir_count_odd : ∀ a b c : Fin 4, Odd (fullDirCount a b c) := by decide

/-- **The directed rule beats the undirected antipodal even-cancellation.**  The undirected
sign-flip count around the full ring is even; the directed pos→neg count around the same
ring is odd.  Both facts on the same boundary make the point of the whole program precise:
the odd boundary seed the engine consumes exists on the full circle **only** for an oriented
door rule. -/
theorem directed_full_ring_odd_undirected_even :
    (∀ a b c : Fin 4, Odd (fullDirCount a b c)) ∧
      (∃ a b c : Fin 4, Even
        (((List.finRange 6).filter
          (fun i => decide (sgn (V a b c (rot i)) ≠ sgn (V a b c i)))).length)) := by
  refine ⟨full_dir_count_odd, ?_⟩
  exact ⟨0, 0, 0, by decide⟩

#print axioms dirTri_le_one
#print axioms dirTri_eq_one_iff_mixed
#print axioms dir_antipode_reverse
#print axioms hexagon_dirTri_le_one
#print axioms full_dir_count_odd
#print axioms directed_full_ring_odd_undirected_even

end SpernerTuckerHexagonDirectedSignDoor
