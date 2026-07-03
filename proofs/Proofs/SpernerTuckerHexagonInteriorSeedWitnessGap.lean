/-
# The interior seed can be witness-free: the directed door count over-states the Tucker witnesses (n = 2)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — closing on the honest gap left by the directed interior seed

The sibling entry `SpernerTuckerHexagonDirectedInteriorSeed` (oq-02-oq-08) proved that
the **directed pos→neg sign door rule** `dir (x → y) ⟺ sgn x = 0 ∧ sgn y = 1` drives the
path-following engine's even/odd handshake to an odd — in fact *exactly 3* — number of
degree-1 rooms whose single directed door lies on an **interior** spoke
(`exists_interior_room`, `interior_deg1_eq_three`).  That was the structural conclusion the
undirected sign-flip engine provably could not deliver.

But that entry's *honest status* flagged the remaining gap precisely: an "interior
degree-1 room" is only the terminal room of the Freund–Todd signed pivot, and **its interior
directed door coincides with a genuine complementary edge `λ u = -λ v` for only some of these
rooms** — so identifying the terminal room with the Tucker witness still needs more.  This
file *quantifies that gap on the concrete hexagon*, and the answer is sharper than "half":
the interior directed seed can be **entirely witness-free**.

## The two labels: sign vs. genuine complementarity

The directed rule reads only **signs** `sgn : Fin 4 → ZMod 2` (`{+1,+2} ↦ 0`, `{-1,-2} ↦ 1`),
firing on any oriented `+ → −` side.  A **genuine Tucker witness** is stronger: a side whose
two labels are *exactly antipodal*, `Compl x y := x = negL y` (`+1`/`−1` or `+2`/`−2`, not the
merely opposite-sign `+1`/`−2`).  Complementary labels always have opposite signs
(`compl_imp_opposite_sign`), so every genuine witness is a sign edge — but the converse fails
two ways:

* **Over-approximation.**  An opposite-sign side need not be complementary (`+1 → -2`).
* **Orientation blindness.**  `Compl` is symmetric, but the directed door only counts the
  `+ → −` orientation, so a complementary spoke oriented `− → +` is *not* a directed door
  (`orientation_blind_witness`).

## What this file proves (all by kernel `decide` / parity, 0 axioms)

* `compl_imp_opposite_sign` — `Compl x y → sgn x = sgn y + 1`: genuine complementarity forces
  opposite signs, so the sign door graph never *misses on sign* (only on orientation).
* `hexagon_tucker_directed` — every antipodal labelling `(a,b,c)` and centre `d` has a room
  side (a spoke `d–vᵢ` / `v_{i+1}–d` or the boundary edge `vᵢ–v_{i+1}`) that is genuinely
  complementary: the true n = 2 Tucker conclusion, restated in the directed model.
* `interiorComplDoor_le_interiorDeg1` — the genuinely-complementary interior seed rooms are a
  sub-count of the 3 interior degree-1 rooms (`≤` pointwise): the seed *contains* the true
  interior witnesses it does find.
* `interior_seed_can_be_witness_free` — **the headline separation.**  At the antipodal
  labelling `a = b = c = +1`, `d = +2` the directed rule still fires 3 interior degree-1 rooms
  (`interiorDeg1 = 3`) yet **none** of them carries a genuine complementary door
  (`interiorComplDoor = 0`).  The interior seed count 3 is therefore *not* a lower bound on the
  Tucker witnesses among interior rooms.
* `tucker_witness_is_on_boundary_there` — at that same labelling a genuine complementary edge
  nonetheless exists, and it is a **boundary** edge (`v₂–v₃ = (+1,-1)`): the witness the
  interior seed missed lives on the boundary.
* `interiorComplDoor_not_constant` — the complementary interior count is genuinely
  labelling-dependent (`= 0` at `(+1,+1,+1,+2)`, `= 3` at `(+1,+1,+1,+1)`): it is *not*
  determined by the seed count.
* `orientation_blind_witness` — an explicit complementary interior spoke whose directed door
  is `0` because it is oriented `− → +`: the concrete cause of the under-count.

## Honest status

A **positive scoping / obstruction result**, 0 sorries / 0 axioms.  It does **not** prove
n = 2 Tucker (that is `hexagon_tucker_directed` here and its siblings) — it *bounds what the
directed interior seed can be trusted to deliver*.  The seed of oq-02-oq-08 always produces 3
interior degree-1 rooms, but `interior_seed_can_be_witness_free` shows those rooms can *all*
be non-witnesses while the true witness sits on the boundary.  Hence the Freund–Todd
identification of the pivot-terminal room with the Tucker complementary simplex genuinely
requires the orientation-completion / boundary-accounting the bare interior seed omits — it
cannot be read off the sign-door count alone.  This is the concrete, machine-checked reason
the remaining geometric construction is still work.

Self-contained: imports Mathlib only, all definitions restated (same encoding as
`SpernerTuckerHexagonDirectedInteriorSeed`).  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`).
-/
import Mathlib

namespace SpernerTuckerHexagonInteriorSeedWitnessGap

open Finset

/-! ## Labelling model (identical encoding to `SpernerTuckerHexagonDirectedInteriorSeed`) -/

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The six boundary labels from three free labels `a,b,c` on `v₀,v₁,v₂`, antipodal
`v_{i+3} = -vᵢ`. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- Cyclic successor around the hexagon boundary. -/
def rot (i : Fin 6) : Fin 6 := i + 1

/-- **Sign map** `sgn : Fin 4 → ZMod 2`, `{+1,+2}↦0`, `{-1,-2}↦1`. -/
def sgn : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

/-- **Directed door indicator**: `1` iff the oriented sign edge runs `+ → −`. -/
def dir (x y : ZMod 2) : ℕ := if x = 0 ∧ y = 1 then 1 else 0

/-- **Genuine complementarity**: the two labels are exactly antipodal (`+1`/`−1` or `+2`/`−2`),
the true Tucker-witness relation — strictly stronger than merely opposite signs. -/
def Compl (x y : Fin 4) : Prop := x = negL y

instance : DecidableRel Compl := fun x y => decEq x (negL y)

/-! ## Sign is a necessary but insufficient shadow of complementarity -/

/-- **Complementary ⟹ opposite signs.**  So a genuine witness is always a *sign* edge: the
directed door graph never fails to see a witness *on sign* — only, as below, on orientation. -/
theorem compl_imp_opposite_sign : ∀ x y : Fin 4, Compl x y → sgn x = sgn y + 1 := by decide

/-! ## Rooms of the disc and their interior directed doors (as in oq-02-oq-08) -/

/-- Directed doors on the two **interior** spokes of room `i` (`d → vᵢ`, `v_{i+1} → d`). -/
def intDoor (a b c d : Fin 4) (i : Fin 6) : ℕ :=
  dir (sgn d) (sgn (V a b c i)) + dir (sgn (V a b c (rot i))) (sgn d)

/-- Directed door on the **boundary** side `vᵢ → v_{i+1}` of room `i`. -/
def bdDoor (a b c _d : Fin 4) (i : Fin 6) : ℕ :=
  dir (sgn (V a b c i)) (sgn (V a b c (rot i)))

/-- Total directed door count of room `i` (`≤ 1`, path structure). -/
def roomDoor (a b c d : Fin 4) (i : Fin 6) : ℕ :=
  intDoor a b c d i + bdDoor a b c d i

/-- Number of degree-1 rooms whose single door is on an **interior** spoke — the directed
interior seed of `SpernerTuckerHexagonDirectedInteriorSeed`. -/
def interiorDeg1 (a b c d : Fin 4) : ℕ :=
  #{i : Fin 6 | roomDoor a b c d i = 1 ∧ intDoor a b c d i = 1}

/-- The directed interior seed is **always three** rooms (restated from oq-02-oq-08). -/
theorem interiorDeg1_eq_three : ∀ a b c d, interiorDeg1 a b c d = 3 := by decide

/-! ## Genuine complementarity on the interior seed rooms

A room `i` is a *complementary* interior seed room when it is an interior degree-1 room
(`roomDoor = 1`, `intDoor = 1`) **and** the interior spoke carrying its directed door is
genuinely complementary — i.e. the room is a true Tucker terminal, not merely an opposite-sign
one.  `Compl (d) (V … i)` is the door on `d → vᵢ`; `Compl (V … (rot i)) d` the door on
`v_{i+1} → d`. -/

/-- Does room `i`'s interior directed door sit on a genuinely complementary spoke? -/
def intDoorCompl (a b c d : Fin 4) (i : Fin 6) : Bool :=
  (dir (sgn d) (sgn (V a b c i)) = 1 && decide (Compl d (V a b c i))) ||
  (dir (sgn (V a b c (rot i))) (sgn d) = 1 && decide (Compl (V a b c (rot i)) d))

/-- Number of interior degree-1 rooms whose directed door is a **genuine** complementary
witness — the sub-count of `interiorDeg1` that actually certifies Tucker at an interior spoke. -/
def interiorComplDoor (a b c d : Fin 4) : ℕ :=
  #{i : Fin 6 | (roomDoor a b c d i = 1 ∧ intDoor a b c d i = 1) ∧ intDoorCompl a b c d i}

/-- **The genuine interior witnesses are a sub-count of the seed.**  Every complementary
interior seed room is in particular an interior degree-1 room, so `interiorComplDoor ≤
interiorDeg1` pointwise: the seed *contains* whatever true interior witnesses exist. -/
theorem interiorComplDoor_le_interiorDeg1 :
    ∀ a b c d, interiorComplDoor a b c d ≤ interiorDeg1 a b c d := by decide

/-! ## The n = 2 Tucker conclusion in the directed model -/

/-- **n = 2 Tucker (directed model).**  For every antipodal labelling `(a,b,c)` and centre `d`
some room side is genuinely complementary: a boundary edge `vᵢ–v_{i+1}` or an interior spoke
`d–vᵢ`.  (`Compl` is symmetric-up-to-`negL`; a spoke `d–vᵢ` is complementary iff `Compl d vᵢ`
or `Compl vᵢ d`.)  The true conclusion the obstruction below is read against. -/
theorem hexagon_tucker_directed : ∀ a b c d : Fin 4,
    ∃ i : Fin 6,
      Compl (V a b c i) (V a b c (rot i)) ∨ Compl d (V a b c i) ∨ Compl (V a b c i) d := by
  decide

/-! ## The headline separation: the interior seed can be witness-free -/

/-- **The interior directed seed can carry zero genuine witnesses.**  At the antipodal
labelling `a = b = c = +1` (`= 0`), centre `d = +2` (`= 1`) the directed rule still fires
`interiorDeg1 = 3` interior degree-1 rooms, yet **none** of their doors is genuinely
complementary (`interiorComplDoor = 0`): every boundary vertex is `±1`, so no spoke can be
antipodal to the centre `+2` whose partner `-2` is absent.  The seed count `3` is therefore
*not* a lower bound on the interior Tucker witnesses. -/
theorem interior_seed_can_be_witness_free :
    interiorDeg1 0 0 0 1 = 3 ∧ interiorComplDoor 0 0 0 1 = 0 := by decide

/-- **…yet Tucker still holds — on the boundary.**  At that same labelling the genuine
complementary edge the interior seed missed is the boundary edge `v₂–v₃ = (+1,-1)`
(`Compl (V 0 0 0 2) (V 0 0 0 3)`), *not* any interior spoke.  Concretely why the terminal
room cannot be identified with the Tucker witness by the sign door alone: here the witness
is not on any seed door at all. -/
theorem tucker_witness_is_on_boundary_there :
    Compl (V 0 0 0 2) (V 0 0 0 (rot 2)) := by decide

/-- **The complementary interior count is not determined by the seed.**  It is a genuine
function of the labelling — `0` at `(+1,+1,+1,+2)`, `3` at `(+1,+1,+1,+1)` — even though
`interiorDeg1` is the constant `3` throughout.  So no fixed fraction of the seed is witness:
the sign door count carries no information about how many interior rooms are true witnesses. -/
theorem interiorComplDoor_not_constant :
    interiorComplDoor 0 0 0 1 = 0 ∧ interiorComplDoor 0 0 0 0 = 3 := by decide

/-- **Orientation blindness, concretely.**  At `a = b = c = d = +1` the interior spoke
`v₃ → d = (-1) → (+1)` is genuinely complementary (`Compl (V 0 0 0 3) 0`, since `negL 0 = 2 =
V 0 0 0 3`) but its directed door is `0` — the `+ → −` rule does not count the `− → +`
orientation.  This is the mechanism by which the directed seed *under*-counts complementary
spokes even as it *over*-counts via non-antipodal opposite-sign edges. -/
theorem orientation_blind_witness :
    Compl (V 0 0 0 3) 0 ∧ dir (sgn (V 0 0 0 3)) (sgn 0) = 0 := by decide

#print axioms compl_imp_opposite_sign
#print axioms hexagon_tucker_directed
#print axioms interiorComplDoor_le_interiorDeg1
#print axioms interiorDeg1_eq_three
#print axioms interior_seed_can_be_witness_free
#print axioms tucker_witness_is_on_boundary_there
#print axioms interiorComplDoor_not_constant
#print axioms orientation_blind_witness

end SpernerTuckerHexagonInteriorSeedWitnessGap
