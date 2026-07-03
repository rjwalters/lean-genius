/-
# The directed pos→neg rule reaches the interior: an odd number of interior degree-1 rooms

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — the directed rule fixes the sign-flip engine's diagnostic

The abstract path-following engine
`SpernerTuckerPathFollowing.exists_interior_degree_one` turns two hypotheses on a
door graph — **even** total endpoint count (handshaking) and an **odd** number of
*boundary* endpoints — into a degree-1 endpoint that is **interior**, i.e. a Tucker
witness room.  Its first concrete instantiation,
`SpernerTuckerHexagonSignFlipEngine`, fired the engine on the *undirected* Sperner
sign-flip door graph and produced only a **diagnostic**: the engine's endpoint is
always a boundary edge of the opposite hemisphere, *never* interior
(`endpoint_is_far_hemisphere_signflip`).  The brute classification
`probe_ft_nested_bruteforce.py` explained why: **no** undirected edge-local rule can
supply an odd full-circle boundary seed (all such rules are negation-symmetric, so the
antipodal 6-cycle pairs their doors and forces the seed even), and of the 52 *oriented*
edge-local rules that do give an odd seed with room-degree ≤ 2, exactly 4 additionally
place an interior degree-1 room for **every** labelling.

The **directed pos→neg sign door rule** `dir (x → y) ⟺ sgn x = 0 ∧ sgn y = 1`
(`SpernerTuckerHexagonDirectedSignDoor`, mask `0x00cc` in the probe) is one of those 4.
Prior iterations verified its two abstract *blades* — every hexagon triangle has ≤ 1
directed door (`hexagon_dirTri_le_one`, path structure) and the full antipodal boundary
ring carries an **odd** directed door count (`full_dir_count_odd`, odd seed).  This file
runs those blades through the engine's parity split **on the disc rooms** and reaches
the conclusion the sign-flip engine could not: an odd — hence non-zero — number of
degree-1 rooms whose single door is **interior**.

## The disc rooms and their directed doors

Each triangle `Tᵢ = (centre d, vᵢ, v_{i+1})` of the hexagon+centre triangulation of `B²`
is a *room*, oriented `d → vᵢ → v_{i+1} → d`.  Its three oriented sides split into two
**interior** spokes (`d → vᵢ`, `v_{i+1} → d`) and one **boundary** edge (`vᵢ → v_{i+1}`).
`roomDoor` counts the directed doors on all three sides (`= hexDirTri`, so `≤ 1` by
`room_door_le_one`); `intDoor` counts only the two interior spokes, `bdDoor` only the
boundary edge.  A **degree-1 room** is one with `roomDoor = 1`; it is *interior* when that
one door sits on an interior spoke (`intDoor = 1`) and *boundary* when on the boundary
edge (`bdDoor = 1`).

## What this file proves (all by kernel `decide` / parity, 0 axioms)

* `total_deg1_even` — the total number of degree-1 rooms is **even** (`∈ {4, 6}`): the
  handshaking half of the engine, realised on the disc rooms.
* `boundary_deg1_odd` — the number of *boundary* degree-1 rooms is **odd** (`∈ {1, 3}`):
  the odd boundary seed, matching `full_dir_count_odd`.
* `handshake_split` — total `=` interior `+` boundary degree-1 rooms (every degree-1 room
  is interior or boundary, exclusively, because `roomDoor ≤ 1`).
* `interior_deg1_odd` — **hence** the number of *interior* degree-1 rooms is **odd**:
  `even − odd = odd`.  This is `exists_interior_degree_one`'s exact parity mechanism
  (even total, odd boundary ⟹ odd interior) run by hand on the concrete rooms.
* `interior_deg1_eq_three` — sharply, that interior count is **always 3**.
* `exists_interior_room` — the payoff, obtained **from the parity count** (`card_pos`,
  not brute enumeration): for every antipodal labelling `(a,b,c)` and centre `d`, there
  is a room with exactly one directed door lying on an interior spoke.

Contrast `SpernerTuckerHexagonSignFlipEngine`, whose interior endpoint count is `0`:
orientation moves the odd seed from a hemisphere to the whole circle, and the resulting
even/odd handshake pushes an odd, positive count of endpoints into the **interior**.

## Honest status

A **positive scoping result**, 0 sorries / 0 axioms.  The door-counting parity now
*forces* an interior degree-1 room to exist — the structural conclusion the sign-flip
reduction provably could not deliver.  It is **not** a full proof of n = 2 Tucker: an
"interior degree-1 room" is the terminal room of the Freund–Todd signed pivot, and its
interior directed door coincides with a genuine complementary edge (`λ u = -λ v`) for
only half of these rooms, so identifying the terminal room with the Tucker witness still
needs the pivot-connectivity argument.  (The bare existence of a complementary edge is
already machine-checked separately in `SpernerTuckerHexagonComplementaryEdge`.)  What is
new here is the *mechanism*: the oriented door count drives the even/odd handshake to a
non-zero **interior** endpoint count, which the entire undirected edge-local class cannot.

Self-contained: imports Mathlib and the sibling engine.  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`).
-/
import Mathlib

namespace SpernerTuckerHexagonDirectedInteriorSeed

open Finset

/-! ## Labelling model (identical encoding to `SpernerTuckerHexagonDirectedSignDoor`) -/

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

/-! ## Rooms of the disc and their interior / boundary directed doors

Room `Tᵢ = (centre d, vᵢ, v_{i+1})` oriented `d → vᵢ → v_{i+1} → d`.  Its two interior
spokes are `d → vᵢ` and `v_{i+1} → d`; its boundary side is `vᵢ → v_{i+1}`. -/

/-- Directed doors on the two **interior** spokes of room `i`. -/
def intDoor (a b c d : Fin 4) (i : Fin 6) : ℕ :=
  dir (sgn d) (sgn (V a b c i)) + dir (sgn (V a b c (rot i))) (sgn d)

/-- Directed door on the **boundary** side of room `i`.  (The centre label `_d` is
carried only for signature uniformity with `intDoor` / `roomDoor`; the boundary edge does
not see the centre.) -/
def bdDoor (a b c _d : Fin 4) (i : Fin 6) : ℕ :=
  dir (sgn (V a b c i)) (sgn (V a b c (rot i)))

/-- Total directed door count of room `i` (its three oriented sides).  Equal to
`SpernerTuckerHexagonDirectedSignDoor.hexDirTri`, hence `≤ 1`. -/
def roomDoor (a b c d : Fin 4) (i : Fin 6) : ℕ :=
  intDoor a b c d i + bdDoor a b c d i

/-- **Every room has at most one directed door** (path structure, the disc form of
`hexagon_dirTri_le_one`).  So a degree-1 room's single door is *either* interior *or*
boundary, never both. -/
theorem room_door_le_one : ∀ a b c d i, roomDoor a b c d i ≤ 1 := by decide

/-! ## The three degree-1 room counts -/

/-- Number of degree-1 rooms whose single door is on an **interior** spoke. -/
def interiorDeg1 (a b c d : Fin 4) : ℕ :=
  #{i : Fin 6 | roomDoor a b c d i = 1 ∧ intDoor a b c d i = 1}

/-- Number of degree-1 rooms whose single door is on the **boundary** side. -/
def boundaryDeg1 (a b c d : Fin 4) : ℕ :=
  #{i : Fin 6 | roomDoor a b c d i = 1 ∧ bdDoor a b c d i = 1}

/-- Total number of degree-1 rooms. -/
def totalDeg1 (a b c d : Fin 4) : ℕ :=
  #{i : Fin 6 | roomDoor a b c d i = 1}

/-! ## The engine's parity mechanism, on the concrete disc rooms -/

/-- **Handshaking half.**  The total number of degree-1 rooms is **even** (values
`∈ {4, 6}` over all antipodal labellings) — the concrete-room form of the engine's
`even_card_degree_one`. -/
theorem total_deg1_even : ∀ a b c d, Even (totalDeg1 a b c d) := by decide

/-- **Odd boundary seed.**  The number of *boundary* degree-1 rooms is **odd** (values
`∈ {1, 3}`), the room count of the odd full-circle directed seed (`full_dir_count_odd`).
Every boundary degree-1 room contributes its one boundary directed door. -/
theorem boundary_deg1_odd : ∀ a b c d, Odd (boundaryDeg1 a b c d) := by decide

/-- **The split.**  Every degree-1 room is interior or boundary, exclusively (because
`roomDoor ≤ 1`), so total `=` interior `+` boundary. -/
theorem handshake_split : ∀ a b c d,
    totalDeg1 a b c d = interiorDeg1 a b c d + boundaryDeg1 a b c d := by decide

/-- **The payoff parity: an odd number of interior degree-1 rooms.**  Even total minus
odd boundary is odd — the exact `exists_interior_degree_one` mechanism (even endpoints,
odd boundary ⟹ odd interior), here forcing the *interior* endpoint count odd.  Derived
from `total_deg1_even`, `boundary_deg1_odd`, `handshake_split`, **not** by re-enumeration:
the door-counting handshake *drives* the conclusion. -/
theorem interior_deg1_odd (a b c d : Fin 4) : Odd (interiorDeg1 a b c d) := by
  have hs := handshake_split a b c d
  have ht := total_deg1_even a b c d
  have hb := boundary_deg1_odd a b c d
  rw [Nat.even_iff] at ht
  rw [Nat.odd_iff] at hb ⊢
  omega

/-- **Sharp count: exactly three interior degree-1 rooms**, for every antipodal labelling
and centre.  (`interior_deg1_odd` is the parity-driven half; this is the exact value.) -/
theorem interior_deg1_eq_three : ∀ a b c d, interiorDeg1 a b c d = 3 := by decide

/-- The interior degree-1 room count is **positive** — the door-counting handshake alone
already yields this (odd ⟹ ≥ 1), independent of the sharp value. -/
theorem interior_deg1_pos (a b c d : Fin 4) : 0 < interiorDeg1 a b c d := by
  have h := interior_deg1_odd a b c d
  rw [Nat.odd_iff] at h
  omega

/-- **The directed rule reaches the interior.**  For every antipodal boundary labelling
`(a,b,c)` and centre label `d`, there is a room with exactly one directed door, sitting on
an **interior** spoke — a Freund–Todd pivot-terminal room.  Obtained *from the parity
count* (`Finset.card_pos` on `interior_deg1_pos`), the concrete realisation of
`SpernerTuckerPathFollowing.exists_interior_degree_one` with a **positive** interior
endpoint count — precisely what `SpernerTuckerHexagonSignFlipEngine` (interior count `0`)
could not produce. -/
theorem exists_interior_room (a b c d : Fin 4) :
    ∃ i : Fin 6, roomDoor a b c d i = 1 ∧ intDoor a b c d i = 1 := by
  have hpos : 0 < interiorDeg1 a b c d := interior_deg1_pos a b c d
  unfold interiorDeg1 at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hi
  exact ⟨i, hi.2⟩

#print axioms room_door_le_one
#print axioms total_deg1_even
#print axioms boundary_deg1_odd
#print axioms handshake_split
#print axioms interior_deg1_odd
#print axioms interior_deg1_eq_three
#print axioms exists_interior_room

end SpernerTuckerHexagonDirectedInteriorSeed
