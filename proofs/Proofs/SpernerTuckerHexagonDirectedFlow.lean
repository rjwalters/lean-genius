/-
# The abstract directed FLOW engine fires on the concrete hexagon: an odd boundary seed forces a source room

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — the first concrete instantiation of the directed flow engine

`SpernerTuckerDirectedIncidenceFlow.lean` builds the abstract *directed* door engine
and proves the master flow-conservation law

  `#sources − #sinks = #boundary-out − #boundary-in`

together with `exists_source_of_more_boundary_out`: an out-heavy directed boundary
forces a **source** cell (a directed path root).  Every prior session's frontier note
recorded that this engine had *not yet been instantiated on real hexagon geometry* —
the concrete disc door structure had only ever been fed to the *undirected* door graph
(`SpernerTuckerHexagonDirectedEngine`) and the *path-following* engine
(`SpernerTuckerHexagonDirectedInteriorSeed`).  The knowledge-base "next step" was
verbatim:

> Instantiate the directed complex on the concrete disc (hexagon) door structure and
> discharge the `out,in ≤ 1` and well-formed hypotheses, connecting `dirCount_odd`'s
> odd `#boundary-out` to `exists_source_of_more_boundary_out`.

**This file does exactly that.**  It builds a concrete directed door complex on the
hexagon+centre triangulation of `B²` from the pos→neg sign rule, discharges the engine's
`hdeg` (out/in-degree ≤ 1) and well-formedness hypotheses over *every* antipodal
labelling, and fires the abstract flow engine to obtain a **source room** — a directed
path start — for every antipodal labelling.

## The construction

* **Cells** `Fin 6`: the six disc triangles `Tᵢ = (centre, vᵢ, v_{i+1})`, each oriented
  counter-clockwise `centre → vᵢ → v_{i+1} → centre`.
* **Doors** `Fin 6 ⊕ Fin 6`: `inl j` is the spoke `{centre, v_j}` (shared by `T_{j-1}`
  and `T_j`); `inr k` is the boundary edge `{v_k, v_{k+1}}` (bordering `T_k` and the
  outside of the disc).
* **Orientation (`tail` / `head`).**  A door is *open* iff it is a directed pos→neg sign
  door in its physical orientation.  The two triangles sharing a spoke traverse it in
  *opposite* directions (`Tⱼ` runs `centre → v_j`, `T_{j-1}` runs `v_j → centre`), so an
  open spoke is a **forward exit** of exactly one triangle (its `tail`) and a **backward
  entry** of the other (its `head`) — an interior door.  An open boundary edge is a
  forward exit of its unique triangle `T_k` and exits through the disc boundary (no head
  cell) — a **boundary-out** door.

## Why the hypotheses hold — the Freund–Todd path structure, structurally

* **`hdeg` (out/in-degree ≤ 1).**  A triangle's *out-degree* is the number of its three
  oriented sides that run pos→neg forward — which is `≤ 1` (this is exactly
  `SpernerTuckerHexagonDirectedInteriorSeed.room_door_le_one`, the disc form of
  `hexagon_dirTri_le_one`).  Its *in-degree* counts the two spokes traversed backward
  pos→neg; both would force the centre label into opposite hemispheres, so `≤ 1`.  This
  is Freund–Todd non-degeneracy realised: every room lies on a directed path.
* **`hwf`+absent (every door interior / boundary-out / boundary-in / absent).**  A spoke
  is interior when open, absent when closed; a boundary edge is boundary-out when open,
  absent when closed.  (The hexagon inevitably has *closed* edges — doors with no ends —
  which the base engine's `hwf` excludes; §1 supplies the mild generalisation admitting
  such absent doors, which contribute `0` to the net flow.)
* **`himb` (out-heavy boundary).**  Every boundary edge, when open, is boundary-out; none
  is ever boundary-in (the outer end is always missing), so `#boundary-in = 0`, while
  `#boundary-out` is the directed boundary-circle count — **odd** (values `{1,3}`), the
  `SpernerTuckerHexagonDirectedInteriorSeed.boundary_deg1_odd` /
  `SpernerTuckerDirectedRingOdd.dirCount_odd` seed.  Hence `0 = #bin < #bout`.

Feeding these to the (absent-generalised) flow engine yields `exists_source_room`: for
every antipodal labelling some triangle is a **source** — an out-degree-1, in-degree-0
room, the root of the directed Freund–Todd pivot path.

## Honest status

A genuine **positive** increment: the first machine-checked firing of the abstract
*directed flow* engine on real n = 2 disc geometry, closing the "instantiate the flow
engine and discharge `hdeg`/`hwf`" step every prior session flagged.  It complements
`SpernerTuckerHexagonDirectedEngine` (undirected door graph → interior simplex) and
`SpernerTuckerHexagonDirectedInteriorSeed` (path-following → interior degree-1 room) by
demonstrating that the *signed flow-conservation* law also fires here.

It does **not** yet close n ≥ 2 Tucker.  Two honest gaps, now sharply located:

1. **The source is not yet isolated in the interior.**  On the *coarse* hexagon every
   triangle borders the disc boundary — there is no interior room — so the abstract
   `exists_interior_source_of_balanced_boundary` (which needs a boundary predicate `bdry`
   with `#sources∂ = #sinks∂`) cannot be run here: its balance hypothesis `hbal` provably
   *fails* on the coarse disc precisely because `#sources − #sinks = #bout > 0`.  Firing
   the *interior* refinement requires a **finer triangulation** carrying genuine interior
   rooms — that is the concrete remaining geometric obligation this file pins down.
2. The general-dimension `bridge` still needs the odd seed from the `(n−1)` Tucker count,
   not the finite disc check `boundary_out_odd`.

Self-contained: imports Mathlib and the abstract flow engine
`SpernerTuckerDirectedIncidenceFlow`.  0 sorries, 0 `axiom` declarations.  The abstract
§1 lemmas are pure double counting (`propext` / `Classical.choice` / `Quot.sound` only);
the concrete §2 discharges are kernel `decide` over the finite `Fin 4⁴` labelling space
(no `native_decide`).
-/
import Mathlib
import Proofs.SpernerTuckerDirectedIncidenceFlow

namespace SpernerTuckerHexagonDirectedFlow

open Finset
open SpernerTuckerDirectedIncidenceFlow

/-! ## §1  Absent-door generalisation of the flow engine

The base engine's well-formedness hypothesis `hwf` demands every door be *interior*,
*boundary-out*, or *boundary-in*.  A concrete triangulation always has *closed* edges —
doors with neither a tail nor a head cell (`tailCount = headCount = 0`).  These
**absent** doors contribute `0` to every flow sum, so admitting them changes nothing in
the conservation law.  We reprove the two lemmas we need under the weaker hypothesis. -/

section Abstract

variable {Cell Door : Type*} [Fintype Cell] [Fintype Door]
variable (tail head : Cell → Door → Bool)

/-- A **absent door** has neither a tail nor a head cell — a closed edge carrying no
directed door. -/
def IsAbsentDoor (d : Door) : Prop := tailCount tail d = 0 ∧ headCount head d = 0

instance : DecidablePred (IsAbsentDoor tail head) := fun d => by
  unfold IsAbsentDoor; infer_instance

/-- **Boundary net flow, admitting absent doors.**  Interior and absent doors both
contribute `0` to the net door weight, so the net flow still equals
`#boundary-out − #boundary-in`. -/
theorem sum_net_eq_boundary_of_absent
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d ∨ IsAbsentDoor tail head d) :
    (∑ c, ((outCount tail c : ℤ) - inCount head c))
      = (univ.filter (IsBoundaryOut tail head)).card
        - (univ.filter (IsBoundaryIn tail head)).card := by
  rw [sum_net_eq_sum_net_door]
  have hterm : ∀ d ∈ (univ : Finset Door),
      ((tailCount tail d : ℤ) - headCount head d)
        = (if IsBoundaryOut tail head d then (1 : ℤ) else 0)
          - (if IsBoundaryIn tail head d then (1 : ℤ) else 0) := by
    intro d _
    rcases hwf d with ⟨ht, hh⟩ | ⟨ht, hh⟩ | ⟨ht, hh⟩ | ⟨ht, hh⟩ <;>
      simp [IsBoundaryOut, IsBoundaryIn, ht, hh]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.sum_boole]

/-- **Directed flow conservation, admitting absent doors.**
`#sources − #sinks = #boundary-out − #boundary-in`. -/
theorem sources_sub_sinks_eq_boundary_of_absent
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d ∨ IsAbsentDoor tail head d) :
    ((univ.filter (IsSource tail head)).card : ℤ)
        - (univ.filter (IsSink tail head)).card
      = (univ.filter (IsBoundaryOut tail head)).card
        - (univ.filter (IsBoundaryIn tail head)).card := by
  rw [← sum_net_eq_sources_sub_sinks tail head hdeg,
    sum_net_eq_boundary_of_absent tail head hwf]

/-- **An out-heavy boundary forces a source, admitting absent doors.**  The absent-door
version of `exists_source_of_more_boundary_out`: if the boundary carries strictly more
outgoing than incoming directed doors, some cell is a source. -/
theorem exists_source_of_more_boundary_out_of_absent
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d ∨ IsAbsentDoor tail head d)
    (himb : (univ.filter (IsBoundaryIn tail head)).card
      < (univ.filter (IsBoundaryOut tail head)).card) :
    ∃ c, IsSource tail head c := by
  have hmaster := sources_sub_sinks_eq_boundary_of_absent tail head hdeg hwf
  have hbpos : (0 : ℤ) < (univ.filter (IsBoundaryOut tail head)).card
      - (univ.filter (IsBoundaryIn tail head)).card :=
    sub_pos.mpr (by exact_mod_cast himb)
  rw [← hmaster] at hbpos
  have hlt : (univ.filter (IsSink tail head)).card
      < (univ.filter (IsSource tail head)).card := by
    exact_mod_cast sub_pos.mp hbpos
  have hpos : 0 < (univ.filter (IsSource tail head)).card :=
    lt_of_le_of_lt (Nat.zero_le _) hlt
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  exact ⟨c, (Finset.mem_filter.mp hc).2⟩

end Abstract

/-! ## §2  The concrete hexagon directed door complex

Labelling model identical to `SpernerTuckerHexagonDirectedInteriorSeed`: three free
labels `a, b, c` on `v₀, v₁, v₂`, antipodal `v_{i+3} = -vᵢ`, and a centre label `d`. -/

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The six boundary labels from three free labels `a,b,c`, antipodal `v_{i+3} = -vᵢ`. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- Sign map `sgn : Fin 4 → Bool`, `{+1,+2}↦false` (pos), `{-1,-2}↦true` (neg). -/
def sgn : Fin 4 → Bool := ![false, false, true, true]

/-- **Directed pos→neg door indicator** on an oriented sign edge `x → y`: open iff `x` is
in the positive hemisphere and `y` in the negative one. -/
def dopen (x y : Fin 4) : Bool := (! sgn x) && sgn y

/-- **Cells** are the six disc triangles `Tᵢ = (centre, vᵢ, v_{i+1})`. -/
abbrev Cell := Fin 6

/-- **Doors** are the six spokes `inl j = {centre, v_j}` and six boundary edges
`inr k = {v_k, v_{k+1}}`. -/
abbrev Dr := Fin 6 ⊕ Fin 6

/-- **Tail incidence.**  Triangle `i` is the *tail* (source end) of door `e` when `e` is
an open pos→neg door running *forward* along `T_i`'s counter-clockwise traversal:
* spoke `inl j`: forward in `T_j` if the spoke runs `centre → v_j` (`dopen d (V j)`), and
  forward in `T_{j-1}` if it runs `v_j → centre` (`dopen (V j) d`);
* boundary edge `inr k`: forward in `T_k` iff `v_k → v_{k+1}` is open (`dopen (V k) (V (k+1))`). -/
def tailB (a b c d : Fin 4) : Cell → Dr → Bool
  | i, Sum.inl j =>
      (dopen d (V a b c j) && decide (i = j))
        || (dopen (V a b c j) d && decide (i = j - 1))
  | i, Sum.inr k =>
      decide (k = i) && dopen (V a b c i) (V a b c (i + 1))

/-- **Head incidence.**  Triangle `i` is the *head* (target end) of door `e` when `e` is
an open pos→neg door running *backward* along `T_i`'s traversal — the dual of `tailB` on
the spokes.  A boundary edge exits through the disc boundary, so it has no head cell. -/
def headB (a b c d : Fin 4) : Cell → Dr → Bool
  | i, Sum.inl j =>
      (dopen d (V a b c j) && decide (i = j - 1))
        || (dopen (V a b c j) d && decide (i = j))
  | _, Sum.inr _ => false

/-! ### The four engine hypotheses, by kernel `decide` over all antipodal labellings -/

/-- **`hdeg`.**  Every triangle has out-degree and in-degree `≤ 1`: the Freund–Todd path
structure.  Out-degree `≤ 1` is `room_door_le_one`; in-degree `≤ 1` because the two
backward spokes force opposite centre hemispheres. -/
theorem hdeg (a b c d : Fin 4) :
    ∀ i : Cell, outCount (tailB a b c d) i ≤ 1 ∧ inCount (headB a b c d) i ≤ 1 := by
  revert a b c d; decide

/-- **`hwf` (absent-generalised).**  Every door is interior, boundary-out, boundary-in,
or absent: spokes are interior/absent, boundary edges are boundary-out/absent. -/
theorem hwf (a b c d : Fin 4) :
    ∀ e : Dr, IsInteriorDoor (tailB a b c d) (headB a b c d) e
      ∨ IsBoundaryOut (tailB a b c d) (headB a b c d) e
      ∨ IsBoundaryIn (tailB a b c d) (headB a b c d) e
      ∨ IsAbsentDoor (tailB a b c d) (headB a b c d) e := by
  revert a b c d; decide

/-- **No boundary-in doors.**  Every open boundary edge exits the disc; none enters, so
the boundary carries no incoming directed door. -/
theorem no_boundary_in (a b c d : Fin 4) :
    (univ.filter (IsBoundaryIn (tailB a b c d) (headB a b c d))).card = 0 := by
  revert a b c d; decide

/-- **The boundary-out count is odd** (values `{1,3}`) — the directed boundary-circle
seed (`dirCount_odd`), here as the flow engine's `#boundary-out`. -/
theorem boundary_out_odd (a b c d : Fin 4) :
    Odd (univ.filter (IsBoundaryOut (tailB a b c d) (headB a b c d))).card := by
  revert a b c d; decide

/-- **`himb`.**  The boundary is out-heavy: `#boundary-in = 0 < #boundary-out` (odd,
hence positive). -/
theorem himb (a b c d : Fin 4) :
    (univ.filter (IsBoundaryIn (tailB a b c d) (headB a b c d))).card
      < (univ.filter (IsBoundaryOut (tailB a b c d) (headB a b c d))).card := by
  rw [no_boundary_in]
  have h := boundary_out_odd a b c d
  rw [Nat.odd_iff] at h
  omega

/-! ### The flow engine fires: an odd boundary seed forces a source room -/

/-- **The abstract directed flow engine fires on the hexagon.**  For every antipodal
labelling `(a, b, c)` and centre label `d`, some triangle `Tᵢ` is a **source** — a room
of out-degree `1` and in-degree `0`, the root of the directed Freund–Todd pivot path.

This is `SpernerTuckerDirectedIncidenceFlow.exists_source_of_more_boundary_out` (absent-
generalised) instantiated on real n = 2 disc geometry: the odd directed boundary seed
(`boundary_out_odd`) drives the master flow-conservation law
`#sources − #sinks = #boundary-out − #boundary-in` to a positive source count. -/
theorem exists_source_room (a b c d : Fin 4) :
    ∃ i : Cell, IsSource (tailB a b c d) (headB a b c d) i :=
  exists_source_of_more_boundary_out_of_absent (tailB a b c d) (headB a b c d)
    (hdeg a b c d) (hwf a b c d) (himb a b c d)

/-- **Unpacking the source.**  The forced room `Tᵢ` has exactly one outgoing directed
door and no incoming one — a genuine directed path start on the disc. -/
theorem exists_source_room_spec (a b c d : Fin 4) :
    ∃ i : Cell, outCount (tailB a b c d) i = 1 ∧ inCount (headB a b c d) i = 0 :=
  exists_source_room a b c d

#check @sources_sub_sinks_eq_boundary_of_absent
#check @exists_source_of_more_boundary_out_of_absent
#check @exists_source_room

-- Axiom audit.  The abstract §1 lemmas and the final existence theorem use only the
-- foundational axioms (propext / Classical.choice / Quot.sound); the concrete §2
-- discharges are kernel `decide` (no `native_decide`, no `sorryAx`, no `Lean.ofReduceBool`).
#print axioms sum_net_eq_boundary_of_absent
#print axioms sources_sub_sinks_eq_boundary_of_absent
#print axioms exists_source_of_more_boundary_out_of_absent
#print axioms exists_source_room

end SpernerTuckerHexagonDirectedFlow
