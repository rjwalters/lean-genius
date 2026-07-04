/-
# The triforce subdivision: the directed flow engine fires, but the odd seed lands on the boundary

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — the FIRST disc with a genuine interior cell, and the correction it forces

`SpernerTuckerHexagonDirectedFlow.lean` (iteration 23) fired the abstract *directed flow*
engine (`SpernerTuckerDirectedIncidenceFlow`) on the coarse hexagon+centre disc: for every
antipodal labelling the master flow-conservation law
`#sources − #sinks = #boundary-out − #boundary-in` produces a **source room**.  Its honest
gap, recorded verbatim in the handoff, was that the forced source lands among *all* cells; the
classical Tucker argument wants it isolated in the **interior**, via the abstract
`SpernerTuckerDirectedInteriorSource.exists_interior_source_of_balanced_boundary`, which needs
a boundary predicate `bdry` and the **balance hypothesis** `hbal : #sources∂ = #sinks∂`.  On
the coarse hexagon that is unrunnable for a trivial reason: *every* triangle borders the disc
boundary, so there is no interior room at all.  The handoff's proposed fix was:

> a finer disc triangulation that carries genuine interior triangles; only then is `bdry`
> non-trivial and the interior-source engine runnable.

**This file builds the smallest such disc and shows the proposed fix is not enough** — a
sharp, machine-checked correction of the frontier.

## The construction — the "triforce" (edge-midpoint) subdivision of a triangle

Subdivide one triangle by its three edge midpoints.  Six vertices, on the boundary
`∂B²` in cyclic order `p₀ … p₅` — corners `p₀ = a, p₂ = b, p₄ = c` and midpoints
`p₁ = m_{ab}, p₃ = m_{bc}, p₅ = m_{ca}` — labelled antipodally `p_{i+3} = -p_i`
(three free labels `a, b, c` on `p₀, p₁, p₂`, so `Fin 4³ = 64` labellings; note there is **no**
interior vertex, unlike the hexagon's free centre `d`).  Four triangles:

* three **corner** cells `T₀ = (p₀,p₁,p₅)`, `T₁ = (p₂,p₃,p₁)`, `T₂ = (p₄,p₅,p₃)`,
  each carrying two boundary edges;
* one **centre** cell `T₃ = (p₁,p₃,p₅)` — the midpoint triangle, whose three edges are all
  interior chords.  `T₃` is a **genuine interior cell**: `bdry T₃` is false.

Doors: three interior chords `{p₁,p₅}, {p₁,p₃}, {p₃,p₅}` (each shared by `T₃` and one corner,
traversed in opposite directions) and six boundary edges (each in one corner, oriented by the
CCW boundary walk).  The directed door rule is identical to the hexagon: a door is *open* iff it
is a pos→neg sign door in its physical orientation; an open interior chord is one corner's
forward exit (`tail`) and `T₃`'s backward entry (`head`) or vice versa; an open boundary edge is
its corner's forward exit (`tail`) through the disc boundary (no head).

## What this file proves (all concrete facts by kernel `decide`; 0 sorries, 0 axioms)

* `hdeg`, `hwf`, `no_boundary_in`, `boundary_out_odd`, `himb` — the four flow-engine hypotheses
  hold, exactly as on the hexagon: every room has out/in-degree ≤ 1, every door is
  interior/boundary-out/boundary-in/absent, `#boundary-in = 0`, and `#boundary-out` is **odd**
  (the `dirCount_odd` seed).
* `exists_source_room` — **the flow engine fires on the triforce**: for every antipodal
  labelling some room is a source (out-degree 1, in-degree 0).  This is the second concrete
  firing of the directed flow engine, now on a disc that *does* carry an interior cell.
* **The correction (the point of the file).**  Despite the genuine interior cell, the
  interior-source engine still cannot fire, because its balance hypothesis `hbal` **provably
  fails**:
  * `interior_cell_never_source` — the interior room `T₃` is *never* a source (for any
    labelling);
  * `interior_cell_through_or_isolated` — in fact `outCount T₃ = inCount T₃` always (`T₃` is a
    directed *through* cell `(1,1)` or *isolated* `(0,0)`, never a path end);
  * `boundary_not_flow_balanced` — the boundary rooms are source-heavy,
    `#{sources∩bdry} ≠ #{sinks∩bdry}` for every labelling, so
    `exists_interior_source_of_balanced_boundary`'s hypothesis `hbal` is false here.

  The mechanism is exactly the master law: with `T₃` never a path end, the *entire* odd seed
  `#sources − #sinks = #boundary-out > 0` is carried by the **boundary** rooms.  Merely adding
  an interior cell does not route flow into it; the interior engine needs boundary rooms that are
  directed *through* cells forwarding the seed inward — which the symmetric triforce labelling
  never produces.  This corrects the "just subdivide" handoff with a decidable obstruction.

* `tucker_triforce` — as a positive by-product, the **actual Tucker conclusion** still holds
  on this disc: for every antipodal labelling some edge is *complementary* (`λ(v) = -λ(u)`).
  This is a second concrete n = 2 Tucker instance, on the edge-midpoint subdivision — orthogonal
  to `SpernerTuckerHexagonComplementaryEdge.tucker_hexagon` (hexagon + free centre vertex).

## Honest status

A genuine increment: the first disc in the program with a real interior room, a second firing of
the directed flow engine, a machine-checked Tucker complementary edge on a new triangulation
*and* — the substantive part — a decidable proof that the interior-source engine's balance
hypothesis fails on it, refuting the conjectured "finer triangulation ⇒ interior engine fires"
next step.  The sharpened frontier: the interior engine needs the *asymmetric* labelling whose
boundary rooms are through-cells (the Freund–Todd pivot entering the interior), not merely a disc
that has interior rooms.  It does **not** prove n ≥ 2 Tucker in general.

Self-contained: imports Mathlib and the abstract flow engine
`SpernerTuckerDirectedIncidenceFlow`.  0 sorries, 0 `axiom` declarations.  The abstract §0
lemmas are pure double counting (`propext` / `Classical.choice` / `Quot.sound` only); the
concrete §1–§2 discharges are kernel `decide` over `Fin 4³` (no `native_decide`).
-/
import Mathlib
import Proofs.SpernerTuckerDirectedIncidenceFlow

namespace SpernerTuckerTriforceDirectedFlow

open Finset
open SpernerTuckerDirectedIncidenceFlow

/-! ## §0  Absent-door generalisation of the flow engine

The base engine's `hwf` demands every door be interior/boundary-out/boundary-in.  A concrete
triangulation always has *closed* edges — doors with neither tail nor head
(`tailCount = headCount = 0`).  These **absent** doors contribute `0` to every flow sum, so
admitting them changes nothing.  We reprove the two lemmas we need under the weaker hypothesis
(identical to `SpernerTuckerHexagonDirectedFlow` §1). -/

section Abstract

variable {Cell Door : Type*} [Fintype Cell] [Fintype Door]
variable (tail head : Cell → Door → Bool)

/-- An **absent door** has neither a tail nor a head cell — a closed edge carrying no directed
door. -/
def IsAbsentDoor (d : Door) : Prop := tailCount tail d = 0 ∧ headCount head d = 0

instance : DecidablePred (IsAbsentDoor tail head) := fun d => by
  unfold IsAbsentDoor; infer_instance

/-- **Boundary net flow, admitting absent doors.** -/
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

/-- **Directed flow conservation, admitting absent doors.** -/
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

/-- **An out-heavy boundary forces a source, admitting absent doors.** -/
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

/-! ## §1  The concrete triforce directed door complex -/

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The six boundary labels from three free labels `a,b,c`, antipodal `p_{i+3} = -p_i`. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- Sign map `sgn : Fin 4 → Bool`, `{+1,+2}↦false` (pos), `{-1,-2}↦true` (neg). -/
def sgn : Fin 4 → Bool := ![false, false, true, true]

/-- **Directed pos→neg door indicator** on an oriented sign edge `x → y`. -/
def dopen (x y : Fin 4) : Bool := (! sgn x) && sgn y

/-- **Cells**: the four triangles `T₀,T₁,T₂` (corners) and `T₃` (centre/midpoint triangle). -/
abbrev Cell := Fin 4

/-- **Doors**: `inl j` the three interior chords, `inr k` the six boundary edges. -/
abbrev Dr := Fin 3 ⊕ Fin 6

/-- Corner cell owning interior chord `j` (the non-centre cell on the chord). -/
def ic : Fin 3 → Cell := ![0, 1, 2]
/-- Tail vertex of interior chord `j`, as its owning corner traverses it (`iu → iv`). -/
def iu : Fin 3 → Fin 6 := ![1, 3, 5]
/-- Head vertex of interior chord `j`, as its owning corner traverses it. -/
def iv : Fin 3 → Fin 6 := ![5, 1, 3]

/-- Corner cell owning boundary edge `k`. -/
def bc : Fin 6 → Cell := ![0, 0, 1, 1, 2, 2]
/-- Tail vertex of boundary edge `k` in the CCW boundary-walk orientation (`bu → bv`). -/
def bu : Fin 6 → Fin 6 := ![0, 5, 2, 1, 4, 3]
/-- Head vertex of boundary edge `k` in the CCW boundary-walk orientation. -/
def bv : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

/-- **Tail incidence.**  For an interior chord `inl j`: the owning corner `ic j` is the tail when
the chord is open in its forward traversal (`iu j → iv j`), and the centre cell `T₃` is the tail
when it is open in the reverse; for a boundary edge `inr k`: the owning corner `bc k` is the tail
when the edge is open in the CCW-walk direction (`bu k → bv k`). -/
def tailB (a b c : Fin 4) : Cell → Dr → Bool
  | i, Sum.inl j =>
      (dopen (V a b c (iu j)) (V a b c (iv j)) && decide (i = ic j))
        || (dopen (V a b c (iv j)) (V a b c (iu j)) && decide (i = 3))
  | i, Sum.inr k =>
      decide (i = bc k) && dopen (V a b c (bu k)) (V a b c (bv k))

/-- **Head incidence.**  The dual of `tailB` on interior chords (centre and corner swap roles);
a boundary edge exits through the disc boundary, so it has no head cell. -/
def headB (a b c : Fin 4) : Cell → Dr → Bool
  | i, Sum.inl j =>
      (dopen (V a b c (iu j)) (V a b c (iv j)) && decide (i = 3))
        || (dopen (V a b c (iv j)) (V a b c (iu j)) && decide (i = ic j))
  | _, Sum.inr _ => false

/-- The **boundary predicate**: a cell touches the disc boundary iff it is not the centre `T₃`. -/
def bdry : Cell → Prop := fun c => c ≠ 3

instance : DecidablePred bdry := fun c => by unfold bdry; infer_instance

/-! ### The four engine hypotheses, by kernel `decide` over all antipodal labellings -/

/-- **`hdeg`.**  Every room has out-degree and in-degree ≤ 1 — the Freund–Todd path structure. -/
theorem hdeg (a b c : Fin 4) :
    ∀ i : Cell, outCount (tailB a b c) i ≤ 1 ∧ inCount (headB a b c) i ≤ 1 := by
  revert a b c; decide

/-- **`hwf` (absent-generalised).**  Every door is interior, boundary-out, boundary-in, or
absent. -/
theorem hwf (a b c : Fin 4) :
    ∀ e : Dr, IsInteriorDoor (tailB a b c) (headB a b c) e
      ∨ IsBoundaryOut (tailB a b c) (headB a b c) e
      ∨ IsBoundaryIn (tailB a b c) (headB a b c) e
      ∨ IsAbsentDoor (tailB a b c) (headB a b c) e := by
  revert a b c; decide

/-- **No boundary-in doors.**  Every open boundary edge exits the disc; none enters. -/
theorem no_boundary_in (a b c : Fin 4) :
    (univ.filter (IsBoundaryIn (tailB a b c) (headB a b c))).card = 0 := by
  revert a b c; decide

/-- **The boundary-out count is odd** (values `{1,3}`) — the directed boundary-circle seed. -/
theorem boundary_out_odd (a b c : Fin 4) :
    Odd (univ.filter (IsBoundaryOut (tailB a b c) (headB a b c))).card := by
  revert a b c; decide

/-- **`himb`.**  The boundary is out-heavy: `#boundary-in = 0 < #boundary-out`. -/
theorem himb (a b c : Fin 4) :
    (univ.filter (IsBoundaryIn (tailB a b c) (headB a b c))).card
      < (univ.filter (IsBoundaryOut (tailB a b c) (headB a b c))).card := by
  rw [no_boundary_in]
  have h := boundary_out_odd a b c
  rw [Nat.odd_iff] at h
  omega

/-! ### The flow engine fires: an odd boundary seed forces a source room -/

/-- **The abstract directed flow engine fires on the triforce.**  For every antipodal labelling
`(a,b,c)` some room is a **source** — out-degree 1, in-degree 0 — the root of the directed
Freund–Todd pivot path.  Second concrete firing of the flow engine, now on a disc with a genuine
interior cell. -/
theorem exists_source_room (a b c : Fin 4) :
    ∃ i : Cell, IsSource (tailB a b c) (headB a b c) i :=
  exists_source_of_more_boundary_out_of_absent (tailB a b c) (headB a b c)
    (hdeg a b c) (hwf a b c) (himb a b c)

/-! ## §2  The correction: the interior-source engine's balance hypothesis fails

Every prior handoff conjectured that a finer disc carrying interior rooms would let the abstract
`SpernerTuckerDirectedInteriorSource.exists_interior_source_of_balanced_boundary` fire.  The
following decidable facts refute that for the smallest such disc: the interior room `T₃` is never
a path end, so the whole odd seed is carried by the boundary and the balance hypothesis `hbal`
fails. -/

/-- **The interior room is never a source.**  For every labelling the centre cell `T₃` is not a
source: the odd boundary seed never produces its path root in the interior. -/
theorem interior_cell_never_source (a b c : Fin 4) :
    ¬ IsSource (tailB a b c) (headB a b c) (3 : Cell) := by
  revert a b c; decide

/-- **The interior room is a through/isolated cell.**  `outCount T₃ = inCount T₃` always (value
`(1,1)` or `(0,0)`): the centre is never a directed path *end*, so it absorbs none of the seed. -/
theorem interior_cell_through_or_isolated (a b c : Fin 4) :
    outCount (tailB a b c) (3 : Cell) = inCount (headB a b c) (3 : Cell) := by
  revert a b c; decide

/-- **The boundary rooms are not flow-balanced.**  For every antipodal labelling
`#{sources ∩ bdry} ≠ #{sinks ∩ bdry}`, so the balance hypothesis `hbal` of
`exists_interior_source_of_balanced_boundary` is false on the triforce — the interior-source
engine cannot be run here even though a genuine interior room exists. -/
theorem boundary_not_flow_balanced (a b c : Fin 4) :
    (univ.filter (fun i => IsSource (tailB a b c) (headB a b c) i ∧ bdry i)).card
      ≠ (univ.filter (fun i => IsSink (tailB a b c) (headB a b c) i ∧ bdry i)).card := by
  revert a b c; decide

/-! ## §3  Positive by-product: the actual Tucker complementary edge -/

/-- Endpoints of a door as a vertex pair. -/
def endpts : Dr → Fin 6 × Fin 6
  | Sum.inl j => (iu j, iv j)
  | Sum.inr k => (bu k, bv k)

/-- A door is **complementary** when its two endpoint labels are antipodal (`λ v = -λ u`). -/
def IsComplEdge (a b c : Fin 4) (e : Dr) : Prop :=
  V a b c (endpts e).2 = negL (V a b c (endpts e).1)

instance (a b c : Fin 4) : DecidablePred (IsComplEdge a b c) := fun e => by
  unfold IsComplEdge; infer_instance

/-- **Tucker's lemma on the triforce disc.**  For every one of the `4³ = 64` antipodal
labellings some edge is complementary — the actual Tucker conclusion (the object Borsuk–Ulam
consumes), on the edge-midpoint subdivision.  Complementary to
`SpernerTuckerHexagonComplementaryEdge.tucker_hexagon` (hexagon + free centre). -/
theorem tucker_triforce (a b c : Fin 4) : ∃ e : Dr, IsComplEdge a b c e := by
  revert a b c; decide

#check @exists_source_room
#check @interior_cell_never_source
#check @boundary_not_flow_balanced
#check @tucker_triforce

-- Axiom audit.  The abstract §0 lemmas and the final existence theorem use only the foundational
-- axioms (propext / Classical.choice / Quot.sound); the concrete §1–§3 discharges are kernel
-- `decide` (no `native_decide`, no `sorryAx`, no `Lean.ofReduceBool`).
#print axioms sources_sub_sinks_eq_boundary_of_absent
#print axioms exists_source_room
#print axioms interior_cell_never_source
#print axioms interior_cell_through_or_isolated
#print axioms boundary_not_flow_balanced
#print axioms tucker_triforce

end SpernerTuckerTriforceDirectedFlow
