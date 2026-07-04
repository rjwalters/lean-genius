/-
# The directed flow-conservation law: sources − sinks = boundary out − in (abstract door engine)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — the directed refinement the undirected engine cannot supply

The door-counting program has a clean *undirected* incidence engine in
`SpernerTuckerDoorIncidenceParity.lean`: for a bipartite incidence
`inc : Cell → Door → Bool`, double counting gives the parity law
`#{odd-door cells} ≡ #{boundary doors} (mod 2)`, and hence "an odd number of
boundary doors forces an odd-door cell".  But `SpernerTuckerBoundaryParity.lean`
proved the crux obstruction: on the antipodal boundary the *undirected*
complementary-door count is **always even**, so the odd seed the engine needs can
**never** come from an undirected boundary handshake.

The resolution — the essentially-unique edge-local closer singled out in the finite
classification and carried into Lean by `SpernerTuckerDirectedRingOdd.dirCount_odd`
— is to **orient** the doors: the pos→neg sign rule makes the directed boundary
count *odd* where the undirected one is even.  What has been missing is the
*abstract directed engine* that consumes such an oriented seed: the directed
analogue of `SpernerTuckerDoorIncidenceParity`, tracking each door's tail (source)
and head (target) cell separately and conserving the net flow.  This file supplies
it.

## The model

A **directed door complex** is two bipartite incidences
`tail head : Cell → Door → Bool`: `tail c d` means cell `c` is the source end of
door `d`, `head c d` that `c` is its target end.  Per cell,
`outCount c = #{d | tail c d}` (outgoing doors) and `inCount c = #{d | head c d}`
(incoming doors); per door, `tailCount d = #{c | tail c d}` and
`headCount d = #{c | head c d}` count its ends among the cells.

A **well-formed** door has exactly one tail *or* one head on each incidence side:
it is *interior* (`tailCount = headCount = 1`, joining a source cell to a target
cell), a *boundary-out* door (`tailCount = 1, headCount = 0`, a directed door
leaving a cell through the region boundary), or a *boundary-in* door
(`tailCount = 0, headCount = 1`, entering a cell from the boundary).

## What this file proves (unconditional double counting; 0 sorries, 0 axioms)

* `sum_outCount_eq_sum_tailCount` / `sum_inCount_eq_sum_headCount` — the two
  double-counting identities (`Finset.sum_comm`), exactly as in the undirected file.
* `sum_net_eq_sum_net_door` — the **net-flow identity** over `ℤ`, with *no*
  hypotheses: `∑_c (outCount c − inCount c) = ∑_d (tailCount d − headCount d)`.
* `sum_net_eq_boundary` — for a well-formed complex, the interior doors cancel
  (net `0`) and only boundary doors contribute:
  `∑_c (outCount c − inCount c) = #boundary-out − #boundary-in`.
* `sum_net_eq_sources_sub_sinks` — when every cell has out- and in-degree `≤ 1`
  (the Freund–Todd non-degeneracy: rooms lie on directed paths), the cell side
  collapses to sources and sinks: `∑_c (outCount c − inCount c) = #sources − #sinks`.
* `sources_sub_sinks_eq_boundary` — **the master directed flow-conservation law**:
  `#sources − #sinks = #boundary-out − #boundary-in`.  This is the exact integer
  identity the classical directed pivot conserves; its mod-2 shadow is the parity
  bridge of the undirected file, but the *signed* version is what an oriented (odd)
  boundary seed actually drives.
* `exists_source_of_more_boundary_out` — the existence corollary: a boundary with
  strictly more outgoing than incoming directed doors forces a **source** cell — a
  directed path start.  (With `#boundary-in = 0` and `#boundary-out` odd, hence
  positive, this is precisely the `dirCount_odd` seed producing a path root.)
* `card_source_eq_card_sink_of_interior` — the pure-interior directed handshake
  (`#sources = #sinks` when there are no boundary doors), the directed analogue of
  the undirected file's `even_card_odd_doorCount_of_all_interior`.

## Honest status

Abstract directed infrastructure, **not** a proof of n ≥ 2 Tucker.  It is the
oriented engine that `SpernerTuckerBoundaryParity` showed the undirected one cannot
be, and it turns an odd directed boundary seed (`SpernerTuckerDirectedRingOdd`) into
a source/path-root cell.  What it does **not** do is isolate that source in the
*interior*: `exists_source_of_more_boundary_out` produces a source among *all*
cells, and separating interior from boundary cells still needs the boundary-cell
accounting (the asymmetric Tucker labelling) — the open geometric frontier every
prior session named.  Value: the signed flow-conservation identity is now a
first-class, hypothesis-light lemma the eventual directed path-following can consume
directly, closing the conceptual gap between the odd *directed* boundary seed and
the *undirected*-only abstract engine.

Self-contained over arbitrary finite `Cell`, `Door` (imports Mathlib only).
0 sorries, 0 `axiom` declarations (`propext` / `Classical.choice` / `Quot.sound`
only — no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`).
-/
import Mathlib

namespace SpernerTuckerDirectedIncidenceFlow

open Finset

variable {Cell Door : Type*} [Fintype Cell] [Fintype Door]
variable (tail head : Cell → Door → Bool)

/-! ## Per-cell and per-door directed counts -/

/-- Outgoing doors of a cell: doors whose *source* (tail) end is this cell. -/
def outCount (c : Cell) : ℕ := (univ.filter (fun d => tail c d)).card

/-- Incoming doors of a cell: doors whose *target* (head) end is this cell. -/
def inCount (c : Cell) : ℕ := (univ.filter (fun d => head c d)).card

/-- Number of cells that are the tail (source) end of a door. -/
def tailCount (d : Door) : ℕ := (univ.filter (fun c => tail c d)).card

/-- Number of cells that are the head (target) end of a door. -/
def headCount (d : Door) : ℕ := (univ.filter (fun c => head c d)).card

/-! ## Double counting the directed incidences -/

/-- **Double counting the tails.**  Summing outgoing doors over cells and tail-counts
over doors count the same source incidences. -/
theorem sum_outCount_eq_sum_tailCount :
    (∑ c, outCount tail c) = ∑ d, tailCount tail d := by
  unfold outCount tailCount
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-- **Double counting the heads.**  Summing incoming doors over cells and head-counts
over doors count the same target incidences. -/
theorem sum_inCount_eq_sum_headCount :
    (∑ c, inCount head c) = ∑ d, headCount head d := by
  unfold inCount headCount
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-! ## The net-flow identity (no hypotheses) -/

/-- **Net-flow identity.**  The net directed flow summed over cells equals the net
directed weight summed over doors — an unconditional consequence of the two
double-counting identities, over `ℤ`. -/
theorem sum_net_eq_sum_net_door :
    (∑ c, ((outCount tail c : ℤ) - inCount head c))
      = ∑ d, ((tailCount tail d : ℤ) - headCount head d) := by
  have h1 : (∑ c, (outCount tail c : ℤ)) = ∑ d, (tailCount tail d : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, sum_outCount_eq_sum_tailCount]
  have h2 : (∑ c, (inCount head c : ℤ)) = ∑ d, (headCount head d : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, sum_inCount_eq_sum_headCount]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, h2]

/-! ## Well-formed doors: interior, boundary-out, boundary-in -/

/-- An **interior door** joins a source cell to a target cell: one tail, one head. -/
def IsInteriorDoor (d : Door) : Prop := tailCount tail d = 1 ∧ headCount head d = 1

/-- A **boundary-out door** leaves a cell through the region boundary: one tail, no
head. -/
def IsBoundaryOut (d : Door) : Prop := tailCount tail d = 1 ∧ headCount head d = 0

/-- A **boundary-in door** enters a cell from the region boundary: no tail, one
head. -/
def IsBoundaryIn (d : Door) : Prop := tailCount tail d = 0 ∧ headCount head d = 1

instance : DecidablePred (IsInteriorDoor tail head) := fun d => by
  unfold IsInteriorDoor; infer_instance
instance : DecidablePred (IsBoundaryOut tail head) := fun d => by
  unfold IsBoundaryOut; infer_instance
instance : DecidablePred (IsBoundaryIn tail head) := fun d => by
  unfold IsBoundaryIn; infer_instance

/-- **The boundary net flow.**  In a well-formed directed door complex the interior
doors cancel (net `0`) and the net flow equals the number of boundary-out doors
minus the boundary-in doors. -/
theorem sum_net_eq_boundary
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d) :
    (∑ c, ((outCount tail c : ℤ) - inCount head c))
      = (univ.filter (IsBoundaryOut tail head)).card
        - (univ.filter (IsBoundaryIn tail head)).card := by
  rw [sum_net_eq_sum_net_door]
  have hterm : ∀ d ∈ (univ : Finset Door),
      ((tailCount tail d : ℤ) - headCount head d)
        = (if IsBoundaryOut tail head d then (1 : ℤ) else 0)
          - (if IsBoundaryIn tail head d then (1 : ℤ) else 0) := by
    intro d _
    rcases hwf d with ⟨ht, hh⟩ | ⟨ht, hh⟩ | ⟨ht, hh⟩ <;>
      simp [IsBoundaryOut, IsBoundaryIn, ht, hh]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.sum_boole]

/-! ## Cells on directed paths: sources and sinks -/

/-- A **source** cell has an outgoing door but no incoming one — a directed path
start. -/
def IsSource (c : Cell) : Prop := outCount tail c = 1 ∧ inCount head c = 0

/-- A **sink** cell has an incoming door but no outgoing one — a directed path end. -/
def IsSink (c : Cell) : Prop := outCount tail c = 0 ∧ inCount head c = 1

instance : DecidablePred (IsSource tail head) := fun c => by
  unfold IsSource; infer_instance
instance : DecidablePred (IsSink tail head) := fun c => by
  unfold IsSink; infer_instance

/-- **The cell net flow.**  When every cell has out-degree and in-degree `≤ 1`
(rooms lie on directed paths), the net flow summed over cells equals the number of
sources minus the number of sinks. -/
theorem sum_net_eq_sources_sub_sinks
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1) :
    (∑ c, ((outCount tail c : ℤ) - inCount head c))
      = (univ.filter (IsSource tail head)).card
        - (univ.filter (IsSink tail head)).card := by
  have hterm : ∀ c ∈ (univ : Finset Cell),
      ((outCount tail c : ℤ) - inCount head c)
        = (if IsSource tail head c then (1 : ℤ) else 0)
          - (if IsSink tail head c then (1 : ℤ) else 0) := by
    intro c _
    have ho := (hdeg c).1
    have hi := (hdeg c).2
    interval_cases hoc : (outCount tail c) <;> interval_cases hic : (inCount head c) <;>
      simp [IsSource, IsSink, hoc, hic]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.sum_boole]

/-! ## The master flow-conservation law and its corollaries -/

/-- **Directed flow conservation.**  In a well-formed directed door complex whose
cells all have out- and in-degree `≤ 1`, the source/sink imbalance equals the boundary
door imbalance:

  `#sources − #sinks = #boundary-out − #boundary-in`.

This is the signed refinement of the undirected parity bridge
(`SpernerTuckerDoorIncidenceParity.card_odd_doorCount_modEq_card_boundaryDoor`): the
*directed* boundary seed (odd where the undirected one is even,
`SpernerTuckerDirectedRingOdd.dirCount_odd`) drives the interior path structure
through this identity, not merely its mod-2 shadow. -/
theorem sources_sub_sinks_eq_boundary
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d) :
    ((univ.filter (IsSource tail head)).card : ℤ)
        - (univ.filter (IsSink tail head)).card
      = (univ.filter (IsBoundaryOut tail head)).card
        - (univ.filter (IsBoundaryIn tail head)).card := by
  rw [← sum_net_eq_sources_sub_sinks tail head hdeg, sum_net_eq_boundary tail head hwf]

/-- **An out-heavy boundary forces a source.**  If the boundary carries strictly more
outgoing than incoming directed doors, then some cell is a source — a directed path
start.  In the Tucker instantiation `#boundary-in = 0` and `#boundary-out` is the odd
(hence positive) directed seed, so a path root is forced. -/
theorem exists_source_of_more_boundary_out
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d)
    (himb : (univ.filter (IsBoundaryIn tail head)).card
      < (univ.filter (IsBoundaryOut tail head)).card) :
    ∃ c, IsSource tail head c := by
  have hmaster := sources_sub_sinks_eq_boundary tail head hdeg hwf
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

/-- **The pure-interior directed handshake.**  With no boundary doors — every door
interior — the number of sources equals the number of sinks.  This is the directed
analogue of the undirected file's `even_card_odd_doorCount_of_all_interior`: a closed
directed door complex has balanced path ends. -/
theorem card_source_eq_card_sink_of_interior
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hint : ∀ d, IsInteriorDoor tail head d) :
    (univ.filter (IsSource tail head)).card
      = (univ.filter (IsSink tail head)).card := by
  have hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d := fun d => Or.inl (hint d)
  have hmaster := sources_sub_sinks_eq_boundary tail head hdeg hwf
  have hbo : (univ.filter (IsBoundaryOut tail head)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _ hb
    obtain ⟨_, h1⟩ := hint d
    obtain ⟨_, h2⟩ := hb
    omega
  have hbi : (univ.filter (IsBoundaryIn tail head)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _ hb
    obtain ⟨_, h1⟩ := hint d
    obtain ⟨h2, _⟩ := hb
    omega
  rw [hbo, hbi] at hmaster
  have : ((univ.filter (IsSource tail head)).card : ℤ)
      = (univ.filter (IsSink tail head)).card := by linarith [hmaster]
  exact_mod_cast this

#check @sum_net_eq_sum_net_door
#check @sum_net_eq_boundary
#check @sources_sub_sinks_eq_boundary
#check @exists_source_of_more_boundary_out
#check @card_source_eq_card_sink_of_interior

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms sum_net_eq_sum_net_door
#print axioms sum_net_eq_boundary
#print axioms sum_net_eq_sources_sub_sinks
#print axioms sources_sub_sinks_eq_boundary
#print axioms exists_source_of_more_boundary_out
#print axioms card_source_eq_card_sink_of_interior

end SpernerTuckerDirectedIncidenceFlow
