/-
# The generalized handshake bridge: boundary doors force an odd-door cell (n ≥ 2 Tucker)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

The door-counting program for Sperner/Tucker/Scarf is driven by a single parity
principle.  The companion files isolate its *graph* form:

* `SpernerDoorCountingParity.lean` / `SpernerTuckerPathFollowing.lean` — the
  handshaking lemma `even_card_odd_degree_vertices`: in any finite simple graph the
  number of odd-degree vertices is even, specialised to degree-≤2 "path/cycle" door
  graphs where door-terminals are the degree-1 path endpoints.
* `SpernerTuckerInteriorParity.lean` — given an **odd** number of *boundary*
  endpoints, the **interior** endpoints (the complementary simplices) are odd too.

All of those start from a `SimpleGraph`, i.e. they presuppose every "door" joins
**exactly two** cells.  The geometric door structure of Tucker is *not* like that:
a complementary facet on the **boundary** of the region belongs to **one** cell,
while an interior facet belongs to **two**.  `SpernerTuckerBoundaryParity.lean`
records the consequence of ignoring this — the raw boundary ring's complementary
count is *always even*, so the odd parity the engine needs cannot come from a plain
graph handshake; it must come from the **boundary doors** themselves.

## What this file proves (the missing bridge)

This file states and verifies the door-counting principle **at the incidence
level**, before any graph is built, where doors are allowed to touch one *or* two
cells.  Model an abstract **door complex** as a bipartite incidence
`inc : Cell → Door → Bool`.  Write

* `doorCount c` = number of doors incident to cell `c`,
* `cellCount d` = number of cells incident to door `d`.

Double counting the incident pairs two ways gives `∑ doorCount = ∑ cellCount`, and
reducing mod 2 yields the **incidence-duality parity law**

  `#{cells with odd door-count}  ≡  #{doors with odd cell-count}   (mod 2)`,

with *no hypotheses whatsoever* (`incidence_parity_duality`).  This is the genuine
generalisation of the handshaking lemma: when every door touches exactly two cells
the right-hand side is empty and one recovers "the number of odd-degree vertices is
even".

Specialising to the geometric regime — every door touches **at most two** cells —
an odd cell-count means *exactly one* cell, i.e. a **boundary door**.  So

  `#{cells with odd door-count}  ≡  #{boundary doors}   (mod 2)`

(`card_odd_doorCount_modEq_card_boundaryDoor`), and therefore an **odd** number of
boundary doors forces a cell with an **odd** number of doors
(`exists_odd_doorCount_of_odd_boundary`).  In the Freund–Todd / Prescott–Su
instantiation the boundary doors are the antipodally-paired boundary facets (whose
odd count is the inductive `(n−1)`-Tucker input) and the odd-door cells are exactly
the degree-1 path endpoints fed to `SpernerTuckerPathFollowing`.  This file is the
clean combinatorial converter between the two — the step the graph-level files
assumed rather than proved.

Self-contained over arbitrary finite `Cell`, `Door`.  0 sorries, 0 axioms.
-/
import Mathlib

namespace SpernerTuckerDoorIncidenceParity

open Finset

variable {Cell Door : Type*} [Fintype Cell] [Fintype Door]
variable (inc : Cell → Door → Bool)

/-- Number of doors incident to a cell. -/
def doorCount (c : Cell) : ℕ := (univ.filter (fun d => inc c d)).card

/-- Number of cells incident to a door. -/
def cellCount (d : Door) : ℕ := (univ.filter (fun c => inc c d)).card

/-- A **boundary door** of the complex is one incident to exactly one cell;
geometrically a facet on the boundary of the region. -/
def IsBoundaryDoor (d : Door) : Prop := cellCount inc d = 1

instance : DecidablePred (IsBoundaryDoor inc) := fun d => by
  unfold IsBoundaryDoor; infer_instance

/-! ## A reusable parity helper

For any `ℕ`-valued statistic on a finite type, the sum is congruent mod 2 to the
number of indices on which the statistic is odd. -/

/-- `(∑ i, a i)` and `#{i | Odd (a i)}` have the same parity. -/
theorem card_odd_mod_two {ι : Type*} [Fintype ι] (a : ι → ℕ) :
    (univ.filter (fun i => Odd (a i))).card % 2 = (∑ i, a i) % 2 := by
  rw [Finset.sum_nat_mod, Finset.card_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases Nat.even_or_odd (a i) with h | h
  · rw [if_neg (by simpa [Nat.not_odd_iff_even] using h), Nat.even_iff.mp h]
  · rw [if_pos h, Nat.odd_iff.mp h]

/-! ## Double counting the incident pairs -/

/-- **Double counting.** Summing the door-counts over cells and the cell-counts over
doors count the same set of incident `(cell, door)` pairs, hence are equal. -/
theorem sum_doorCount_eq_sum_cellCount :
    (∑ c, doorCount inc c) = ∑ d, cellCount inc d := by
  unfold doorCount cellCount
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-! ## The incidence-duality parity law (no hypotheses) -/

/-- **Generalized handshaking lemma / incidence-duality parity law.**  For an
arbitrary bipartite incidence `inc : Cell → Door → Bool`, the number of cells whose
door-count is odd is congruent mod 2 to the number of doors whose cell-count is odd.

When every door is incident to exactly two cells (a graph), the right-hand side is
empty and this is exactly `SimpleGraph.even_card_odd_degree_vertices`. -/
theorem incidence_parity_duality :
    (univ.filter (fun c => Odd (doorCount inc c))).card % 2
      = (univ.filter (fun d => Odd (cellCount inc d))).card % 2 := by
  rw [card_odd_mod_two, card_odd_mod_two, sum_doorCount_eq_sum_cellCount]

/-! ## Geometric specialization: doors touch at most two cells -/

omit [Fintype Door] in
/-- When a door touches at most two cells, "odd cell-count" means *exactly one*
cell, i.e. the door is a boundary door. -/
theorem odd_cellCount_iff_boundary {d : Door} (h : cellCount inc d ≤ 2) :
    Odd (cellCount inc d) ↔ IsBoundaryDoor inc d := by
  unfold IsBoundaryDoor
  rw [Nat.odd_iff]
  omega

/-- **The boundary-door parity bridge.**  In a door complex where every door is
incident to at most two cells, the number of cells with an odd door-count is
congruent mod 2 to the number of boundary doors.

This converts the antipodal boundary condition (an *odd* number of boundary doors,
supplied by the inductive `(n−1)`-Tucker statement) into an *odd* number of cells
that are path endpoints, the input to the path-following engine. -/
theorem card_odd_doorCount_modEq_card_boundaryDoor
    (h2 : ∀ d, cellCount inc d ≤ 2) :
    (univ.filter (fun c => Odd (doorCount inc c))).card % 2
      = (univ.filter (IsBoundaryDoor inc)).card % 2 := by
  rw [incidence_parity_duality]
  have hfilt : (univ.filter (fun d => Odd (cellCount inc d)))
      = univ.filter (IsBoundaryDoor inc) :=
    Finset.filter_congr (fun d _ => odd_cellCount_iff_boundary inc (h2 d))
  rw [hfilt]

/-- **Odd boundary doors force an odd-door cell.**  If a door complex with doors of
incidence ≤ 2 has an *odd* number of boundary doors, then some cell has an *odd*
number of doors.  Geometrically: the antipodal boundary condition forces a
path-endpoint cell — the seed from which path-following reaches a complementary
simplex. -/
theorem exists_odd_doorCount_of_odd_boundary
    (h2 : ∀ d, cellCount inc d ≤ 2)
    (hbdry : Odd (univ.filter (IsBoundaryDoor inc)).card) :
    ∃ c, Odd (doorCount inc c) := by
  have hmod := card_odd_doorCount_modEq_card_boundaryDoor inc h2
  rw [Nat.odd_iff] at hbdry
  rw [hbdry] at hmod
  have hpos : 0 < (univ.filter (fun c => Odd (doorCount inc c))).card := by
    rcases Nat.eq_zero_or_pos (univ.filter (fun c => Odd (doorCount inc c))).card with h0 | hp
    · rw [h0] at hmod; simp at hmod
    · exact hp
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hc
  exact ⟨c, hc.2⟩

/-! ## Parity-refined form

For direct use alongside `SpernerTuckerInteriorParity`, the boundary-door count and
the odd-door-cell count have the *same* parity. -/

/-- The number of boundary doors and the number of odd-door cells have the same
parity. -/
theorem odd_boundary_iff_odd_doorCount_cell
    (h2 : ∀ d, cellCount inc d ≤ 2) :
    Odd (univ.filter (IsBoundaryDoor inc)).card
      ↔ Odd (univ.filter (fun c => Odd (doorCount inc c))).card := by
  have hmod := card_odd_doorCount_modEq_card_boundaryDoor inc h2
  rw [Nat.odd_iff, Nat.odd_iff, hmod]

/-! ## Sanity check: the pure-graph case recovers the handshaking lemma

If every door is incident to *exactly* two cells there are no boundary doors, so the
duality law degenerates to "the number of odd-door-count cells is even". -/

/-- With every door incident to exactly two cells, the number of cells of odd
door-count is even — the handshaking lemma recovered from the incidence law. -/
theorem even_card_odd_doorCount_of_all_interior
    (h2 : ∀ d, cellCount inc d = 2) :
    Even (univ.filter (fun c => Odd (doorCount inc c))).card := by
  have hbdry : (univ.filter (IsBoundaryDoor inc)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _
    unfold IsBoundaryDoor
    rw [h2 d]; decide
  have hmod := card_odd_doorCount_modEq_card_boundaryDoor inc (fun d => by rw [h2 d])
  rw [hbdry] at hmod
  rw [Nat.even_iff, hmod]

#check @incidence_parity_duality
#check @card_odd_doorCount_modEq_card_boundaryDoor
#check @exists_odd_doorCount_of_odd_boundary
#check @even_card_odd_doorCount_of_all_interior

-- Axiom audit: the results depend only on the foundational axioms
-- (propext / Classical.choice / Quot.sound); no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms incidence_parity_duality
#print axioms card_odd_doorCount_modEq_card_boundaryDoor
#print axioms exists_odd_doorCount_of_odd_boundary
#print axioms even_card_odd_doorCount_of_all_interior

end SpernerTuckerDoorIncidenceParity
