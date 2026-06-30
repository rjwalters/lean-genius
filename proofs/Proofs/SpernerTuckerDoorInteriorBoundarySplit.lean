/-
# Interior/boundary split of the door count: reconciling the two parity engines (n ≥ 2 Tucker)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

The door-counting program for Sperner/Tucker runs two parity engines over the same
abstract incidence `inc : Cell → Door → Bool`:

* the **graph** engine (`SpernerTuckerDoorGraph.lean`) builds a `SimpleGraph` whose
  edges are the *interior* doors (each joining exactly two cells) and concludes via
  the handshaking lemma — its path endpoints are the cells of **odd interior
  degree**;
* the **incidence** engine (`SpernerTuckerDoorIncidenceParity.lean`) works before any
  graph and concludes via the incidence-duality law — its path-endpoint seeds are the
  cells of **odd total door-count** (`exists_odd_doorCount_of_odd_boundary`).

Those two notions of "path endpoint" differ by exactly the **boundary** doors: the
total door-count of a cell is its interior (graph-degree) count *plus* its
boundary-door count.  This file proves that split and reads off the parity
relationship, so the seeds produced by the incidence engine and the endpoints
consumed by the graph engine are connected by one clean equation rather than left
implicitly identified.

## What this file proves

Over arbitrary finite `Cell`, `Door` with the geometric hypothesis that every door
touches at most two cells (`h2 : ∀ d, cellCount inc d ≤ 2`):

* `doorCount_eq_interior_add_boundary` — `doorCount c = interiorDoorCount c +
  boundaryDoorCount c`: an incident door is interior (two cells) or boundary (one
  cell), nothing else, so the count splits exactly.
* `odd_doorCount_iff_xor` — a cell has odd total door-count **iff** its interior
  parity and boundary parity disagree (`Odd interior ↔ Even boundary`).  When a cell
  touches no boundary door this collapses to "odd total ⇔ odd interior degree"
  (`odd_doorCount_iff_odd_interior_of_no_boundary`), identifying the incidence-engine
  seed with the graph-engine endpoint.

Self-contained over arbitrary finite `Cell`, `Door`.  0 sorries, 0 axioms.
-/
import Mathlib

namespace SpernerTuckerDoorInteriorBoundarySplit

open Finset

variable {Cell Door : Type*} [Fintype Cell] [Fintype Door]
variable (inc : Cell → Door → Bool)

/-- Number of doors incident to a cell. -/
def doorCount (c : Cell) : ℕ := (univ.filter (fun d => inc c d)).card

/-- Number of cells incident to a door. -/
def cellCount (d : Door) : ℕ := (univ.filter (fun c => inc c d)).card

/-- A **boundary door** is incident to exactly one cell. -/
def IsBoundaryDoor (d : Door) : Prop := cellCount inc d = 1

/-- An **interior door** is incident to exactly two cells (a graph edge). -/
def IsInteriorDoor (d : Door) : Prop := cellCount inc d = 2

instance : DecidablePred (IsBoundaryDoor inc) := fun d => by
  unfold IsBoundaryDoor; infer_instance
instance : DecidablePred (IsInteriorDoor inc) := fun d => by
  unfold IsInteriorDoor; infer_instance

/-- Interior doors incident to a cell — the graph-degree contribution used by
`SpernerTuckerDoorGraph`. -/
def interiorDoorCount (c : Cell) : ℕ :=
  (univ.filter (fun d => inc c d ∧ IsInteriorDoor inc d)).card

/-- Boundary doors incident to a cell. -/
def boundaryDoorCount (c : Cell) : ℕ :=
  (univ.filter (fun d => inc c d ∧ IsBoundaryDoor inc d)).card

omit [Fintype Door] in
/-- A door incident to a cell touches at least that cell, so its cell-count is ≥ 1. -/
theorem one_le_cellCount_of_inc {c : Cell} {d : Door} (h : inc c d) :
    1 ≤ cellCount inc d := by
  unfold cellCount
  apply Finset.card_pos.mpr
  exact ⟨c, by simp [h]⟩

omit [Fintype Door] in
/-- Under the ≤2 hypothesis, an incident door is boundary exactly when it is not
interior. -/
theorem inc_boundary_iff_not_interior (h2 : ∀ d, cellCount inc d ≤ 2) (c : Cell)
    (d : Door) :
    (inc c d ∧ IsBoundaryDoor inc d) ↔ (inc c d ∧ ¬ IsInteriorDoor inc d) := by
  by_cases hinc : inc c d
  · have h1 : 1 ≤ cellCount inc d := one_le_cellCount_of_inc inc hinc
    have hle : cellCount inc d ≤ 2 := h2 d
    simp only [hinc, true_and, IsBoundaryDoor, IsInteriorDoor]
    omega
  · simp [hinc]

/-- **Interior/boundary split of the door count.**  When every door touches at most
two cells, every door incident to a cell is either interior (touches two cells) or
boundary (touches one), so the total door-count of a cell splits exactly into its
interior and boundary parts. -/
theorem doorCount_eq_interior_add_boundary (h2 : ∀ d, cellCount inc d ≤ 2)
    (c : Cell) :
    doorCount inc c = interiorDoorCount inc c + boundaryDoorCount inc c := by
  have hbdry : boundaryDoorCount inc c
      = (univ.filter (fun d => inc c d ∧ ¬ IsInteriorDoor inc d)).card := by
    unfold boundaryDoorCount
    congr 1
    exact Finset.filter_congr (fun d _ => inc_boundary_iff_not_interior inc h2 c d)
  rw [hbdry, interiorDoorCount, doorCount, ← Finset.filter_filter, ← Finset.filter_filter,
      Finset.filter_card_add_filter_neg_card_eq_card]

/-- **Parity of the door-count split.**  A cell is a path-endpoint seed (odd total
door-count) iff its interior-door parity and boundary-door parity disagree.  This is
the explicit reconciliation of the two parity engines: `interiorDoorCount` is the
graph-degree contribution used by `SpernerTuckerDoorGraph`, `boundaryDoorCount` the
boundary incidence used by `SpernerTuckerDoorIncidenceParity`. -/
theorem odd_doorCount_iff_xor (h2 : ∀ d, cellCount inc d ≤ 2) (c : Cell) :
    Odd (doorCount inc c)
      ↔ (Odd (interiorDoorCount inc c) ↔ Even (boundaryDoorCount inc c)) := by
  rw [doorCount_eq_interior_add_boundary inc h2, Nat.odd_add]

/-- **All-interior corollary.**  If a cell touches no boundary door then its total
door-count parity is exactly its interior (graph-degree) parity — the incidence-engine
seed coincides with the graph-engine path endpoint. -/
theorem odd_doorCount_iff_odd_interior_of_no_boundary
    (h2 : ∀ d, cellCount inc d ≤ 2)
    (hno : ∀ d, ¬ IsBoundaryDoor inc d) (c : Cell) :
    Odd (doorCount inc c) ↔ Odd (interiorDoorCount inc c) := by
  have hb0 : boundaryDoorCount inc c = 0 := by
    unfold boundaryDoorCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _ hd
    exact hno d hd.2
  rw [doorCount_eq_interior_add_boundary inc h2, hb0, Nat.add_zero]

#check @doorCount_eq_interior_add_boundary
#check @odd_doorCount_iff_xor
#check @odd_doorCount_iff_odd_interior_of_no_boundary

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no sorryAx, no Lean.ofReduceBool.
#print axioms doorCount_eq_interior_add_boundary
#print axioms odd_doorCount_iff_xor
#print axioms odd_doorCount_iff_odd_interior_of_no_boundary

end SpernerTuckerDoorInteriorBoundarySplit
