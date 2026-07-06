/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib
import Proofs.SpernerMathlib

/-!
# Antipodal Parity Refinement of the Door-Counting Engine (the Tucker frontier)

Research artifact for `sperner-mathlib-oq-03`
("Tucker's lemma via Sperner door-counting").

## Where this sits

The parent entry `sperner-mathlib` proves Sperner's lemma through the door-counting
**master identity** `Sperner.sperner_parity`:

    #{panchromatic cells}  ≡  #{boundary doors}   (mod 2).

Sperner's lemma (`Sperner.exists_panchromatic`) then forces a panchromatic cell whenever
the boundary-door count is *odd*.  Tucker's lemma concerns the **antipodally symmetric**
setting — a triangulated `n`-ball whose boundary is invariant under the antipodal map
`x ↦ -x`.  A natural question (this problem) is whether the *same* door-counting engine
delivers Tucker by feeding it the antipodal symmetry.

## What this file proves

We isolate the exact parity obstruction, purely at the abstract cell-complex level of the
`sperner-mathlib` engine (no geometry, no triangulation data).  The antipodal map is a
**fixed-point-free involution on the boundary doors**: a boundary door and its antipode
are distinct boundary doors.  Feeding this into the parent's reusable
`Sperner.even_card_fpf_invol` — whose own docstring already advertises "Tucker's lemma,
Borsuk–Ulam" — gives, with the same adjacency hypotheses as `sperner_parity`:

* `even_card_boundary_doors_of_antipodal` — the raw boundary-door count is **even**;
* `even_card_panchromatic_of_antipodal` — hence, via `sperner_parity`, the panchromatic
  cell count is **even**;
* `not_odd_panchromatic_of_antipodal` — so the raw antipodal boundary can **never** supply
  the odd parity that `exists_panchromatic` requires.

This is the dimension-free, engine-level reason — established previously only for the
`n = 2` hexagon by a 64-case `decide` in `SpernerTuckerBoundaryParity`, and echoed for the
inductive tower in `SpernerTuckerAntipodalParity` — that Tucker's odd parity **cannot**
come from the raw antipodal boundary count.  It must be imported from a finer object (the
lower-dimensional Tucker instance, or the *oriented* sign door rule of
`sperner-mathlib4-oq-02-oq-07`, whose antipode acts by transpose rather than by pairing).
The result sharpens precisely what the remaining open geometric input for Tucker has to be.

## Honest status

Parity *infrastructure* on the `sperner-mathlib` door-counting engine — **not** a proof of
Tucker's lemma.  It rules out the naive door-count route and pins down the obstruction.
Self-contained; 0 sorries, 0 `axiom`s (foundational `propext` / `Classical.choice` /
`Quot.sound` only, plain `decide`, no `Lean.ofReduceBool`).
-/

namespace SpernerMathlibOQ03

open Finset Sperner

variable {V : Type*} [DecidableEq V] {d : ℕ}
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]

/-- The set of **boundary doors** of a coloring `c`: door facets `(s, k)` with no adjacent
cell (`adj s k = none`).  This is exactly the finset whose parity governs the panchromatic
count in `Sperner.sperner_parity`. -/
def boundaryDoors (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (c : V → Fin (d + 1)) : Finset (Cell × Fin (d + 1)) :=
  univ.filter (fun p => IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none)

/-- **The raw antipodal boundary-door count is even.**  If the boundary doors carry a
fixed-point-free involution `neg` — the abstract antipodal map, sending every boundary door
to a *distinct* boundary door and squaring to the identity — then their number is even.
A direct specialisation of the parent's `Sperner.even_card_fpf_invol`. -/
theorem even_card_boundary_doors_of_antipodal
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (c : V → Fin (d + 1))
    (neg : Cell × Fin (d + 1) → Cell × Fin (d + 1))
    (hInv : ∀ p ∈ boundaryDoors vertex adj c, neg (neg p) = p)
    (hMem : ∀ p ∈ boundaryDoors vertex adj c, neg p ∈ boundaryDoors vertex adj c)
    (hNe : ∀ p ∈ boundaryDoors vertex adj c, neg p ≠ p) :
    Even (boundaryDoors vertex adj c).card :=
  even_card_fpf_invol (boundaryDoors vertex adj c) neg hInv hMem hNe

/-- **Main — antipodal symmetry forces an even panchromatic count.**  Under the same
adjacency hypotheses as `Sperner.sperner_parity`, if the boundary doors admit a
fixed-point-free involution (the antipodal map), then the number of panchromatic cells is
**even**.  This is the antipodal analogue of Sperner's lemma: where Sperner's *odd*
boundary count forces an *odd* (hence positive) panchromatic count, an antipodal boundary
forces an *even* one — so it cannot, on its own, force a witness. -/
theorem even_card_panchromatic_of_antipodal
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_symm : ∀ s k s' k',
      adj s k = some (s', k') → adj s' k' = some (s, k))
    (hadj_vertex : ∀ s k s' k',
      adj s k = some (s', k') →
      (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s'))
    (hadj_ne : ∀ s k s' k', adj s k = some (s', k') → s ≠ s')
    (c : V → Fin (d + 1))
    (neg : Cell × Fin (d + 1) → Cell × Fin (d + 1))
    (hInv : ∀ p ∈ boundaryDoors vertex adj c, neg (neg p) = p)
    (hMem : ∀ p ∈ boundaryDoors vertex adj c, neg p ∈ boundaryDoors vertex adj c)
    (hNe : ∀ p ∈ boundaryDoors vertex adj c, neg p ≠ p) :
    Even (univ.filter (fun s : Cell => IsPanchromatic vertex c s)).card := by
  have hpar := sperner_parity vertex adj hadj_symm hadj_vertex hadj_ne c
  have hbdry := even_card_boundary_doors_of_antipodal vertex adj c neg hInv hMem hNe
  have hbd : boundaryDoors vertex adj c
      = univ.filter (fun p : Cell × Fin (d + 1) =>
          IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none) := rfl
  rw [hbd] at hbdry
  rw [Nat.even_iff] at hbdry ⊢
  rw [hpar]
  exact hbdry

/-- **Corollary — the raw antipodal boundary can never supply Tucker's odd parity.**  Under
antipodal symmetry the panchromatic count is even, so it is *never* odd.  In particular the
hypothesis of `Sperner.exists_panchromatic` (an *odd* boundary-door count) is unreachable
from the raw antipodal boundary alone: the odd seed Tucker needs must come from a finer
object than the door count itself. -/
theorem not_odd_panchromatic_of_antipodal
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_symm : ∀ s k s' k',
      adj s k = some (s', k') → adj s' k' = some (s, k))
    (hadj_vertex : ∀ s k s' k',
      adj s k = some (s', k') →
      (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s'))
    (hadj_ne : ∀ s k s' k', adj s k = some (s', k') → s ≠ s')
    (c : V → Fin (d + 1))
    (neg : Cell × Fin (d + 1) → Cell × Fin (d + 1))
    (hInv : ∀ p ∈ boundaryDoors vertex adj c, neg (neg p) = p)
    (hMem : ∀ p ∈ boundaryDoors vertex adj c, neg p ∈ boundaryDoors vertex adj c)
    (hNe : ∀ p ∈ boundaryDoors vertex adj c, neg p ≠ p) :
    ¬ Odd (univ.filter (fun s : Cell => IsPanchromatic vertex c s)).card := by
  have heven := even_card_panchromatic_of_antipodal
    vertex adj hadj_symm hadj_vertex hadj_ne c neg hInv hMem hNe
  exact Nat.not_odd_iff_even.mpr heven

/-! ## Non-vacuity of the parity engine

The antipodal parity core is not vacuous: here it fires on a concrete two-element
boundary-door set `{(true, 0), (false, 0)}` swapped by the antipodal involution
`(b, k) ↦ (!b, k)`, certifying the even count `2` by the same `even_card_fpf_invol`
mechanism the main theorem uses. -/
example :
    Even (({(true, (0 : Fin 1)), (false, (0 : Fin 1))} : Finset (Bool × Fin 1))).card := by
  refine even_card_fpf_invol _ (fun p => (!p.1, p.2)) ?_ ?_ ?_ <;> decide

#check @even_card_boundary_doors_of_antipodal
#check @even_card_panchromatic_of_antipodal
#check @not_odd_panchromatic_of_antipodal

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms even_card_panchromatic_of_antipodal
#print axioms not_odd_panchromatic_of_antipodal

end SpernerMathlibOQ03
