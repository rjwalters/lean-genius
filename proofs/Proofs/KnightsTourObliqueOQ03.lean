/-
  Knight's Tour Oblique Angles: Reversal × D₄ commute (OQ-03)

  Open question OQ-03 follows `KnightsTourObliqueOQ02.lean` (the histogram /
  distribution skeleton) and `KnightsTourObliqueOQ02Reverse.lean` (which built
  `reverseTour`, the time-reversal of a closed tour, and proved it is an
  involution of the finite set of closed tours).

  The OQ-02 program studies the symmetries that act on the oblique-count
  histogram of closed knight's tours.  Two symmetries are in play:

    * the dihedral board group `D₄` (`applyD4Tour`), which permutes the
      *squares* of the board (an isometry of the plane), and
    * time-reversal (`reverseTour`), which permutes the *traversal order* of a
      fixed tour.

  These are conceptually independent — one moves the board, the other walks the
  path backwards.  This file proves they **commute** as maps on closed tours,
  so the symmetry acting on tours is the order-16 group `D₄ × ℤ/2`.  This
  refines the orbit-divisibility picture for the histogram (every level set is
  closed under both actions), and it is the structural fact that lets the
  deferred reversal-invariance of `obliqueCount` be combined with the proven
  `oblique_count_invariant` (the `D₄` half).

  ## What this file proves (verified, 0 sorries, 0 axioms)

  * `reverseTour_applyD4Tour` — reversal commutes with every `D₄` element:
    `reverseTour (applyD4Tour g t) = applyD4Tour g (reverseTour t)`.  The proof
    is `List.reverse` commuting with `List.map` on the square lists.
  * `d4_reverse_leftInverse` — the composite symmetry `t ↦ reverseTour (applyD4Tour g t)`
    is undone by `t ↦ reverseTour (applyD4Tour (d4Inv g) t)`, using the
    commutation, the involutivity of `reverseTour`, and `applyD4Tour_inv_left`.
  * `d4_reverse_injective` — hence each composite symmetry is injective, an
    honest order-2-times-`D₄` symmetry of the finite type `ClosedTour`.
  * `reverseTour_applyD4Tour_orbit` — reversal maps the `D₄`-orbit of `t` onto
    the `D₄`-orbit of `reverseTour t`.

  ## Honesty / scope

  This is the *commutation* of the two symmetries, not the reversal-invariance
  of the oblique count itself (`obliqueCount (reverseTour t) = obliqueCount t`),
  which OQ-02 left deferred as iteration-heavy cyclic-list bookkeeping.  The
  parent file's uniqueness theorem `unique_four_oblique` is an axiom
  (Knuth's computational enumeration) and the base file uses `native_decide`;
  this file introduces no new axioms and uses no `native_decide` — its four
  results depend only on the foundational axioms.

  Parent: `KnightsTourObliqueOQ02Reverse.lean`.
-/

import Mathlib
import Proofs.KnightsTourObliqueOQ02Reverse

namespace KnightsTourOblique

/-!
## Time-reversal commutes with the D₄ board action

`applyD4Tour g t` maps the square list by `applyD4 g`; `reverseTour t` reverses
the square list.  Since `List.map` commutes with `List.reverse`, the two
operations commute on closed tours.
-/

/-- **Reversal commutes with `D₄`.** Permuting the board by a dihedral symmetry
and then traversing the tour backwards is the same as traversing backwards and
then permuting the board. -/
theorem reverseTour_applyD4Tour (g : Bool × Fin 4) (t : ClosedTour) :
    reverseTour (applyD4Tour g t) = applyD4Tour g (reverseTour t) := by
  rw [closedTour_eq_iff]
  show (t.squares.map (applyD4 g)).reverse = (t.squares.reverse).map (applyD4 g)
  rw [List.map_reverse]

/-- The composite symmetry `t ↦ reverseTour (applyD4Tour g t)` has the explicit
left inverse `t ↦ reverseTour (applyD4Tour (d4Inv g) t)`: reversal is an
involution and `applyD4Tour (d4Inv g)` undoes `applyD4Tour g`. -/
theorem d4_reverse_leftInverse (g : Bool × Fin 4) (t : ClosedTour) :
    reverseTour (applyD4Tour (d4Inv g) (reverseTour (applyD4Tour g t))) = t := by
  rw [reverseTour_applyD4Tour, reverseTour_involutive, applyD4Tour_inv_left]

/-- Each composite reversal-and-`D₄` symmetry is injective, so reversal together
with the board group `D₄` acts faithfully on the finite type of closed tours
(an order-16 `D₄ × ℤ/2` symmetry). -/
theorem d4_reverse_injective (g : Bool × Fin 4) :
    Function.Injective (fun t => reverseTour (applyD4Tour g t)) :=
  Function.LeftInverse.injective
    (g := fun t => reverseTour (applyD4Tour (d4Inv g) t))
    (fun t => d4_reverse_leftInverse g t)

/-- Reversal maps the `D₄`-orbit of `t` onto the `D₄`-orbit of `reverseTour t`:
the reverse of any board-symmetry image of `t` is a board-symmetry image of the
reverse of `t` (witnessed by the same group element). -/
theorem reverseTour_applyD4Tour_orbit (g : Bool × Fin 4) (t : ClosedTour) :
    ∃ h : Bool × Fin 4, reverseTour (applyD4Tour g t) = applyD4Tour h (reverseTour t) :=
  ⟨g, reverseTour_applyD4Tour g t⟩

end KnightsTourOblique
