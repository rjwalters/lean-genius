/-
  Knight's Tour Oblique Angles: structure of the oblique turn graph (OQ-04)

  Open question OQ-04 of the parent entry `knights-tour-oblique` asks:

      "What is the maximum number of oblique turns in a closed tour?"

  Where the MINIMUM is exactly 4 (proved in the base file, generalized to n×n
  in OQ-01), the MAXIMUM is a search-heavy question over the ~1.3×10¹³ closed
  knight's tours of the 8×8 board and is genuinely open: no elementary closed
  form is known.  This file does NOT claim to resolve it.

  Instead it establishes, by finite enumeration, the local and global structure
  of the oblique relation on the eight knight directions -- the combinatorial
  substrate from which any oblique count is assembled.  The file is deliberately
  self-contained (it imports only Mathlib, mirroring the self-contained OQ-01),
  so every result is assumption-free: 0 axioms, 0 sorries, no `native_decide`.

  We index the eight knight directions 0..7 counterclockwise, matching
  `allMoveVectors` in the base file `KnightsTourOblique.lean`:

      0:(1,2) 1:(2,1) 2:(2,-1) 3:(1,-2) 4:(-1,-2) 5:(-2,-1) 6:(-2,1) 7:(-1,2)

  A turn from direction `i` to direction `j` is *oblique* (obtuse) iff the dot
  product `vec i ⬝ vec j` is negative; this matches `isOblique` in the base
  file.  Direction `i + 4 (mod 8)` is the *antipode* `neg i`, and the turn to
  the antipode is the reversal (dot = -5), which cannot occur in a tour because
  it would revisit the previous square -- the base file's `no_turn_angle_4_all`.

  Main results (all proved by `decide` over the finite index set):

    * `dot_neg`             -- the turn to the antipode has dot product -5;
    * `oblique_iff_dot`     -- a legal (non-reversal) turn is oblique iff its
                               dot product is exactly -3 or -4;
    * `dot_legal_spectrum`  -- the legal dot spectrum is {-4,-3,0,3,4,5};
    * `legal_successors_card`         -- 7 legal successors per direction;
    * `oblique_successors_card`       -- 3 oblique successors per direction;
    * `legal_oblique_successors_card` -- exactly 2 LEGAL oblique successors:
                               the oblique relation is 2-regular on legal turns;
    * `oblique_pairs_card` / `legal_oblique_pairs_card` -- the global oblique
                               densities 24/64 = 3/8 and 16/56 = 2/7.

  The exact maximum oblique count (OQ-04 proper) remains open; the local
  structure here constrains per-step choices but does not by itself bound the
  global maximum below the trivial 64.
-/
import Mathlib

namespace KnightsTourObliqueOQ04

open Finset

/-- The eight knight move directions, indexed 0..7 counterclockwise, matching
    `allMoveVectors` in the base entry `KnightsTourOblique.lean`. -/
def vec : Fin 8 → Int × Int
  | 0 => (1, 2)
  | 1 => (2, 1)
  | 2 => (2, -1)
  | 3 => (1, -2)
  | 4 => (-1, -2)
  | 5 => (-2, -1)
  | 6 => (-2, 1)
  | 7 => (-1, 2)

/-- Dot product of two knight directions. -/
def dot (i j : Fin 8) : Int := (vec i).1 * (vec j).1 + (vec i).2 * (vec j).2

/-- A turn from direction `i` to direction `j` is oblique (obtuse) iff the dot
    product of the two move vectors is negative. -/
def isOblique (i j : Fin 8) : Bool := decide (dot i j < 0)

/-- The antipodal (reversed) direction: `i + 4 (mod 8)`. -/
def neg (i : Fin 8) : Fin 8 := i + 4

/-! ### The antipode is the reversal -/

/-- `neg` is an involution: the antipode of the antipode is the original. -/
theorem neg_neg (i : Fin 8) : neg (neg i) = i := by
  revert i; decide

/-- The antipode really is the negated vector. -/
theorem vec_neg (i : Fin 8) : vec (neg i) = (-(vec i).1, -(vec i).2) := by
  revert i; decide

/-- The turn to the antipode is the reversal: its dot product is `-5`, the
    unique most-negative value.  In a tour this turn cannot occur (it would
    revisit the previous square), so the antipode is the one oblique successor
    that is always forbidden. -/
theorem dot_neg (i : Fin 8) : dot i (neg i) = -5 := by
  revert i; decide

/-! ### Per-turn refinement on legal (non-reversal) moves -/

/-- A legal (non-reversal) turn is oblique iff its dot product is exactly `-3`
    or `-4`.  This sharpens the base file's `oblique_iff_large_turn`
    (turn angle ∈ {3,4,5}, dot ∈ {-3,-4,-5}) by deleting the reversal value
    `-5`, consistent with `no_turn_angle_4_all`. -/
theorem oblique_iff_dot (i j : Fin 8) (h : j ≠ neg i) :
    isOblique i j = true ↔ dot i j = -3 ∨ dot i j = -4 := by
  revert i j h; decide

/-- For legal turns the dot-product spectrum loses the reversal value `-5`:
    it is exactly `{-4,-3,0,3,4,5}`. -/
theorem dot_legal_spectrum (i j : Fin 8) (h : j ≠ neg i) :
    dot i j = -4 ∨ dot i j = -3 ∨ dot i j = 0 ∨
    dot i j = 3 ∨ dot i j = 4 ∨ dot i j = 5 := by
  revert i j h; decide

/-! ### Local successor counts -/

/-- Every knight direction has exactly seven legal successors: all directions
    except its own antipode. -/
theorem legal_successors_card (i : Fin 8) :
    (univ.filter (fun j => j ≠ neg i)).card = 7 := by
  fin_cases i <;> decide

/-- Every knight direction has exactly three oblique successors (dot product
    `< 0`): the two genuine obtuse turns plus the reversal. -/
theorem oblique_successors_card (i : Fin 8) :
    (univ.filter (fun j => isOblique i j = true)).card = 3 := by
  fin_cases i <;> decide

/-- **2-regularity of the legal oblique relation.**  Removing the forbidden
    reversal from the three oblique successors leaves exactly two: every
    direction has precisely two legal oblique successors.  This is the uniform
    local constraint underlying any bound on the oblique-turn count of a tour
    (and it explains the global legal density `2/7` structurally). -/
theorem legal_oblique_successors_card (i : Fin 8) :
    (univ.filter (fun j => j ≠ neg i ∧ isOblique i j = true)).card = 2 := by
  fin_cases i <;> decide

/-! ### Global counts -/

/-- Among all `8 * 8 = 64` ordered pairs of knight directions, exactly `24` are
    oblique: a global oblique density of `24/64 = 3/8`. -/
theorem oblique_pairs_card :
    (univ.filter
      (fun p : Fin 8 × Fin 8 => isOblique p.1 p.2 = true)).card = 24 := by
  decide

/-- Among the `8 * 7 = 56` legal (non-reversal) ordered pairs, exactly `16` are
    oblique: a legal oblique density of `16/56 = 2/7`. -/
theorem legal_oblique_pairs_card :
    (univ.filter
      (fun p : Fin 8 × Fin 8 => p.2 ≠ neg p.1 ∧ isOblique p.1 p.2 = true)).card = 16 := by
  decide

end KnightsTourObliqueOQ04
