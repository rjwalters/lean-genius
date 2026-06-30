/-
  Knight's Tour Oblique Angles: Reversal Symmetry Infrastructure (OQ-02, Target D)

  Open question OQ-02 (companion to `KnightsTourObliqueOQ02.lean`) studies
  the distribution of oblique counts across all closed knight's tours on the
  8×8 board. The OQ-02 file establishes the **D4 symmetry** of that
  distribution (the dihedral group of the board acts on tours preserving
  `obliqueCount`). This file develops the *second* independent symmetry that
  the OQ-02 docstring flagged as deferred (Target D): **time reversal** of a
  tour.

  Reversal is genuinely independent of the D4 board action: D4 permutes the
  *squares* of the board (an isometry of the plane), whereas reversal
  permutes the *traversal order* of a fixed tour. Together they enlarge the
  symmetry acting on the histogram's level sets from the order-8 board group
  to a group containing an extra order-2 reversal, refining the
  orbit-divisibility picture for `obliqueDistribution`.

  ## What this file proves (verified, 0 sorries, 0 axioms)

  * `reverseTour : ClosedTour → ClosedTour`, the tour traversed backwards,
    is a *well-defined* closed tour: `List.reverse` preserves length and
    `Nodup`, the knight graph is symmetric so the reversed path is still a
    knight path, and the closing edge survives the head/last swap.
  * `reverseTour_involutive` and `reverseTour_injective`: reversal is an
    order-2 symmetry (an involution) of the finite set of closed tours.
  * The **algebraic core of count-invariance**: obliqueness of a consecutive
    move pair is both *symmetric* (`isOblique_comm`, the dot product is
    commutative) and *invariant under joint negation* (`isOblique_neg_neg`,
    `(-v₁)·(-v₂) = v₁·v₂`).  Reversing a tour reverses the cyclic move
    sequence and negates each move (`getMoveVector_swap`), so these two
    facts are exactly what make the oblique count reversal-invariant.

  ## Deferred to the next session (Target D capstone)

  `obliqueCount (reverseTour t) = obliqueCount t`.  Strategy, fully reduced
  to general list lemmas:

      tourMoves (reverseTour t) = ((tourMoves t).map MoveVector.neg).reverse.rotate 1   -- (R)

  (each reversed edge `s_{i+1} → s_i` is `neg` of the original `s_i → s_{i+1}`,
  and the cyclic move list is reversed and rotated by one). Then
  `obliqueCount` = the length of the `isOblique`-filtered cyclic-pair list,
  which is invariant under (i) `rotate 1` (cyclic shift), (ii) `reverse`
  (using `isOblique_comm`), and (iii) `map MoveVector.neg` (using
  `isOblique_neg_neg`). Lemma (R) is the only index-level step; the three
  invariances are general facts about `L.zip (L.rotate 1)`. This was left
  for a follow-up because the Aristotle proof-search backend was unavailable
  this session and the list bookkeeping is iteration-heavy.

  Parent: `KnightsTourOblique.lean`.  Sibling: `KnightsTourObliqueOQ02.lean`.
-/

import Mathlib
import Proofs.KnightsTourObliqueOQ02

namespace KnightsTourOblique

/-!
## The algebraic core: obliqueness is symmetric and negation-invariant

`isOblique v₁ v₂ = (v₁ · v₂ < 0)` and the dot product is a symmetric
bilinear form, so it is unchanged by swapping its arguments or by negating
both of them. These two facts are the entire reason reversal preserves the
oblique count.
-/

/-- The dot product of knight move vectors is commutative. -/
theorem MoveVector.dot_comm (v1 v2 : MoveVector) : v1.dot v2 = v2.dot v1 := by
  simp only [MoveVector.dot]; ring

/-- Obliqueness is symmetric: the order of the two moves does not matter
    (the dot product is commutative). -/
theorem isOblique_comm (v1 v2 : MoveVector) : isOblique v1 v2 = isOblique v2 v1 := by
  simp only [isOblique, MoveVector.dot_comm v1 v2]

/-- Negating a knight move vector is an involution. -/
@[simp] theorem MoveVector.neg_neg (v : MoveVector) : v.neg.neg = v := by
  apply MoveVector.ext <;> simp only [MoveVector.neg, _root_.neg_neg]

/-- The dot product is invariant under negating both arguments. -/
theorem MoveVector.dot_neg_neg (v1 v2 : MoveVector) :
    v1.neg.dot v2.neg = v1.dot v2 := by
  simp only [MoveVector.dot, MoveVector.neg]; ring

/-- Obliqueness is invariant under negating both moves: `(-v₁)·(-v₂) = v₁·v₂`. -/
theorem isOblique_neg_neg (v1 v2 : MoveVector) :
    isOblique v1.neg v2.neg = isOblique v1 v2 := by
  simp only [isOblique, MoveVector.dot_neg_neg]

/-- Reversing a single edge negates its move vector: for knight-adjacent
    squares, `getMoveVector s2 s1 = (getMoveVector s1 s2).neg`. This is the
    move-level statement of "traversing backwards flips each step". -/
theorem getMoveVector_swap (s1 s2 : Square) (h : knightGraph.Adj s1 s2) :
    getMoveVector s2 s1 = (getMoveVector s1 s2).neg := by
  have h12 : isKnightOffset ((s2.1 : Int) - s1.1) ((s2.2 : Int) - s1.2) = true := by
    simpa only [knightGraph, SimpleGraph.Adj, knightAdj] using h
  have h21 : isKnightOffset ((s1.1 : Int) - s2.1) ((s1.2 : Int) - s2.2) = true := by
    simpa only [knightGraph, SimpleGraph.Adj, knightAdj] using knightGraph.symm h
  simp only [getMoveVector]
  rw [dif_pos h12, dif_pos h21]
  simp only [MoveVector.neg]
  apply MoveVector.ext
  · show ((s1.1 : Int) - s2.1) = -((s2.1 : Int) - s1.1); ring
  · show ((s1.2 : Int) - s2.2) = -((s2.2 : Int) - s1.2); ring

/-!
## Reversal as a well-defined involution on closed tours

`reverseTour t` visits `t`'s squares in the opposite order. It is a genuine
`ClosedTour`: `List.reverse` preserves length and `Nodup`, the knight graph
is symmetric so the reversed path is still a knight path, and the closing
edge survives the head/last swap.
-/

/-- Reversing a knight path yields a knight path: each reversed edge is the
    original edge read backwards, and the knight graph is symmetric. -/
theorem isKnightPath_reverse {l : List Square} (h : isKnightPath l) :
    isKnightPath l.reverse := by
  intro i hi
  rw [List.length_reverse] at hi
  -- The reversed edge at `i` is the original edge at `l.length - 2 - i`,
  -- read in the opposite order; close by graph symmetry.
  have key := h (l.length - 1 - (i + 1)) (by omega)
  -- Rewrite the reversed-list getElems to the underlying list via `getElem_reverse`
  -- (`l.reverse[j] = l[l.length - 1 - j]`), then match against the original edge.
  -- Keeping the index as `l.length - 1 - (i + 1)` (rather than the equivalent
  -- `l.length - 2 - i`) leaves the minuend `l.length` visible to `omega`.
  rw [List.getElem_reverse, List.getElem_reverse]
  convert knightGraph.symm key using 2 <;> · congr 1; omega

/-- The reversed square list of a tour is nonempty. -/
theorem reverseTour_nonempty (t : ClosedTour) : t.squares.reverse ≠ [] := by
  simpa using t.nonempty

/-- The closing edge survives reversal: the head and last of the reversed
    list close up, using `t.closes` and graph symmetry. -/
theorem reverseTour_closes (t : ClosedTour) :
    knightGraph.Adj (t.squares.reverse.getLast (reverseTour_nonempty t))
                    (t.squares.reverse.head (reverseTour_nonempty t)) := by
  rw [List.getLast_reverse, List.head_reverse]
  exact knightGraph.symm t.closes

/-- **Reversal of a closed tour** (Target D infrastructure): visit the same
    squares in the opposite order. -/
def reverseTour (t : ClosedTour) : ClosedTour where
  squares := t.squares.reverse
  length_eq := by rw [List.length_reverse]; exact t.length_eq
  nodup := by rw [List.nodup_reverse]; exact t.nodup
  path := isKnightPath_reverse t.path
  nonempty := reverseTour_nonempty t
  closes := reverseTour_closes t

@[simp] theorem reverseTour_squares (t : ClosedTour) :
    (reverseTour t).squares = t.squares.reverse := rfl

/-- Reversal is an involution on closed tours: reversing twice is the
    identity (`List.reverse_reverse`). -/
theorem reverseTour_involutive (t : ClosedTour) :
    reverseTour (reverseTour t) = t := by
  rw [closedTour_eq_iff]
  simp only [reverseTour_squares, List.reverse_reverse]

/-- Reversal is injective on closed tours (it is its own inverse), hence an
    order-2 symmetry of the finite type `ClosedTour`. -/
theorem reverseTour_injective : Function.Injective reverseTour := by
  intro t1 t2 h
  have := congrArg reverseTour h
  rwa [reverseTour_involutive, reverseTour_involutive] at this

end KnightsTourOblique
