/-
  Knight's Tour Oblique Angles: Reversal Count-Invariance Capstone (OQ-02, Target D)

  This file discharges the capstone deferred by `KnightsTourObliqueOQ02Reverse.lean`:

      obliqueCount (reverseTour t) = obliqueCount t        -- `obliqueCount_reverseTour`

  i.e. the oblique-turn count is invariant under **time reversal** of a closed
  tour. Together with the D4 board symmetry (`oblique_count_invariant`), this
  enlarges the symmetry group acting on the level sets of `obliqueDistribution`
  by an independent order-2 factor.

  ## Strategy

  `obliqueCount t` is the length of the `isOblique`-filtered list of *cyclic
  adjacent pairs* of `tourMoves t`. We abstract this as
  `cyclicObliqueCount : List MoveVector → ℕ` (definitionally equal on tours),
  and prove a single workhorse:

  * `cyclicObliqueCount_eq_of_perm_map` — if the cyclic-pair list of `L₁` is a
    permutation of `(cyclic-pair list of L₂).map f` for some `f` that preserves
    obliqueness, then `cyclicObliqueCount L₁ = cyclicObliqueCount L₂`.

  Three instances of the workhorse give the three symmetries of the cyclic
  count, matching the three algebraic facts proved in the sibling file:

  * `cyclicObliqueCount_map_neg`     (uses `isOblique_neg_neg`)   — `f = (neg, neg)`
  * `cyclicObliqueCount_reverse`     (uses `isOblique_comm`)      — `f = Prod.swap`
  * `cyclicObliqueCount_rotate_one`  (identity `f`)               — cyclic shift

  The index-level lemma (R)
      tourMoves (reverseTour t) = ((tourMoves t).map MoveVector.neg).reverse.rotate 1
  (`tourMoves_reverseTour`) then reduces the capstone to chaining the three
  invariances.

  Parent: `KnightsTourOblique.lean`. Sibling: `KnightsTourObliqueOQ02Reverse.lean`.
-/

import Mathlib
import Proofs.KnightsTourObliqueOQ02Reverse

namespace KnightsTourOblique

open List

/-! ## The cyclic oblique count as a function of the raw move list -/

/-- The oblique count expressed directly on a list of move vectors, via the
    cyclic adjacent-pair list `L.zip (L.tail ++ [L.head!])`. Definitionally
    equal to `obliqueCount` on `tourMoves t` (`obliqueCount_eq_cyclic`). -/
def cyclicObliqueCount (L : List MoveVector) : Nat :=
  ((L.zip (L.tail ++ [L.head!])).filter fun p => isOblique p.1 p.2).length

/-- `obliqueCount` is the cyclic oblique count of the tour's move list. -/
theorem obliqueCount_eq_cyclic (t : ClosedTour) :
    obliqueCount t = cyclicObliqueCount (tourMoves t) := rfl

/-! ## Workhorse: count invariance under a predicate-preserving pair map -/

/-- **Workhorse.** If the cyclic-pair list of `L₁` is a permutation of the
    cyclic-pair list of `L₂` mapped through `f`, and `f` preserves obliqueness
    of pairs, then the two cyclic oblique counts agree.

    Proof: `(filter p).length = countP p`; permutation preserves `countP`;
    `countP` commutes with `map` as `countP (p ∘ f)`; finally `f`'s
    obliqueness-preservation rewrites the predicate back. -/
theorem cyclicObliqueCount_eq_of_perm_map (L₁ L₂ : List MoveVector)
    (f : MoveVector × MoveVector → MoveVector × MoveVector)
    (hf : ∀ p : MoveVector × MoveVector, isOblique (f p).1 (f p).2 = isOblique p.1 p.2)
    (hperm : List.Perm (L₁.zip (L₁.tail ++ [L₁.head!]))
             ((L₂.zip (L₂.tail ++ [L₂.head!])).map f)) :
    cyclicObliqueCount L₁ = cyclicObliqueCount L₂ := by
  simp only [cyclicObliqueCount]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  rw [hperm.countP_eq, List.countP_map]
  apply List.countP_congr
  intro pr _
  simp only [Function.comp_apply, hf]

/-! ## Instance 1: negating every move preserves the cyclic count -/

/-- The cyclic-pair list of `L.map neg` is the cyclic-pair list of `L` with both
    coordinates negated. Index-free: `map_tail`, `head!_map`, `zip_map`. -/
theorem cyclicPairs_map_neg (L : List MoveVector) (hL : L ≠ []) :
    (L.map MoveVector.neg).zip
        ((L.map MoveVector.neg).tail ++ [(L.map MoveVector.neg).head!]) =
      (L.zip (L.tail ++ [L.head!])).map
        (fun p => (MoveVector.neg p.1, MoveVector.neg p.2)) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hL
  simp only [List.map_cons, List.tail_cons, List.head!_cons]
  rw [← List.map_singleton (f := MoveVector.neg), ← List.map_append, ← List.map_cons,
      List.zip_map]
  rfl

/-- Negating all moves preserves the cyclic oblique count
    (uses `isOblique_neg_neg`). -/
theorem cyclicObliqueCount_map_neg (L : List MoveVector) (hL : L ≠ []) :
    cyclicObliqueCount (L.map MoveVector.neg) = cyclicObliqueCount L := by
  apply cyclicObliqueCount_eq_of_perm_map _ _
    (fun p => (MoveVector.neg p.1, MoveVector.neg p.2))
  · intro p; exact isOblique_neg_neg p.1 p.2
  · rw [cyclicPairs_map_neg L hL]

/-! ## Instance 2 & 3: rotation and reversal of the move list -/

/-- For a nonempty list, the cyclic shift `L.tail ++ [L.head!]` is `L.rotate 1`. -/
theorem tail_append_head!_eq_rotate_one {α : Type*} [Inhabited α] (L : List α)
    (hL : L ≠ []) : L.tail ++ [L.head!] = L.rotate 1 := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hL
  simp

/-- Rotation by one commutes with `zip` for equal-length lists. -/
theorem zip_rotate_one_comm {α β : Type*} (l : List α) (m : List β)
    (h : l.length = m.length) :
    (l.rotate 1).zip (m.rotate 1) = (l.zip m).rotate 1 := by
  apply List.ext_getElem
  · simp [List.length_zip, List.length_rotate, h]
  · intro i hi hi2
    have hz : (l.zip m).length = l.length := by simp [List.length_zip, h]
    simp only [List.getElem_zip, List.getElem_rotate, List.length_zip, List.length_rotate,
      hz, h, Nat.min_self]

/-- Rotating the move list by one preserves the cyclic oblique count
    (the cyclic-pair list is rotated, hence a permutation). -/
theorem cyclicObliqueCount_rotate_one (L : List MoveVector) (hL : L ≠ []) :
    cyclicObliqueCount (L.rotate 1) = cyclicObliqueCount L := by
  apply cyclicObliqueCount_eq_of_perm_map _ _ id
  · intro p; simp
  · simp only [List.map_id]
    have hL1 : L.rotate 1 ≠ [] := by simpa using hL
    rw [tail_append_head!_eq_rotate_one (L.rotate 1) hL1,
        tail_append_head!_eq_rotate_one L hL,
        zip_rotate_one_comm L (L.rotate 1) (by simp [List.length_rotate])]
    exact List.rotate_perm _ 1

/-- Reversal commutes with `zip` for equal-length lists. -/
theorem zip_reverse_comm {α β : Type*} (l : List α) (m : List β)
    (h : l.length = m.length) :
    (l.zip m).reverse = l.reverse.zip m.reverse := by
  apply List.ext_getElem
  · simp [List.length_zip, List.length_reverse, h]
  · intro i hi hi2
    have hz : (l.zip m).length = l.length := by simp [List.length_zip, h]
    simp only [List.getElem_reverse, List.getElem_zip, List.length_zip, List.length_reverse,
      hz, h, Nat.min_self]

/-- Rotating a reversed-rotated list back by one recovers the reverse:
    `(L.rotate 1).reverse.rotate 1 = L.reverse`. -/
theorem rotate_one_reverse_rotate_one {α : Type*} (L : List α) :
    (L.rotate 1).reverse.rotate 1 = L.reverse := by
  rcases L with _ | ⟨a, l⟩
  · simp
  · rw [List.reverse_rotate, List.rotate_rotate, ← List.rotate_mod, List.length_reverse]
    have h0 : ((a :: l).length - 1 % (a :: l).length + 1) % (a :: l).length = 0 := by
      rcases Nat.eq_zero_or_pos l.length with h | h
      · have he : (a :: l).length = 1 := by simp [h]
        rw [he]
      · have hge : 2 ≤ (a :: l).length := by simp only [List.length_cons]; omega
        rw [Nat.mod_eq_of_lt hge, Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [h0, List.rotate_zero]

/-- Reversing the move list preserves the cyclic oblique count
    (uses `isOblique_comm`; cyclic pairs of the reverse are the swapped
    cyclic pairs of the original, up to reversal and a cyclic shift). -/
theorem cyclicObliqueCount_reverse (L : List MoveVector) (hL : L ≠ []) :
    cyclicObliqueCount L.reverse = cyclicObliqueCount L := by
  apply cyclicObliqueCount_eq_of_perm_map _ _ Prod.swap
  · intro p; simpa [Prod.swap] using isOblique_comm p.2 p.1
  · have hLr : L.reverse ≠ [] := by simpa using hL
    rw [tail_append_head!_eq_rotate_one L.reverse hLr,
        tail_append_head!_eq_rotate_one L hL, List.zip_swap]
    have key : L.reverse.zip (L.reverse.rotate 1) =
        ((L.rotate 1).zip L).reverse.rotate 1 := by
      rw [zip_reverse_comm (L.rotate 1) L (by simp [List.length_rotate]),
          ← zip_rotate_one_comm (L.rotate 1).reverse L.reverse
            (by simp [List.length_rotate]),
          rotate_one_reverse_rotate_one]
    rw [key]
    exact (List.rotate_perm _ 1).trans (List.reverse_perm _)

/-! ## The index-level reversal identity (R) and the capstone -/

/-- For a nonempty list, `L.tail ++ [L.head h] = L.rotate 1` (head-with-proof form). -/
theorem tail_append_head_eq_rotate_one {α : Type*} (L : List α) (h : L ≠ []) :
    L.tail ++ [L.head h] = L.rotate 1 := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil h
  simp

/-- `tourMoves` expressed via the cyclic rotation of the square list. -/
theorem tourMoves_eq_zip_rotate (t : ClosedTour) :
    tourMoves t = (t.squares.zip (t.squares.rotate 1)).map
      (fun p : Square × Square => getMoveVector p.1 p.2) := by
  rw [tourMoves_eq_map]
  simp only [tourPairs]
  rw [tail_append_head_eq_rotate_one t.squares t.nonempty]

/-- (R): the moves of the reversed tour are the negated moves, reversed and
    cyclically shifted by one. The closing-edge offset is exactly the cyclic
    `rotate 1`; each reversed edge negates its move (`getMoveVector_swap`). -/
theorem tourMoves_reverseTour (t : ClosedTour) :
    tourMoves (reverseTour t) =
      ((tourMoves t).map MoveVector.neg).reverse.rotate 1 := by
  -- Every cyclic consecutive square pair is knight-adjacent.
  have hpairs_adj : ∀ p ∈ t.squares.zip (t.squares.rotate 1),
      knightGraph.Adj p.1 p.2 := by
    intro p hp
    obtain ⟨s1, s2⟩ := p
    have hp' : (s1, s2) ∈ tourPairs t := by
      simp only [tourPairs]
      rw [tail_append_head_eq_rotate_one t.squares t.nonempty]
      exact hp
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hp'
    have h_adj := tourPairs_all_adj t i (by rw [tourPairs_length] at hi; omega)
    simp only at h_adj heq
    rw [heq] at h_adj
    exact h_adj
  -- On adjacent pairs, negating the move equals swapping the endpoints.
  have hcongr : (t.squares.zip (t.squares.rotate 1)).map
        (MoveVector.neg ∘ fun p : Square × Square => getMoveVector p.1 p.2)
      = (t.squares.zip (t.squares.rotate 1)).map
        ((fun p : Square × Square => getMoveVector p.1 p.2) ∘ Prod.swap) := by
    apply List.map_congr_left
    intro p hp
    obtain ⟨s1, s2⟩ := p
    simp only [Function.comp_apply, Prod.swap_prod_mk]
    exact (getMoveVector_swap s1 s2 (hpairs_adj (s1, s2) hp)).symm
  rw [tourMoves_eq_zip_rotate (reverseTour t), reverseTour_squares,
      tourMoves_eq_zip_rotate t, List.map_map, hcongr, ← List.map_map, List.zip_swap,
      ← List.map_reverse, ← List.map_rotate,
      zip_reverse_comm (t.squares.rotate 1) t.squares (by simp [List.length_rotate]),
      ← zip_rotate_one_comm (t.squares.rotate 1).reverse t.squares.reverse
        (by simp [List.length_rotate]),
      rotate_one_reverse_rotate_one]

/-- **Capstone (Target D):** the oblique count is invariant under time
    reversal of a closed tour. -/
theorem obliqueCount_reverseTour (t : ClosedTour) :
    obliqueCount (reverseTour t) = obliqueCount t := by
  have hne : tourMoves t ≠ [] := by
    have h : (tourMoves t).length = 64 := tourMoves_length t
    intro hnil; rw [hnil] at h; simp at h
  have hne_neg : (tourMoves t).map MoveVector.neg ≠ [] := by
    simpa using hne
  have hne_rev : ((tourMoves t).map MoveVector.neg).reverse ≠ [] := by
    simpa using hne_neg
  rw [obliqueCount_eq_cyclic, obliqueCount_eq_cyclic, tourMoves_reverseTour]
  rw [cyclicObliqueCount_rotate_one _ hne_rev]
  rw [cyclicObliqueCount_reverse _ hne_neg]
  rw [cyclicObliqueCount_map_neg _ hne]

end KnightsTourOblique
