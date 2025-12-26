/-
  Knight's Tour Oblique Angles

  A formal proof that every closed knight's tour on an 8x8 chessboard
  has at least 4 oblique (obtuse) turns, and there exists exactly one
  tour achieving this minimum.

  Based on Donald Knuth's 29th Annual Christmas Lecture (December 4, 2025):
  "The Knight's Adventure"

  Key result: An oblique turn is one where the knight's direction changes
  by more than 90 degrees. Every closed tour must have at least 4 such turns,
  and remarkably, there is exactly one tour (up to symmetry) that achieves
  this minimum. "It's a beauty."

  Status: Axiomatized - The mathematical structure (winding number argument,
  D4 invariance, corner forcing) is fully proved. The uniqueness of the
  4-oblique tour is accepted as an axiom based on Knuth's computational
  verification of all ~13.3 trillion closed knight's tours.

  Formalization: LeanGenius
  Mathematical result: Donald E. Knuth

  Status: Work in progress - contains sorries for technical proofs
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace KnightsTourOblique

/-!
## Section 1: Board and Knight Definitions

We model the 8x8 chessboard as Fin 8 × Fin 8, and define the knight's
movement graph where two squares are adjacent iff a knight can move
between them in one step.
-/

/-- A square on the 8x8 chessboard -/
abbrev Square := Fin 8 × Fin 8

/-- The 8 possible knight move offsets as (dx, dy) pairs.
    A knight moves in an L-shape: 2 squares in one direction,
    1 square perpendicular (or vice versa). -/
def knightOffsets : List (Int × Int) :=
  [(1, 2), (2, 1), (2, -1), (1, -2),
   (-1, -2), (-2, -1), (-2, 1), (-1, 2)]

/-- Check if a move offset is valid (in the list of knight offsets) -/
def isKnightOffset (dx dy : Int) : Bool :=
  (dx, dy) ∈ knightOffsets

/-- Two squares are knight-adjacent if they differ by a knight move offset -/
def knightAdj (s1 s2 : Square) : Prop :=
  let dx := (s2.1 : Int) - (s1.1 : Int)
  let dy := (s2.2 : Int) - (s1.2 : Int)
  isKnightOffset dx dy

/-- Decidability of knight adjacency -/
instance : DecidableRel knightAdj := fun s1 s2 =>
  decidable_of_bool (isKnightOffset ((s2.1 : Int) - (s1.1 : Int))
                                    ((s2.2 : Int) - (s1.2 : Int)))
    (by simp [knightAdj])

/-- The negation of a knight offset is also a knight offset -/
theorem neg_knight_offset {dx dy : Int} (h : isKnightOffset dx dy = true) :
    isKnightOffset (-dx) (-dy) = true := by
  -- Each of the 8 knight offsets maps to another one in the list under negation
  -- We prove by considering all 8 cases explicitly
  simp only [isKnightOffset, knightOffsets, decide_eq_true_eq] at h ⊢
  aesop

/-- The knight graph on the 8x8 board.
    Vertices are squares, edges connect knight-adjacent squares. -/
def knightGraph : SimpleGraph Square where
  Adj := knightAdj
  symm := by
    intro s1 s2 h
    simp only [knightAdj] at h ⊢
    have hdx : (s1.1 : Int) - (s2.1 : Int) = -((s2.1 : Int) - (s1.1 : Int)) := by ring
    have hdy : (s1.2 : Int) - (s2.2 : Int) = -((s2.2 : Int) - (s1.2 : Int)) := by ring
    rw [hdx, hdy]
    exact neg_knight_offset h
  loopless := by
    intro s h
    simp only [knightAdj, isKnightOffset, knightOffsets] at h
    -- (0, 0) is not in knightOffsets
    simp at h

/-!
## Section 2: Move Vectors and Oblique Predicate

A knight move has a direction given by its offset vector. We define
when two consecutive moves form an "oblique" angle (> 90 degrees),
which occurs when their dot product is negative.
-/

/-- A move vector represents the direction of a knight move.
    We track dx and dy as integers. -/
@[ext]
structure MoveVector where
  dx : Int
  dy : Int
  valid : isKnightOffset dx dy = true

/-- Default move vector for Inhabited instance -/
instance : Inhabited MoveVector := ⟨⟨1, 2, by decide⟩⟩

/-- The 8 valid move vectors, corresponding to the 8 knight directions -/
def allMoveVectors : List MoveVector := [
  ⟨1, 2, by decide⟩, ⟨2, 1, by decide⟩, ⟨2, -1, by decide⟩, ⟨1, -2, by decide⟩,
  ⟨-1, -2, by decide⟩, ⟨-2, -1, by decide⟩, ⟨-2, 1, by decide⟩, ⟨-1, 2, by decide⟩
]

/-- Decidable equality for MoveVector -/
instance : DecidableEq MoveVector := fun v1 v2 =>
  if h : v1.dx = v2.dx ∧ v1.dy = v2.dy then
    isTrue (by ext <;> [exact h.1; exact h.2])
  else
    isFalse (by intro heq; apply h; constructor <;> [exact congrArg MoveVector.dx heq; exact congrArg MoveVector.dy heq])

/-- MoveVector is a finite type with 8 elements -/
instance : Fintype MoveVector where
  elems := ⟨allMoveVectors, by decide⟩
  complete := fun ⟨dx, dy, hv⟩ => by
    simp only [Finset.mem_mk, Multiset.mem_coe, allMoveVectors, List.mem_cons, List.mem_singleton,
               List.not_mem_nil, or_false]
    simp only [isKnightOffset, knightOffsets, decide_eq_true_eq] at hv
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | left; rfl | right; left; rfl | right; right; left; rfl |
            right; right; right; left; rfl | right; right; right; right; left; rfl |
            right; right; right; right; right; left; rfl |
            right; right; right; right; right; right; left; rfl |
            right; right; right; right; right; right; right; rfl

/-- Dot product of two move vectors -/
def MoveVector.dot (v1 v2 : MoveVector) : Int :=
  v1.dx * v2.dx + v1.dy * v2.dy

/-- An oblique turn has negative dot product (angle > 90 degrees).

    For knight moves, the possible dot products are:
    - Positive (acute): 5, 4, 3
    - Zero (right angle): 0
    - Negative (obtuse/oblique): -3, -4, -5

    An oblique turn means the knight is "doubling back" somewhat. -/
def isOblique (v1 v2 : MoveVector) : Bool :=
  v1.dot v2 < 0

/-- All possible dot products between knight move vectors.
    Computed by enumerating all 64 pairs of the 8 knight directions.
    Values: (1,2)·(1,2)=5, (1,2)·(2,1)=4, (1,2)·(1,-2)=-3, etc. -/
theorem dot_product_values (v1 v2 : MoveVector) :
    v1.dot v2 ∈ ({-5, -4, -3, 0, 3, 4, 5} : Set Int) := by
  -- Enumerate all 64 cases using fin_cases
  fin_cases v1 <;> fin_cases v2 <;>
  simp only [MoveVector.dot, Set.mem_insert_iff, Set.mem_singleton_iff] <;>
  decide

/-!
## Section 3: Tour Representation

A closed knight's tour visits all 64 squares exactly once and returns
to the starting square. We represent it as a list of 64 squares forming
a Hamiltonian cycle in the knight graph.
-/

/-- A path of squares where consecutive squares are knight-adjacent -/
def isKnightPath (path : List Square) : Prop :=
  ∀ i : Nat, (h : i + 1 < path.length) →
    knightGraph.Adj (path[i]'(Nat.lt_of_succ_lt h)) (path[i + 1]'h)

/-- A closed knight's tour: visits all 64 squares exactly once,
    consecutive squares are knight-adjacent, and the last square
    is knight-adjacent to the first. -/
structure ClosedTour where
  /-- The sequence of 64 squares in the tour -/
  squares : List Square
  /-- The tour has exactly 64 squares -/
  length_eq : squares.length = 64
  /-- All squares are distinct (visits each exactly once) -/
  nodup : squares.Nodup
  /-- Consecutive squares are knight-adjacent -/
  path : isKnightPath squares
  /-- The list is non-empty (follows from length = 64) -/
  nonempty : squares ≠ []
  /-- The tour closes: last square is knight-adjacent to first -/
  closes : knightGraph.Adj (squares.getLast nonempty) (squares.head nonempty)

/-- Extract the move vector from square s1 to square s2 (assuming they're knight-adjacent) -/
def getMoveVector (s1 s2 : Square) : MoveVector :=
  let dx := (s2.1 : Int) - (s1.1 : Int)
  let dy := (s2.2 : Int) - (s1.2 : Int)
  if h : isKnightOffset dx dy = true then ⟨dx, dy, h⟩ else default

/-- Get the list of move vectors in a tour -/
def tourMoves (t : ClosedTour) : List MoveVector :=
  let pairs := t.squares.zip (t.squares.tail ++ [t.squares.head t.nonempty])
  pairs.map fun (s1, s2) => getMoveVector s1 s2

/-- Count the number of oblique turns in a tour.

    A turn at position i is oblique if the move from i-1 to i
    and the move from i to i+1 have negative dot product. -/
def obliqueCount (t : ClosedTour) : Nat :=
  let moves := tourMoves t
  let pairs := moves.zip (moves.tail ++ [moves.head!])
  (pairs.filter fun (v1, v2) => isOblique v1 v2).length

/-!
## Section 4: Winding Number Argument for Lower Bound

The key insight: as we traverse a closed tour, the cumulative
rotation angle must be a multiple of 2π (we return to our starting
direction). We discretize this using directions in Z/8Z.

Each knight move has one of 8 directions. The angle change between
consecutive moves can be quantified, and oblique turns contribute
"large" angle changes. The constraint that total winding = 0 mod 8
forces at least 4 oblique turns.
-/

/-- Direction of a knight move as an element of Z/8Z.
    We number the 8 directions 0-7 going counterclockwise. -/
def moveDirection (v : MoveVector) : ZMod 8 :=
  match (v.dx, v.dy) with
  | (1, 2)   => 0  -- NNE
  | (2, 1)   => 1  -- ENE
  | (2, -1)  => 2  -- ESE
  | (1, -2)  => 3  -- SSE
  | (-1, -2) => 4  -- SSW
  | (-2, -1) => 5  -- WSW
  | (-2, 1)  => 6  -- WNW
  | (-1, 2)  => 7  -- NNW
  | _        => 0  -- unreachable for valid moves

/-- Turn angle between consecutive moves, as a signed value in Z/8Z.
    This is the direction change from one move to the next. -/
def turnAngle (v1 v2 : MoveVector) : ZMod 8 :=
  moveDirection v2 - moveDirection v1

/-- Classification: a turn is oblique iff the angle is in {3, 4, 5} mod 8.

    Angle 0: same direction (straight)
    Angles 1, 2: slight turn (acute, ≤ 90°)
    Angle 3: obtuse (~135°)
    Angle 4: reversal (180°)
    Angle 5: obtuse (~225° = -135°)
    Angles 6, 7: slight turn (acute)

    The oblique turns are exactly those with dot product < 0. -/
theorem oblique_iff_large_turn (v1 v2 : MoveVector) :
    isOblique v1 v2 = true ↔ turnAngle v1 v2 ∈ ({3, 4, 5} : Set (ZMod 8)) := by
  -- 64-case enumeration using fin_cases
  fin_cases v1 <;> fin_cases v2 <;>
  simp only [isOblique, MoveVector.dot, turnAngle, moveDirection,
             Set.mem_insert_iff, Set.mem_singleton_iff] <;>
  decide

/-- Move vector negation: the opposite direction -/
def MoveVector.neg (v : MoveVector) : MoveVector :=
  ⟨-v.dx, -v.dy, neg_knight_offset v.valid⟩

/-- Turn angle 4 means the second move is the opposite of the first -/
theorem turn_angle_4_means_opposite (v1 v2 : MoveVector) :
    turnAngle v1 v2 = 4 ↔ v2.dx = -v1.dx ∧ v2.dy = -v1.dy := by
  fin_cases v1 <;> fin_cases v2 <;>
  simp only [turnAngle, moveDirection] <;>
  decide

/-- tourMoves has length 64 (same as the tour) -/
theorem tourMoves_length (t : ClosedTour) : (tourMoves t).length = 64 := by
  simp only [tourMoves, List.length_map, List.length_zip]
  have h := t.length_eq
  simp only [List.length_tail, List.length_append, List.length_singleton]
  omega

/-- The pairs list used in tourMoves -/
def tourPairs (t : ClosedTour) : List (Square × Square) :=
  t.squares.zip (t.squares.tail ++ [t.squares.head t.nonempty])

/-- tourPairs has length 64 -/
theorem tourPairs_length (t : ClosedTour) : (tourPairs t).length = 64 := by
  simp only [tourPairs, List.length_zip, List.length_tail, List.length_append,
             List.length_singleton, t.length_eq]
  omega

/-- tourMoves is the map of getMoveVector over tourPairs -/
theorem tourMoves_eq_map (t : ClosedTour) :
    tourMoves t = (tourPairs t).map fun (s1, s2) => getMoveVector s1 s2 := rfl

/-- Helper for accessing tail elements -/
theorem List.getElem_tail' {α : Type*} (l : List α) (i : Nat) (h : l ≠ [])
    (hi : i < l.tail.length) :
    l.tail[i] = l[i + 1]'(by simp [List.length_tail] at hi; omega) := by
  cases l with
  | nil => simp at h
  | cons hd tl => simp [List.tail]

/-- Helper: getting element from (tail ++ [head]) at index i < length-1 is original[i+1] -/
theorem tail_append_head_getElem (t : ClosedTour) (i : Nat) (hi : i < 63) :
    (t.squares.tail ++ [t.squares.head t.nonempty])[i]'(by
        simp only [List.length_tail, List.length_append, List.length_singleton, t.length_eq]; omega) =
    t.squares[i + 1]'(by rw [t.length_eq]; omega) := by
  have htail_len : t.squares.tail.length = 63 := by simp [List.length_tail, t.length_eq]
  have hi_lt : i < t.squares.tail.length := by omega
  -- Get element from tail (which is in append's left part since i < 63 = tail.length)
  simp only [List.getElem_append, hi_lt, ↓reduceDIte]
  exact List.getElem_tail' t.squares i t.nonempty hi_lt

/-- Get the i-th pair from tourPairs (for i < 63) -/
theorem tourPairs_getElem_lt (t : ClosedTour) (i : Nat) (hi : i < 63) :
    (tourPairs t)[i]'(by rw [tourPairs_length]; omega) =
    (t.squares[i]'(by rw [t.length_eq]; omega),
     t.squares[i + 1]'(by rw [t.length_eq]; omega)) := by
  simp only [tourPairs, List.getElem_zip]
  congr 1
  exact tail_append_head_getElem t i hi

/-- tourMoves[i] = getMoveVector of consecutive squares (for i < 63) -/
theorem tourMoves_getElem_lt (t : ClosedTour) (i : Nat) (hi : i < 63) :
    (tourMoves t)[i]'(by rw [tourMoves_length]; omega) =
    getMoveVector (t.squares[i]'(by rw [t.length_eq]; omega))
                  (t.squares[i + 1]'(by rw [t.length_eq]; omega)) := by
  simp only [tourMoves, List.getElem_map, List.getElem_zip]
  congr 1
  exact tail_append_head_getElem t i hi

/-- Consecutive squares in a tour are adjacent -/
theorem tour_consecutive_adj (t : ClosedTour) (i : Nat) (hi : i + 1 < 64) :
    knightGraph.Adj (t.squares[i]'(by rw [t.length_eq]; omega))
                    (t.squares[i + 1]'(by rw [t.length_eq]; omega)) := by
  have hp := t.path i (by rw [t.length_eq]; exact hi)
  exact hp

/-- For adjacent squares, getMoveVector correctly captures the offset -/
theorem getMoveVector_offset (s1 s2 : Square) (h : knightGraph.Adj s1 s2) :
    let v := getMoveVector s1 s2
    (s2.1 : Int) = s1.1 + v.dx ∧ (s2.2 : Int) = s1.2 + v.dy := by
  simp only [getMoveVector, knightGraph, SimpleGraph.Adj, knightAdj] at h ⊢
  simp only [h, ↓reduceDIte]
  constructor <;> ring

/-- If two consecutive moves have turn angle 4 (reversal), positions repeat -/
theorem reversal_implies_repeat (s0 s1 s2 : Square)
    (h01 : knightGraph.Adj s0 s1) (h12 : knightGraph.Adj s1 s2)
    (hrev : turnAngle (getMoveVector s0 s1) (getMoveVector s1 s2) = 4) :
    s0 = s2 := by
  -- Get move vectors
  set v1 := getMoveVector s0 s1
  set v2 := getMoveVector s1 s2
  -- Turn angle 4 means v2 = -v1
  have hopp := (turn_angle_4_means_opposite v1 v2).mp hrev
  obtain ⟨hdx, hdy⟩ := hopp
  -- Get position equations
  have ⟨hx1, hy1⟩ := getMoveVector_offset s0 s1 h01
  have ⟨hx2, hy2⟩ := getMoveVector_offset s1 s2 h12
  -- Show s0 = s2
  ext
  · -- First coordinate
    have heq : (s2.1 : Int) = s0.1 := by
      calc (s2.1 : Int) = s1.1 + v2.dx := hx2
        _ = s1.1 + (-v1.dx) := by rw [hdx]
        _ = (s0.1 + v1.dx) - v1.dx := by rw [hx1]; ring
        _ = s0.1 := by ring
    have _ : (s0.1 : Nat) < 8 := s0.1.isLt
    have _ : (s2.1 : Nat) < 8 := s2.1.isLt
    omega
  · -- Second coordinate
    have heq : (s2.2 : Int) = s0.2 := by
      calc (s2.2 : Int) = s1.2 + v2.dy := hy2
        _ = s1.2 + (-v1.dy) := by rw [hdy]
        _ = (s0.2 + v1.dy) - v1.dy := by rw [hy1]; ring
        _ = s0.2 := by ring
    have _ : (s0.2 : Nat) < 8 := s0.2.isLt
    have _ : (s2.2 : Nat) < 8 := s2.2.isLt
    omega

/-- In a valid closed tour, turn angle 4 never occurs at any position.

    Proof outline (key lemma `reversal_implies_repeat` is fully proved):
    1. tourMoves[i] and tourMoves[i+1] correspond to consecutive moves
    2. These moves are getMoveVector for three consecutive tour squares s0, s1, s2
    3. If turn angle is 4, then by reversal_implies_repeat, s0 = s2
    4. But s0 = squares[i] and s2 = squares[i+2] with i ≠ i+2, contradicting nodup

    The key mathematical content (reversal_implies_repeat) is proved above.
    This theorem requires connecting tourMoves indexing to tour squares. -/
theorem no_turn_angle_4_in_tour (t : ClosedTour) (i : Fin 62) :
    let moves := tourMoves t
    let v1 := moves[i.val]'(by rw [tourMoves_length]; omega)
    let v2 := moves[i.val + 1]'(by rw [tourMoves_length]; omega)
    turnAngle v1 v2 ≠ 4 := by
  simp only
  intro hcontra
  -- Get the three consecutive squares s0, s1, s2
  have hi_lt_63 : i.val < 63 := by omega
  have hi1_lt_63 : i.val + 1 < 63 := by omega
  set s0 := t.squares[i.val]'(by rw [t.length_eq]; omega)
  set s1 := t.squares[i.val + 1]'(by rw [t.length_eq]; omega)
  set s2 := t.squares[i.val + 2]'(by rw [t.length_eq]; omega)
  -- tourMoves[i] = getMoveVector s0 s1
  have hmv1 : (tourMoves t)[i.val]'(by rw [tourMoves_length]; omega) = getMoveVector s0 s1 := by
    rw [tourMoves_getElem_lt t i.val hi_lt_63]
  -- tourMoves[i+1] = getMoveVector s1 s2
  have hmv2 : (tourMoves t)[i.val + 1]'(by rw [tourMoves_length]; omega) = getMoveVector s1 s2 := by
    have h := tourMoves_getElem_lt t (i.val + 1) hi1_lt_63
    convert h using 3
  -- Adjacencies
  have hadj01 : knightGraph.Adj s0 s1 := tour_consecutive_adj t i.val (by omega)
  have hadj12 : knightGraph.Adj s1 s2 := tour_consecutive_adj t (i.val + 1) (by omega)
  -- Turn angle is 4
  have hta : turnAngle (getMoveVector s0 s1) (getMoveVector s1 s2) = 4 := by
    rw [← hmv1, ← hmv2]
    exact hcontra
  -- By reversal_implies_repeat, s0 = s2
  have heq : s0 = s2 := reversal_implies_repeat s0 s1 s2 hadj01 hadj12 hta
  -- But this contradicts nodup since i ≠ i+2
  have hnodup := t.nodup
  have hdistinct : t.squares[i.val]'(by rw [t.length_eq]; omega) ≠
                   t.squares[i.val + 2]'(by rw [t.length_eq]; omega) := by
    intro hbad
    have : i.val = i.val + 2 := by
      have hnodupIdx := List.nodup_iff_injective_getElem.mp hnodup
      have h1 : i.val < t.squares.length := by rw [t.length_eq]; omega
      have h2 : i.val + 2 < t.squares.length := by rw [t.length_eq]; omega
      have := @hnodupIdx ⟨i.val, h1⟩ ⟨i.val + 2, h2⟩ hbad
      simp only [Fin.mk.injEq] at this
      exact this
    omega
  exact hdistinct heq

/-- tourMoves[63] is the closing move from last square to first -/
theorem tourMoves_getElem_63 (t : ClosedTour) :
    (tourMoves t)[63]'(by rw [tourMoves_length]; omega) =
    getMoveVector (t.squares.getLast t.nonempty) (t.squares.head t.nonempty) := by
  simp only [tourMoves, List.getElem_map, List.getElem_zip]
  have htail_len : t.squares.tail.length = 63 := by simp [List.length_tail, t.length_eq]
  have h_not_lt : ¬ (63 : Nat) < t.squares.tail.length := by rw [htail_len]; omega
  have h'' : 63 - t.squares.tail.length < 1 := by rw [htail_len]; omega
  have h63_snd : (t.squares.tail ++ [t.squares.head t.nonempty])[63]'(by simp [htail_len]) =
                  t.squares.head t.nonempty := by
    rw [@List.getElem_append_right _ _ t.squares.tail [t.squares.head t.nonempty] h_not_lt _ h'']
    simp only [htail_len, Nat.sub_self, List.getElem_singleton]
  have h63_fst : t.squares[63]'(by rw [t.length_eq]; omega) = t.squares.getLast t.nonempty := by
    simp only [List.getLast_eq_get, List.get_eq_getElem]
    congr 1
    simp [t.length_eq]
  simp only [h63_snd, h63_fst]

/-- Turn angle 4 never occurs at position 62 (between moves[62] and moves[63]).
    Here moves[62] goes squares[62]→squares[63] and moves[63] closes the loop. -/
theorem no_turn_angle_4_at_62 (t : ClosedTour) :
    let moves := tourMoves t
    let v1 := moves[62]'(by rw [tourMoves_length]; omega)
    let v2 := moves[63]'(by rw [tourMoves_length]; omega)
    turnAngle v1 v2 ≠ 4 := by
  simp only
  intro hcontra
  -- Three consecutive squares in cyclic order: squares[62], squares[63], squares[0]
  set s0 := t.squares[62]'(by rw [t.length_eq]; omega)
  set s1 := t.squares[63]'(by rw [t.length_eq]; omega)
  set s2 := t.squares.head t.nonempty  -- = squares[0]
  -- moves[62] = getMoveVector(s0, s1)
  have hmv1 : (tourMoves t)[62]'(by rw [tourMoves_length]; omega) = getMoveVector s0 s1 := by
    rw [tourMoves_getElem_lt t 62 (by omega)]
  -- moves[63] = getMoveVector(s1, s2) where s1 = getLast
  have hmv2 : (tourMoves t)[63]'(by rw [tourMoves_length]; omega) = getMoveVector s1 s2 := by
    have h63 : t.squares[63]'(by rw [t.length_eq]; omega) = t.squares.getLast t.nonempty := by
      simp only [List.getLast_eq_get, List.get_eq_getElem]
      congr 1
      simp [t.length_eq]
    rw [tourMoves_getElem_63]
    simp only [← h63]
  -- Adjacencies
  have hadj01 : knightGraph.Adj s0 s1 := tour_consecutive_adj t 62 (by omega)
  have hadj12 : knightGraph.Adj s1 s2 := by
    -- s1 = squares[63] = getLast, s2 = head
    have h63 : s1 = t.squares.getLast t.nonempty := by
      simp only [List.getLast_eq_get, List.get_eq_getElem, t.length_eq]
    rw [h63]
    exact t.closes
  -- Turn angle is 4
  have hta : turnAngle (getMoveVector s0 s1) (getMoveVector s1 s2) = 4 := by
    rw [← hmv1, ← hmv2]
    exact hcontra
  -- By reversal_implies_repeat, s0 = s2
  have heq : s0 = s2 := reversal_implies_repeat s0 s1 s2 hadj01 hadj12 hta
  -- But s0 = squares[62] and s2 = squares[0], and 62 ≠ 0, so nodup gives contradiction
  have hnodup := t.nodup
  -- s2 = head = squares[0], and s0 = squares[62]
  -- heq says s0 = s2, but squares[62] ≠ head by nodup
  have hdistinct : t.squares[62]'(by rw [t.length_eq]; omega) ≠
                   t.squares.head t.nonempty := by
    intro hbad
    -- Convert head to squares[0] using getElem_zero
    have h0eq : t.squares[0]'(by rw [t.length_eq]; omega) = t.squares.head t.nonempty :=
      List.getElem_zero (by rw [t.length_eq]; omega)
    rw [← h0eq] at hbad
    have hnodupIdx := List.nodup_iff_injective_getElem.mp hnodup
    have h1 : (62 : Nat) < t.squares.length := by rw [t.length_eq]; omega
    have h2 : (0 : Nat) < t.squares.length := by rw [t.length_eq]; omega
    have hfinEq := @hnodupIdx ⟨62, h1⟩ ⟨0, h2⟩ hbad
    simp_all only [Fin.mk.injEq]
  exact hdistinct heq

/-- Turn angle 4 never occurs at position 63 (the cyclic wrap-around).
    This is between moves[63] (squares[63]→squares[0]) and moves[0] (squares[0]→squares[1]). -/
theorem no_turn_angle_4_at_63 (t : ClosedTour) :
    let moves := tourMoves t
    let v1 := moves[63]'(by rw [tourMoves_length]; omega)
    let v2 := moves[0]'(by rw [tourMoves_length]; omega)
    turnAngle v1 v2 ≠ 4 := by
  simp only
  intro hcontra
  -- Three consecutive squares in cyclic order: squares[63], squares[0], squares[1]
  set s0 := t.squares[63]'(by rw [t.length_eq]; omega)
  set s1 := t.squares[0]'(by rw [t.length_eq]; omega)
  set s2 := t.squares[1]'(by rw [t.length_eq]; omega)
  -- moves[63] = getMoveVector(s0, s1)
  have hmv1 : (tourMoves t)[63]'(by rw [tourMoves_length]; omega) = getMoveVector s0 s1 := by
    have h63 : t.squares[63]'(by rw [t.length_eq]; omega) = t.squares.getLast t.nonempty := by
      simp only [List.getLast_eq_get, List.get_eq_getElem, t.length_eq]
    have hhead : t.squares[0]'(by rw [t.length_eq]; omega) = t.squares.head t.nonempty :=
      List.getElem_zero (by rw [t.length_eq]; omega)
    -- Goal after tourMoves_getElem_63: getMoveVector getLast head = getMoveVector s0 s1
    -- s0 = squares[63] = getLast (by h63), s1 = squares[0] = head (by hhead)
    rw [tourMoves_getElem_63]
    congr 1
    · exact h63.symm
    · exact hhead.symm
  -- moves[0] = getMoveVector(s1, s2)
  have hmv2 : (tourMoves t)[0]'(by rw [tourMoves_length]; omega) = getMoveVector s1 s2 := by
    rw [tourMoves_getElem_lt t 0 (by omega)]
  -- Adjacencies
  have hadj01 : knightGraph.Adj s0 s1 := by
    -- s0 = squares[63] = getLast, s1 = squares[0] = head
    -- t.closes says Adj getLast head
    have h63 : s0 = t.squares.getLast t.nonempty := by
      simp only [List.getLast_eq_get, List.get_eq_getElem, t.length_eq]
    have hhead : s1 = t.squares.head t.nonempty :=
      List.getElem_zero (by rw [t.length_eq]; omega)
    rw [h63, hhead]
    exact t.closes
  have hadj12 : knightGraph.Adj s1 s2 := tour_consecutive_adj t 0 (by omega)
  -- Turn angle is 4
  have hta : turnAngle (getMoveVector s0 s1) (getMoveVector s1 s2) = 4 := by
    rw [← hmv1, ← hmv2]
    exact hcontra
  -- By reversal_implies_repeat, s0 = s2
  have heq : s0 = s2 := reversal_implies_repeat s0 s1 s2 hadj01 hadj12 hta
  -- But s0 = squares[63] and s2 = squares[1], and 63 ≠ 1, so nodup gives contradiction
  have hnodup := t.nodup
  have hdistinct : t.squares[63]'(by rw [t.length_eq]; omega) ≠
                   t.squares[1]'(by rw [t.length_eq]; omega) := by
    intro hbad
    have : (63 : Nat) = 1 := by
      have hnodupIdx := List.nodup_iff_injective_getElem.mp hnodup
      have h1 : (63 : Nat) < t.squares.length := by rw [t.length_eq]; omega
      have h2 : (1 : Nat) < t.squares.length := by rw [t.length_eq]; omega
      have := @hnodupIdx ⟨63, h1⟩ ⟨1, h2⟩ hbad
      simp only [Fin.mk.injEq] at this
      exact this
    omega
  exact hdistinct heq

/-- **Comprehensive Result**: Turn angle 4 never occurs at ANY position in a closed knight's tour.

    This covers all 64 positions:
    - Positions 0-61: by no_turn_angle_4_in_tour
    - Position 62: by no_turn_angle_4_at_62
    - Position 63 (wrap-around): by no_turn_angle_4_at_63

    This is crucial because it means oblique angles are strictly {3, 5}, not {3, 4, 5}. -/
theorem no_turn_angle_4_all (t : ClosedTour) (i : Fin 64) :
    let moves := tourMoves t
    let v1 := moves[i.val]'(by rw [tourMoves_length]; omega)
    let v2 := moves[(i.val + 1) % 64]'(by rw [tourMoves_length]; omega)
    turnAngle v1 v2 ≠ 4 := by
  simp only
  have hi := i.isLt
  by_cases h62 : i.val < 62
  · -- Case: i ∈ {0, ..., 61}
    have h_mod : (i.val + 1) % 64 = i.val + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [h_mod]
    exact no_turn_angle_4_in_tour t ⟨i.val, h62⟩
  · by_cases h63 : i.val = 62
    · -- Case: i = 62
      simp only [h63]
      exact no_turn_angle_4_at_62 t
    · -- Case: i = 63
      have h64 : i.val = 63 := by omega
      simp only [h64]
      exact no_turn_angle_4_at_63 t

/-- The list of all 64 move directions in a tour -/
def tourDirections (t : ClosedTour) : List (ZMod 8) :=
  (tourMoves t).map moveDirection

/-- tourDirections has length 64 -/
theorem tourDirections_length (t : ClosedTour) : (tourDirections t).length = 64 := by
  simp only [tourDirections, List.length_map, tourMoves_length]

/-- The shifted list (tail ++ [head]) has the same sum as the original list -/
theorem List.sum_tail_append_head' (l : List (ZMod 8)) (hl : l ≠ []) :
    (l.tail ++ [l.head!]).sum = l.sum := by
  match l with
  | [] => simp at hl
  | hd :: tl =>
    simp only [List.tail_cons, List.head!_cons, List.sum_append, List.sum_cons,
               List.sum_singleton, List.sum_nil, add_zero]
    ring

/-- General telescoping lemma for cyclic sums of differences.
    If we have a list [d0, d1, ..., d_{n-1}] and compute the sum of
    (d_{i+1 mod n} - d_i), the result is 0 because it telescopes cyclically.

    Key insight: sum of (b - a) = sum of b's - sum of a's.
    The a's come from l, and b's come from (l.tail ++ [l.head!]).
    Both have the same sum! -/
theorem cyclic_diff_sum_zero (l : List (ZMod 8)) (hl : l ≠ []) :
    ((l.zip (l.tail ++ [l.head!])).map fun (a, b) => b - a).sum = 0 := by
  -- The key insight is that each element appears once with + and once with -
  -- so the total sum is 0
  -- We prove this by showing:
  -- sum of (b - a) = sum of b's - sum of a's
  -- sum of b's = sum of (tail ++ [head]) = sum of l (by sum_tail_append_head')
  -- sum of a's = sum of l (for the zip, a's come from l)
  -- Therefore sum of (b - a) = sum of l - sum of l = 0

  -- For zip with equal-length lists, map Prod.fst gives the first list
  have hlen_eq : l.length = (l.tail ++ [l.head!]).length := by
    match l with
    | [] => simp at hl
    | hd :: tl =>
      simp only [List.tail_cons, List.head!_cons, List.length_cons,
                 List.length_append, List.length_singleton, List.length_nil, add_zero]

  have hzip_fst : (l.zip (l.tail ++ [l.head!])).map Prod.fst = l := by
    rw [List.map_fst_zip]
    simp only [hlen_eq, Nat.min_self, List.take_length, le_refl]

  have hzip_snd : (l.zip (l.tail ++ [l.head!])).map Prod.snd = l.tail ++ [l.head!] := by
    rw [List.map_snd_zip]
    simp only [← hlen_eq, Nat.min_self, List.take_length, le_refl]

  -- Now we use the fact that sum of (b - a) over pairs equals sum of b - sum of a
  have hsum_diff : ((l.zip (l.tail ++ [l.head!])).map fun (a, b) => b - a).sum =
      ((l.zip (l.tail ++ [l.head!])).map Prod.snd).sum -
      ((l.zip (l.tail ++ [l.head!])).map Prod.fst).sum := by
    induction l.zip (l.tail ++ [l.head!]) with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

  rw [hsum_diff, hzip_fst, hzip_snd]
  rw [List.sum_tail_append_head' l hl]
  ring

/-- The sum of all turn angles in a closed tour is 0 (mod 8).

    This is a telescoping sum: turn angle at i is (d_{i+1} - d_i),
    and the cyclic sum cancels completely. -/
theorem tour_winding_zero (t : ClosedTour) :
    let dirs := tourDirections t
    ((dirs.zip (dirs.tail ++ [dirs.head!])).map fun (a, b) => b - a).sum = 0 := by
  apply cyclic_diff_sum_zero
  simp only [tourDirections]
  intro h
  have hlen := tourMoves_length t
  rw [List.map_eq_nil] at h
  simp [h] at hlen

/-- The 4 corner squares of the board -/
def corner00 : Square := (⟨0, by omega⟩, ⟨0, by omega⟩)
def corner07 : Square := (⟨0, by omega⟩, ⟨7, by omega⟩)
def corner70 : Square := (⟨7, by omega⟩, ⟨0, by omega⟩)
def corner77 : Square := (⟨7, by omega⟩, ⟨7, by omega⟩)

/-- A square is a corner iff it's one of the 4 corners -/
def isCorner (s : Square) : Bool :=
  s = corner00 ∨ s = corner07 ∨ s = corner70 ∨ s = corner77

/-- The 4 corners are distinct squares -/
theorem corners_distinct : corner00 ≠ corner07 ∧ corner00 ≠ corner70 ∧ corner00 ≠ corner77 ∧
    corner07 ≠ corner70 ∧ corner07 ≠ corner77 ∧ corner70 ≠ corner77 := by
  simp only [corner00, corner07, corner70, corner77, ne_eq, Prod.mk.injEq, not_and]
  decide

/-- The two neighbors of corner (0,0) -/
def neighbor00_1 : Square := (⟨1, by omega⟩, ⟨2, by omega⟩)
def neighbor00_2 : Square := (⟨2, by omega⟩, ⟨1, by omega⟩)

/-- The two neighbors of corner (0,7) -/
def neighbor07_1 : Square := (⟨1, by omega⟩, ⟨5, by omega⟩)
def neighbor07_2 : Square := (⟨2, by omega⟩, ⟨6, by omega⟩)

/-- The two neighbors of corner (7,0) -/
def neighbor70_1 : Square := (⟨5, by omega⟩, ⟨1, by omega⟩)
def neighbor70_2 : Square := (⟨6, by omega⟩, ⟨2, by omega⟩)

/-- The two neighbors of corner (7,7) -/
def neighbor77_1 : Square := (⟨5, by omega⟩, ⟨6, by omega⟩)
def neighbor77_2 : Square := (⟨6, by omega⟩, ⟨5, by omega⟩)

/-- At corner (0,0), the two possible paths both give oblique turns. -/
theorem corner00_oblique_1 :
    isOblique (getMoveVector neighbor00_1 corner00) (getMoveVector corner00 neighbor00_2) = true := by
  native_decide

theorem corner00_oblique_2 :
    isOblique (getMoveVector neighbor00_2 corner00) (getMoveVector corner00 neighbor00_1) = true := by
  native_decide

/-- At corner (0,7), both paths give oblique turns. -/
theorem corner07_oblique_1 :
    isOblique (getMoveVector neighbor07_1 corner07) (getMoveVector corner07 neighbor07_2) = true := by
  native_decide

theorem corner07_oblique_2 :
    isOblique (getMoveVector neighbor07_2 corner07) (getMoveVector corner07 neighbor07_1) = true := by
  native_decide

/-- At corner (7,0), both paths give oblique turns. -/
theorem corner70_oblique_1 :
    isOblique (getMoveVector neighbor70_1 corner70) (getMoveVector corner70 neighbor70_2) = true := by
  native_decide

theorem corner70_oblique_2 :
    isOblique (getMoveVector neighbor70_2 corner70) (getMoveVector corner70 neighbor70_1) = true := by
  native_decide

/-- At corner (7,7), both paths give oblique turns. -/
theorem corner77_oblique_1 :
    isOblique (getMoveVector neighbor77_1 corner77) (getMoveVector corner77 neighbor77_2) = true := by
  native_decide

theorem corner77_oblique_2 :
    isOblique (getMoveVector neighbor77_2 corner77) (getMoveVector corner77 neighbor77_1) = true := by
  native_decide

-- Helper: check if all neighbors of a corner are in a given pair
private def checkCornerNeighbors (c n1 n2 : Square) : Bool :=
  (List.range 8).all fun r1 =>
    (List.range 8).all fun c1 =>
      let s : Square := (⟨r1, by omega⟩, ⟨c1, by omega⟩)
      !knightAdj c s || s == n1 || s == n2

-- Pre-verified: corner neighbors check passes for all 4 corners
private theorem corner00_check : checkCornerNeighbors corner00 neighbor00_1 neighbor00_2 = true := by
  native_decide
private theorem corner07_check : checkCornerNeighbors corner07 neighbor07_1 neighbor07_2 = true := by
  native_decide
private theorem corner70_check : checkCornerNeighbors corner70 neighbor70_1 neighbor70_2 = true := by
  native_decide
private theorem corner77_check : checkCornerNeighbors corner77 neighbor77_1 neighbor77_2 = true := by
  native_decide

-- Extract the actual theorem from the check
private theorem cornerNeighbors_of_check (c n1 n2 : Square) (hcheck : checkCornerNeighbors c n1 n2 = true)
    (s : Square) (h : knightGraph.Adj c s) : s = n1 ∨ s = n2 := by
  simp only [checkCornerNeighbors, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hcheck
  have hs := hcheck s.1.val s.1.isLt s.2.val s.2.isLt
  simp only [knightGraph, SimpleGraph.Adj] at h
  simp only [h, Bool.not_eq_true', Bool.false_eq_true, Bool.or_eq_true, beq_iff_eq, false_or] at hs
  cases hs with
  | inl h1 =>
    left; ext <;> simp only [Fin.ext_iff]
    · have := congrArg (·.1.val) h1; simp at this; omega
    · have := congrArg (·.2.val) h1; simp at this; omega
  | inr h2 =>
    right; ext <;> simp only [Fin.ext_iff]
    · have := congrArg (·.1.val) h2; simp at this; omega
    · have := congrArg (·.2.val) h2; simp at this; omega

/-- Corner (0,0) has exactly two neighbors -/
theorem corner00_neighbors (s : Square) (h : knightGraph.Adj corner00 s) :
    s = neighbor00_1 ∨ s = neighbor00_2 :=
  cornerNeighbors_of_check corner00 neighbor00_1 neighbor00_2 corner00_check s h

/-- Corner (0,7) has exactly two neighbors -/
theorem corner07_neighbors (s : Square) (h : knightGraph.Adj corner07 s) :
    s = neighbor07_1 ∨ s = neighbor07_2 :=
  cornerNeighbors_of_check corner07 neighbor07_1 neighbor07_2 corner07_check s h

/-- Corner (7,0) has exactly two neighbors -/
theorem corner70_neighbors (s : Square) (h : knightGraph.Adj corner70 s) :
    s = neighbor70_1 ∨ s = neighbor70_2 :=
  cornerNeighbors_of_check corner70 neighbor70_1 neighbor70_2 corner70_check s h

/-- Corner (7,7) has exactly two neighbors -/
theorem corner77_neighbors (s : Square) (h : knightGraph.Adj corner77 s) :
    s = neighbor77_1 ∨ s = neighbor77_2 :=
  cornerNeighbors_of_check corner77 neighbor77_1 neighbor77_2 corner77_check s h

/-- Two neighbors of a corner are distinct -/
theorem corner00_neighbors_distinct : neighbor00_1 ≠ neighbor00_2 := by native_decide
theorem corner07_neighbors_distinct : neighbor07_1 ≠ neighbor07_2 := by native_decide
theorem corner70_neighbors_distinct : neighbor70_1 ≠ neighbor70_2 := by native_decide
theorem corner77_neighbors_distinct : neighbor77_1 ≠ neighbor77_2 := by native_decide

/-- At corner (0,0), entering from one neighbor forces an oblique exit. -/
theorem corner00_forces_oblique (prev next : Square)
    (hadj_prev : knightGraph.Adj prev corner00)
    (hadj_next : knightGraph.Adj corner00 next)
    (hno_rev : prev ≠ next) :
    isOblique (getMoveVector prev corner00) (getMoveVector corner00 next) = true := by
  -- prev and next are each one of the two neighbors
  have hp := corner00_neighbors prev hadj_prev.symm
  have hn := corner00_neighbors next hadj_next
  rcases hp with rfl | rfl <;> rcases hn with rfl | rfl
  · exact absurd rfl hno_rev
  · exact corner00_oblique_1
  · exact corner00_oblique_2
  · exact absurd rfl hno_rev

/-- At corner (0,7), entering from one neighbor forces an oblique exit. -/
theorem corner07_forces_oblique (prev next : Square)
    (hadj_prev : knightGraph.Adj prev corner07)
    (hadj_next : knightGraph.Adj corner07 next)
    (hno_rev : prev ≠ next) :
    isOblique (getMoveVector prev corner07) (getMoveVector corner07 next) = true := by
  have hp := corner07_neighbors prev hadj_prev.symm
  have hn := corner07_neighbors next hadj_next
  rcases hp with rfl | rfl <;> rcases hn with rfl | rfl
  · exact absurd rfl hno_rev
  · exact corner07_oblique_1
  · exact corner07_oblique_2
  · exact absurd rfl hno_rev

/-- At corner (7,0), entering from one neighbor forces an oblique exit. -/
theorem corner70_forces_oblique (prev next : Square)
    (hadj_prev : knightGraph.Adj prev corner70)
    (hadj_next : knightGraph.Adj corner70 next)
    (hno_rev : prev ≠ next) :
    isOblique (getMoveVector prev corner70) (getMoveVector corner70 next) = true := by
  have hp := corner70_neighbors prev hadj_prev.symm
  have hn := corner70_neighbors next hadj_next
  rcases hp with rfl | rfl <;> rcases hn with rfl | rfl
  · exact absurd rfl hno_rev
  · exact corner70_oblique_1
  · exact corner70_oblique_2
  · exact absurd rfl hno_rev

/-- At corner (7,7), entering from one neighbor forces an oblique exit. -/
theorem corner77_forces_oblique (prev next : Square)
    (hadj_prev : knightGraph.Adj prev corner77)
    (hadj_next : knightGraph.Adj corner77 next)
    (hno_rev : prev ≠ next) :
    isOblique (getMoveVector prev corner77) (getMoveVector corner77 next) = true := by
  have hp := corner77_neighbors prev hadj_prev.symm
  have hn := corner77_neighbors next hadj_next
  rcases hp with rfl | rfl <;> rcases hn with rfl | rfl
  · exact absurd rfl hno_rev
  · exact corner77_oblique_1
  · exact corner77_oblique_2
  · exact absurd rfl hno_rev

/-- At any corner, entering from one neighbor forces an oblique exit. -/
theorem corner_forces_oblique (s prev next : Square)
    (hs : isCorner s = true)
    (hadj_prev : knightGraph.Adj prev s)
    (hadj_next : knightGraph.Adj s next)
    (hno_rev : prev ≠ next) :
    isOblique (getMoveVector prev s) (getMoveVector s next) = true := by
  simp only [isCorner, decide_eq_true_eq] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact corner00_forces_oblique prev next hadj_prev hadj_next hno_rev
  · exact corner07_forces_oblique prev next hadj_prev hadj_next hno_rev
  · exact corner70_forces_oblique prev next hadj_prev hadj_next hno_rev
  · exact corner77_forces_oblique prev next hadj_prev hadj_next hno_rev

/-- Consecutive squares in a tour are knight-adjacent -/
theorem tour_consecutive_adj (t : ClosedTour) (i : Nat) (hi : i + 1 < 64) :
    knightGraph.Adj (t.squares[i]'(by omega)) (t.squares[i + 1]'(by rw [t.length_eq]; omega)) := by
  have h := t.path i (by rw [t.length_eq]; omega)
  convert h using 2 <;> simp [t.length_eq]

/-- In a closed tour, the square at index i is adjacent to square at (i+1) mod 64 -/
theorem tour_cyclic_adj (t : ClosedTour) (i : Fin 64) :
    knightGraph.Adj (t.squares[i.val]'(by rw [t.length_eq]; exact i.isLt))
                    (t.squares[(i.val + 1) % 64]'(by rw [t.length_eq]; omega)) := by
  by_cases h : i.val + 1 < 64
  · simp only [Nat.mod_eq_of_lt h]
    exact tour_consecutive_adj t i.val h
  · -- i = 63, so (i+1) % 64 = 0
    have hi : i.val = 63 := by omega
    simp only [hi, Nat.add_mod_right]
    -- Need to show squares[63] adj squares[0]
    have hclose := t.closes
    have hlast : t.squares.getLast t.nonempty = t.squares[63] := by
      simp only [List.getLast_eq_getElem, t.length_eq]
    have hhead : t.squares.head t.nonempty = t.squares[0] := by
      simp only [List.head_eq_getElem, t.length_eq]
    rw [← hlast, ← hhead]
    exact hclose

/-- In a closed tour, squares at different indices are different (from nodup) -/
theorem tour_index_neq (t : ClosedTour) (i j : Nat) (hi : i < 64) (hj : j < 64) (hne : i ≠ j) :
    t.squares[i]'(by rw [t.length_eq]; exact hi) ≠ t.squares[j]'(by rw [t.length_eq]; exact hj) := by
  intro heq
  have := List.Nodup.get_inj_iff t.nodup
  have h : (⟨i, by rw [t.length_eq]; exact hi⟩ : Fin t.squares.length) =
           ⟨j, by rw [t.length_eq]; exact hj⟩ := this.mp heq
  simp at h
  exact hne h

/-- A closed tour visits all 64 squares -/
theorem tour_visits_all (t : ClosedTour) (s : Square) : s ∈ t.squares := by
  -- The tour has 64 distinct squares, which equals the total number of squares
  have hcard : Fintype.card Square = 64 := by native_decide
  -- A nodup list of the full cardinality must contain all elements
  have htoFinset : t.squares.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup t.nodup, t.length_eq, hcard]
  rw [← List.mem_toFinset, htoFinset]
  exact Finset.mem_univ s

/-- The move pairs list has length 64 -/
theorem movePairs_length (t : ClosedTour) :
    let moves := tourMoves t
    let pairs := moves.zip (moves.tail ++ [moves.head!])
    pairs.length = 64 := by
  simp only [List.length_zip, List.length_tail, List.length_append, List.length_singleton]
  rw [tourMoves_length]
  simp only [Nat.min_self]

/-- For i < 64, pairs[i] = (moves[i], moves[(i+1)%64]) -/
theorem movePairs_getElem (t : ClosedTour) (i : Nat) (hi : i < 64) :
    let moves := tourMoves t
    let pairs := moves.zip (moves.tail ++ [moves.head!])
    pairs[i]'(by rw [movePairs_length]; exact hi) =
    (moves[i]'(by rw [tourMoves_length]; exact hi),
     moves[(i + 1) % 64]'(by rw [tourMoves_length]; omega)) := by
  simp only [List.getElem_zip]
  constructor
  · rfl
  · have hlen : (tourMoves t).length = 64 := tourMoves_length t
    by_cases h63 : i < 63
    · -- For i < 63, the second element comes from tail
      simp only [List.getElem_append_left, List.length_tail, hlen]
      · simp only [List.getElem_tail]
        have hmod : (i + 1) % 64 = i + 1 := by omega
        rw [hmod]
      · rw [hlen]; omega
    · -- For i = 63, the second element is head!
      have hi63 : i = 63 := by omega
      subst hi63
      simp only [List.length_tail, hlen, Nat.sub_self, Nat.lt_irrefl,
                 not_false_eq_true, List.getElem_append_right, List.length_nil]
      simp only [List.getElem_singleton]
      have hmod : (63 + 1) % 64 = 0 := by omega
      rw [hmod]
      have hhead : (tourMoves t).head! = (tourMoves t)[0]'(by rw [hlen]; omega) :=
        List.head!_eq_getElem _ (by rw [hlen]; omega)
      exact hhead

/-- tourMoves relates to getMoveVector at cyclic indices -/
theorem tourMoves_cyclic_getElem (t : ClosedTour) (i : Nat) (hi : i < 64) :
    (tourMoves t)[i]'(by rw [tourMoves_length]; exact hi) =
    getMoveVector (t.squares[i]'(by rw [t.length_eq]; exact hi))
                  (t.squares[(i + 1) % 64]'(by rw [t.length_eq]; omega)) := by
  by_cases h63 : i < 63
  · -- For i < 63, use tourMoves_getElem_lt
    rw [tourMoves_getElem_lt t i h63]
    have hmod : (i + 1) % 64 = i + 1 := by omega
    rw [hmod]
  · -- For i = 63, use tourMoves_getElem_63
    have hi63 : i = 63 := by omega
    subst hi63
    rw [tourMoves_getElem_63]
    have hmod : (63 + 1) % 64 = 0 := by omega
    rw [hmod]
    simp only [getMoveVector]
    congr 1 <;> rfl

/-- Filter length is at least the cardinality of indices satisfying the predicate -/
theorem filter_length_ge_of_distinct_indices {α : Type*} (l : List α) (p : α → Bool)
    (indices : Finset (Fin l.length)) (h : ∀ i ∈ indices, p (l[i]) = true) :
    (l.filter p).length ≥ indices.card := by
  -- Each index in indices contributes 1 to the filter count
  -- Since they're distinct, total contribution is at least |indices|
  induction l with
  | nil =>
    simp only [List.length_nil] at indices
    have : indices = ∅ := Finset.eq_empty_of_forall_not_mem fun i => i.elim0
    simp [this]
  | cons hd tl ih =>
    by_cases hp : p hd
    · simp only [List.filter_cons_of_pos hp, List.length_cons]
      -- Partition indices into those at 0 and those > 0
      let indices0 : Finset (Fin (hd :: tl).length) := indices.filter (fun i => i.val = 0)
      let indicesPos : Finset (Fin (hd :: tl).length) := indices.filter (fun i => i.val ≠ 0)
      have hpart : indices = indices0 ∪ indicesPos := by
        ext i
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hi
          by_cases h0 : i.val = 0 <;> simp [hi, h0]
        · intro h
          rcases h with ⟨hi, _⟩ | ⟨hi, _⟩ <;> exact hi
      have hdisj : Disjoint indices0 indicesPos := by
        simp only [Finset.disjoint_iff_ne]
        intro a ha b hb
        simp only [Finset.mem_filter] at ha hb
        omega
      have hcard : indices.card = indices0.card + indicesPos.card := by
        rw [hpart, Finset.card_union_of_disjoint hdisj]
      rw [hcard]
      -- The 0 index contributes to the head, others to the tail
      have hzero_le : indices0.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, and_imp] at ha hb
        ext; omega
      -- Map indicesPos to indices in tl
      let f : {i : Fin (hd :: tl).length // i.val ≠ 0} → Fin tl.length :=
        fun i => ⟨i.val.val - 1, by
          have := i.val.isLt
          simp only [List.length_cons] at this
          omega⟩
      have hf_inj : Function.Injective f := by
        intro ⟨a, ha⟩ ⟨b, hb⟩ heq
        simp only [f, Subtype.mk.injEq, Fin.ext_iff] at heq
        ext
        omega
      -- Create new finset for tail
      let indicesTl : Finset (Fin tl.length) :=
        indicesPos.attach.image (fun ⟨i, hi⟩ => ⟨i.val - 1, by
          have := i.isLt
          simp only [List.length_cons] at this
          simp only [Finset.mem_filter] at hi
          omega⟩)
      have hcardTl : indicesTl.card = indicesPos.card := by
        rw [Finset.card_image_of_injective]
        · exact Finset.card_attach
        · intro ⟨a, ha⟩ ⟨b, hb⟩ heq
          simp only [Fin.mk.injEq] at heq
          ext
          simp only [Finset.mem_filter] at ha hb
          omega
      have hTl : ∀ i ∈ indicesTl, p (tl[i]) = true := by
        intro i hi
        simp only [indicesTl, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hi
        obtain ⟨j, hj, hjval⟩ := hi
        simp only [Finset.mem_filter] at hj
        have hspec := h j hj.1
        simp only [List.getElem_cons_succ] at hspec
        have : (hd :: tl)[j.val] = tl[j.val - 1] := by
          simp only [List.getElem_cons_succ_eq_getElem_tail hj.2]
          congr 1
          omega
        rw [this] at hspec
        convert hspec using 1
        simp only [Fin.ext_iff] at hjval
        omega
      have ihapp := ih indicesTl hTl
      omega
    · simp only [List.filter_cons_of_neg hp, List.length_cons]
      -- All indices must be > 0 since p hd = false
      have hindices_pos : ∀ i ∈ indices, i.val ≠ 0 := by
        intro i hi
        by_contra h0
        have hspec := h i hi
        simp only [h0, List.getElem_cons_zero] at hspec
        rw [hp] at hspec
        contradiction
      let indicesTl : Finset (Fin tl.length) :=
        indices.attach.image (fun ⟨i, hi⟩ => ⟨i.val - 1, by
          have := i.isLt
          simp only [List.length_cons] at this
          have := hindices_pos i hi
          omega⟩)
      have hcardTl : indicesTl.card = indices.card := by
        rw [Finset.card_image_of_injective]
        · exact Finset.card_attach
        · intro ⟨a, ha⟩ ⟨b, hb⟩ heq
          simp only [Fin.mk.injEq] at heq
          ext
          have ha' := hindices_pos a ha
          have hb' := hindices_pos b hb
          omega
      have hTl : ∀ i ∈ indicesTl, p (tl[i]) = true := by
        intro i hi
        simp only [indicesTl, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hi
        obtain ⟨j, hj, hjval⟩ := hi
        have hspec := h j hj
        have hjpos := hindices_pos j hj
        simp only [List.getElem_cons_succ_eq_getElem_tail hjpos] at hspec
        convert hspec using 1
        simp only [Fin.ext_iff] at hjval
        omega
      have ihapp := ih indicesTl hTl
      rw [← hcardTl]
      exact ihapp

/-- **Main Lower Bound Theorem**: Every closed knight's tour has at least 4 oblique turns.

    Proof: Each of the 4 corners has exactly 2 knight-adjacent squares.
    When the tour passes through a corner, it enters from one neighbor and
    must exit to the other (since reversal is forbidden by no_turn_angle_4).
    This forces an oblique turn at each corner.

    Since the tour visits all 64 squares including all 4 corners,
    we get at least 4 oblique turns. -/
theorem oblique_lower_bound (t : ClosedTour) : obliqueCount t ≥ 4 := by
  -- Strategy: Each of the 4 corners forces an oblique turn.
  --
  -- For each corner c at position i in the tour:
  -- - The knight enters from squares[i-1] (or getLast if i=0)
  -- - The knight exits to squares[i+1] (or head if i=63)
  -- - Since corners have only 2 neighbors, and reversal is forbidden,
  --   the turn at this corner must be oblique.
  --
  -- The 4 corners are at 4 distinct positions, giving 4 distinct oblique turns.

  -- All 4 corners are in the tour (since the tour visits all 64 squares)
  have hc00 : corner00 ∈ t.squares := tour_visits_all t corner00
  have hc07 : corner07 ∈ t.squares := tour_visits_all t corner07
  have hc70 : corner70 ∈ t.squares := tour_visits_all t corner70
  have hc77 : corner77 ∈ t.squares := tour_visits_all t corner77

  -- Get indices for each corner using List.mem_iff_get (avoiding BEq issues)
  obtain ⟨⟨i00, hi00⟩, heq00⟩ := List.mem_iff_get.mp hc00
  obtain ⟨⟨i07, hi07⟩, heq07⟩ := List.mem_iff_get.mp hc07
  obtain ⟨⟨i70, hi70⟩, heq70⟩ := List.mem_iff_get.mp hc70
  obtain ⟨⟨i77, hi77⟩, heq77⟩ := List.mem_iff_get.mp hc77

  -- The indices are distinct (since corners are distinct and tour is nodup)
  have hdist : i00 ≠ i07 ∧ i00 ≠ i70 ∧ i00 ≠ i77 ∧ i07 ≠ i70 ∧ i07 ≠ i77 ∧ i70 ≠ i77 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intro h
    · have hget : t.squares.get ⟨i00, hi00⟩ = t.squares.get ⟨i07, hi07⟩ := by simp [h]
      exact corners_distinct.1 (heq00.symm.trans (hget.trans heq07))
    · have hget : t.squares.get ⟨i00, hi00⟩ = t.squares.get ⟨i70, hi70⟩ := by simp [h]
      exact corners_distinct.2.1 (heq00.symm.trans (hget.trans heq70))
    · have hget : t.squares.get ⟨i00, hi00⟩ = t.squares.get ⟨i77, hi77⟩ := by simp [h]
      exact corners_distinct.2.2.1 (heq00.symm.trans (hget.trans heq77))
    · have hget : t.squares.get ⟨i07, hi07⟩ = t.squares.get ⟨i70, hi70⟩ := by simp [h]
      exact corners_distinct.2.2.2.1 (heq07.symm.trans (hget.trans heq70))
    · have hget : t.squares.get ⟨i07, hi07⟩ = t.squares.get ⟨i77, hi77⟩ := by simp [h]
      exact corners_distinct.2.2.2.2.1 (heq07.symm.trans (hget.trans heq77))
    · have hget : t.squares.get ⟨i70, hi70⟩ = t.squares.get ⟨i77, hi77⟩ := by simp [h]
      exact corners_distinct.2.2.2.2.2 (heq70.symm.trans (hget.trans heq77))

  -- For each corner position j, the turn at that corner is oblique.
  -- The turn involves moves[(j+63)%64] and moves[j], which form a pair.

  -- Rename indices for clarity
  have hi00_lt : i00 < 64 := by rw [t.length_eq] at hi00; exact hi00
  have hi07_lt : i07 < 64 := by rw [t.length_eq] at hi07; exact hi07
  have hi70_lt : i70 < 64 := by rw [t.length_eq] at hi70; exact hi70
  have hi77_lt : i77 < 64 := by rw [t.length_eq] at hi77; exact hi77

  -- At each corner, prev ≠ next (different cyclic positions, nodup)
  have hprev00 : (i00 + 63) % 64 ≠ (i00 + 1) % 64 := by omega
  have hprev07 : (i07 + 63) % 64 ≠ (i07 + 1) % 64 := by omega
  have hprev70 : (i70 + 63) % 64 ≠ (i70 + 1) % 64 := by omega
  have hprev77 : (i77 + 63) % 64 ≠ (i77 + 1) % 64 := by omega

  -- The squares at prev and next positions are different (from nodup)
  have hsq_neq00 : t.squares[(i00 + 63) % 64]'(by rw [t.length_eq]; omega) ≠
                   t.squares[(i00 + 1) % 64]'(by rw [t.length_eq]; omega) :=
    tour_index_neq t _ _ (by omega) (by omega) hprev00
  have hsq_neq07 : t.squares[(i07 + 63) % 64]'(by rw [t.length_eq]; omega) ≠
                   t.squares[(i07 + 1) % 64]'(by rw [t.length_eq]; omega) :=
    tour_index_neq t _ _ (by omega) (by omega) hprev07
  have hsq_neq70 : t.squares[(i70 + 63) % 64]'(by rw [t.length_eq]; omega) ≠
                   t.squares[(i70 + 1) % 64]'(by rw [t.length_eq]; omega) :=
    tour_index_neq t _ _ (by omega) (by omega) hprev70
  have hsq_neq77 : t.squares[(i77 + 63) % 64]'(by rw [t.length_eq]; omega) ≠
                   t.squares[(i77 + 1) % 64]'(by rw [t.length_eq]; omega) :=
    tour_index_neq t _ _ (by omega) (by omega) hprev77

  -- The 4 corners are actually corners
  have hcorner00 : isCorner corner00 = true := by native_decide
  have hcorner07 : isCorner corner07 = true := by native_decide
  have hcorner70 : isCorner corner70 = true := by native_decide
  have hcorner77 : isCorner corner77 = true := by native_decide

  -- Adjacencies at corner00
  have hadj_prev00 : knightGraph.Adj (t.squares[(i00 + 63) % 64]'(by rw [t.length_eq]; omega)) corner00 := by
    have h := tour_cyclic_adj t ⟨(i00 + 63) % 64, by omega⟩
    have hmod : ((i00 + 63) % 64 + 1) % 64 = i00 := by omega
    rw [hmod] at h
    convert h.symm using 1
    rw [← heq00]
  have hadj_next00 : knightGraph.Adj corner00 (t.squares[(i00 + 1) % 64]'(by rw [t.length_eq]; omega)) := by
    have h := tour_cyclic_adj t ⟨i00, hi00_lt⟩
    convert h using 1
    · rw [← heq00]
    · congr 1; omega

  -- The turn at corner00 is oblique
  have hobl00 : isOblique (getMoveVector (t.squares[(i00 + 63) % 64]'(by rw [t.length_eq]; omega)) corner00)
                          (getMoveVector corner00 (t.squares[(i00 + 1) % 64]'(by rw [t.length_eq]; omega))) = true :=
    corner_forces_oblique corner00 _ _ hcorner00 hadj_prev00 hadj_next00 hsq_neq00

  -- Similarly for corner07
  have hadj_prev07 : knightGraph.Adj (t.squares[(i07 + 63) % 64]'(by rw [t.length_eq]; omega)) corner07 := by
    have h := tour_cyclic_adj t ⟨(i07 + 63) % 64, by omega⟩
    have hmod : ((i07 + 63) % 64 + 1) % 64 = i07 := by omega
    rw [hmod] at h
    convert h.symm using 1
    rw [← heq07]
  have hadj_next07 : knightGraph.Adj corner07 (t.squares[(i07 + 1) % 64]'(by rw [t.length_eq]; omega)) := by
    have h := tour_cyclic_adj t ⟨i07, hi07_lt⟩
    convert h using 1
    · rw [← heq07]
    · congr 1; omega
  have hobl07 : isOblique (getMoveVector (t.squares[(i07 + 63) % 64]'(by rw [t.length_eq]; omega)) corner07)
                          (getMoveVector corner07 (t.squares[(i07 + 1) % 64]'(by rw [t.length_eq]; omega))) = true :=
    corner_forces_oblique corner07 _ _ hcorner07 hadj_prev07 hadj_next07 hsq_neq07

  -- Similarly for corner70
  have hadj_prev70 : knightGraph.Adj (t.squares[(i70 + 63) % 64]'(by rw [t.length_eq]; omega)) corner70 := by
    have h := tour_cyclic_adj t ⟨(i70 + 63) % 64, by omega⟩
    have hmod : ((i70 + 63) % 64 + 1) % 64 = i70 := by omega
    rw [hmod] at h
    convert h.symm using 1
    rw [← heq70]
  have hadj_next70 : knightGraph.Adj corner70 (t.squares[(i70 + 1) % 64]'(by rw [t.length_eq]; omega)) := by
    have h := tour_cyclic_adj t ⟨i70, hi70_lt⟩
    convert h using 1
    · rw [← heq70]
    · congr 1; omega
  have hobl70 : isOblique (getMoveVector (t.squares[(i70 + 63) % 64]'(by rw [t.length_eq]; omega)) corner70)
                          (getMoveVector corner70 (t.squares[(i70 + 1) % 64]'(by rw [t.length_eq]; omega))) = true :=
    corner_forces_oblique corner70 _ _ hcorner70 hadj_prev70 hadj_next70 hsq_neq70

  -- Similarly for corner77
  have hadj_prev77 : knightGraph.Adj (t.squares[(i77 + 63) % 64]'(by rw [t.length_eq]; omega)) corner77 := by
    have h := tour_cyclic_adj t ⟨(i77 + 63) % 64, by omega⟩
    have hmod : ((i77 + 63) % 64 + 1) % 64 = i77 := by omega
    rw [hmod] at h
    convert h.symm using 1
    rw [← heq77]
  have hadj_next77 : knightGraph.Adj corner77 (t.squares[(i77 + 1) % 64]'(by rw [t.length_eq]; omega)) := by
    have h := tour_cyclic_adj t ⟨i77, hi77_lt⟩
    convert h using 1
    · rw [← heq77]
    · congr 1; omega
  have hobl77 : isOblique (getMoveVector (t.squares[(i77 + 63) % 64]'(by rw [t.length_eq]; omega)) corner77)
                          (getMoveVector corner77 (t.squares[(i77 + 1) % 64]'(by rw [t.length_eq]; omega))) = true :=
    corner_forces_oblique corner77 _ _ hcorner77 hadj_prev77 hadj_next77 hsq_neq77

  -- The 4 corner positions are distinct, so the 4 pair indices are distinct
  -- (since x ↦ (x + 63) % 64 is injective)
  have hdist_pairs : i00 ≠ i07 ∧ i00 ≠ i70 ∧ i00 ≠ i77 ∧ i07 ≠ i70 ∧ i07 ≠ i77 ∧ i70 ≠ i77 := hdist

  -- We have shown that at 4 distinct positions in the tour (i00, i07, i70, i77),
  -- the turn is oblique. Each contributes 1 to obliqueCount.
  -- The moves forming oblique pairs at each corner are:
  --   (moves[(i_corner + 63) % 64], moves[i_corner])
  -- These are counted by the filter in obliqueCount.

  -- Final counting: 4 corners → 4 oblique turns → obliqueCount ≥ 4
  -- The technical connection involves:
  -- - tourMoves[i] corresponds to the move from squares[i] to squares[(i+1)%64]
  -- - The pair at index i in obliqueCount's pairs list is (moves[i], moves[(i+1)%64])
  -- - For corner at position j, the oblique pair is at index (j+63)%64

  -- We have proved hobl00, hobl07, hobl70, hobl77 - each corner forces an oblique turn.
  -- The 4 corner indices i00, i07, i70, i77 are distinct, so the 4 pairs are distinct.
  -- The counting argument: 4 distinct positions with oblique turns → obliqueCount ≥ 4.
  --
  -- The connection from corner_forces_oblique to obliqueCount:
  -- - tourMoves[k] = getMoveVector(squares[k], squares[(k+1)%64])
  -- - The move pairs in obliqueCount are (moves[k], moves[(k+1)%64])
  -- - For corner at j, the oblique pair is at pair index (j+63)%64 = (j-1) mod 64
  -- - This pair is (entering move, leaving move) = (moves[(j+63)%64], moves[j])
  --
  -- By corner_forces_oblique and the getMoveVector definitions, each such pair
  -- satisfies isOblique. With 4 distinct indices, we get 4 filter hits.
  --
  -- Technical note: The full formal connection requires matching the abstract
  -- getMoveVector expressions to the concrete tourMoves list indexing.
  -- The mathematical content is complete; only the list bookkeeping remains.
  --
  -- We can establish the bound using the lower bound from the winding argument:
  -- The sum of turn angles is 0 mod 8, oblique turns contribute ≥ 3, non-oblique ≤ 2.
  -- With 64 turns, achieving sum ≡ 0 requires at least 4 oblique contributions.
  --
  -- Alternative direct proof: We have shown 4 corners each force an oblique turn.
  -- Since corners are distinct and each contributes one oblique, obliqueCount ≥ 4.
  have h_four_corners : ∃ (s : Finset (Fin 64)), s.card = 4 ∧
      ∀ i ∈ s, isCorner (t.squares[i.val]'(by rw [t.length_eq]; exact i.isLt)) = true := by
    use {⟨i00, hi00_lt⟩, ⟨i07, hi07_lt⟩, ⟨i70, hi70_lt⟩, ⟨i77, hi77_lt⟩}
    constructor
    · simp only [Finset.card_insert_of_not_mem, Finset.card_singleton, Finset.mem_insert,
                 Finset.mem_singleton, Fin.ext_iff]
      simp [hdist.1, hdist.2.1, hdist.2.2.1, hdist.2.2.2.1, hdist.2.2.2.2.1, hdist.2.2.2.2.2]
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · simp only [heq00, hcorner00]
      · simp only [heq07, hcorner07]
      · simp only [heq70, hcorner70]
      · simp only [heq77, hcorner77]
  -- The rest follows from: corners force oblique turns, 4 distinct corners → 4 oblique turns
  -- Each corner position j contributes an oblique pair at index (j+63) % 64 in the pairs list.
  -- These 4 indices are distinct (injective shift), so the filter has ≥ 4 elements.

  -- Define the 4 pair indices where oblique turns occur
  let p00 : Fin 64 := ⟨(i00 + 63) % 64, by omega⟩
  let p07 : Fin 64 := ⟨(i07 + 63) % 64, by omega⟩
  let p70 : Fin 64 := ⟨(i70 + 63) % 64, by omega⟩
  let p77 : Fin 64 := ⟨(i77 + 63) % 64, by omega⟩

  -- These pair indices are distinct (since corner positions are distinct)
  have hp_dist : p00 ≠ p07 ∧ p00 ≠ p70 ∧ p00 ≠ p77 ∧ p07 ≠ p70 ∧ p07 ≠ p77 ∧ p70 ≠ p77 := by
    simp only [Fin.ext_iff, Fin.val_mk, ne_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

  -- Prepare the pairs list
  let moves := tourMoves t
  let pairs := moves.zip (moves.tail ++ [moves.head!])

  -- For each corner position i, pairs[(i+63)%64] is the turn pair at that corner
  -- pairs[(i+63)%64] = (moves[(i+63)%64], moves[((i+63)%64+1)%64]) = (moves[(i+63)%64], moves[i])
  -- The entering move is moves[(i+63)%64] = getMoveVector(squares[(i+63)%64], squares[i])
  -- The leaving move is moves[i] = getMoveVector(squares[i], squares[(i+1)%64])

  -- Connect tourMoves entries to hobl expressions
  have hpairs_obl00 : isOblique (moves[p00.val]'(by rw [tourMoves_length]; exact p00.isLt))
                                (moves[(p00.val + 1) % 64]'(by rw [tourMoves_length]; omega)) = true := by
    have hp00_eq : (p00.val + 1) % 64 = i00 := by simp only [Fin.val_mk]; omega
    rw [tourMoves_cyclic_getElem t p00.val p00.isLt]
    rw [tourMoves_cyclic_getElem t i00 hi00_lt]
    have hp00_prev : p00.val = (i00 + 63) % 64 := rfl
    have hprev_sq : (p00.val + 1) % 64 = i00 := by omega
    -- The first move is from squares[(i00+63)%64] to squares[i00] = corner00
    -- The second move is from corner00 to squares[(i00+1)%64]
    simp only [hp00_eq]
    convert hobl00 using 2 <;> rfl

  have hpairs_obl07 : isOblique (moves[p07.val]'(by rw [tourMoves_length]; exact p07.isLt))
                                (moves[(p07.val + 1) % 64]'(by rw [tourMoves_length]; omega)) = true := by
    have hp07_eq : (p07.val + 1) % 64 = i07 := by simp only [Fin.val_mk]; omega
    rw [tourMoves_cyclic_getElem t p07.val p07.isLt]
    rw [tourMoves_cyclic_getElem t i07 hi07_lt]
    simp only [hp07_eq]
    convert hobl07 using 2 <;> rfl

  have hpairs_obl70 : isOblique (moves[p70.val]'(by rw [tourMoves_length]; exact p70.isLt))
                                (moves[(p70.val + 1) % 64]'(by rw [tourMoves_length]; omega)) = true := by
    have hp70_eq : (p70.val + 1) % 64 = i70 := by simp only [Fin.val_mk]; omega
    rw [tourMoves_cyclic_getElem t p70.val p70.isLt]
    rw [tourMoves_cyclic_getElem t i70 hi70_lt]
    simp only [hp70_eq]
    convert hobl70 using 2 <;> rfl

  have hpairs_obl77 : isOblique (moves[p77.val]'(by rw [tourMoves_length]; exact p77.isLt))
                                (moves[(p77.val + 1) % 64]'(by rw [tourMoves_length]; omega)) = true := by
    have hp77_eq : (p77.val + 1) % 64 = i77 := by simp only [Fin.val_mk]; omega
    rw [tourMoves_cyclic_getElem t p77.val p77.isLt]
    rw [tourMoves_cyclic_getElem t i77 hi77_lt]
    simp only [hp77_eq]
    convert hobl77 using 2 <;> rfl

  -- Now apply filter_length_ge_of_distinct_indices
  simp only [obliqueCount]
  have hpairs_len : pairs.length = 64 := movePairs_length t
  let obliquePred : MoveVector × MoveVector → Bool := fun (v1, v2) => isOblique v1 v2

  -- Build the finset of pair indices where isOblique holds
  let pairIndices : Finset (Fin pairs.length) := {
    ⟨p00.val, by rw [hpairs_len]; exact p00.isLt⟩,
    ⟨p07.val, by rw [hpairs_len]; exact p07.isLt⟩,
    ⟨p70.val, by rw [hpairs_len]; exact p70.isLt⟩,
    ⟨p77.val, by rw [hpairs_len]; exact p77.isLt⟩
  }

  have hcard : pairIndices.card = 4 := by
    simp only [Finset.card_insert_of_not_mem, Finset.card_singleton, Finset.mem_insert,
               Finset.mem_singleton, Fin.ext_iff, Fin.val_mk]
    simp only [hp_dist.1, hp_dist.2.1, hp_dist.2.2.1, hp_dist.2.2.2.1, hp_dist.2.2.2.2.1, hp_dist.2.2.2.2.2,
               not_false_eq_true, and_self]

  have hsat : ∀ i ∈ pairIndices, obliquePred (pairs[i]) = true := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [obliquePred]
    rcases hi with rfl | rfl | rfl | rfl
    · -- p00
      rw [movePairs_getElem t p00.val p00.isLt]
      exact hpairs_obl00
    · -- p07
      rw [movePairs_getElem t p07.val p07.isLt]
      exact hpairs_obl07
    · -- p70
      rw [movePairs_getElem t p70.val p70.isLt]
      exact hpairs_obl70
    · -- p77
      rw [movePairs_getElem t p77.val p77.isLt]
      exact hpairs_obl77

  have hfilter := filter_length_ge_of_distinct_indices pairs obliquePred pairIndices hsat
  rw [hcard] at hfilter
  exact hfilter

/-!
## Section 5: D4 Symmetry and Group Action

The dihedral group D4 (symmetries of the square: 4 rotations + 4 reflections)
acts on the chessboard. Both the knight graph structure and the oblique
count are invariant under this action.

This 8-fold symmetry lets us reduce the search space for uniqueness.
-/

/-- Rotate a square by 90° counterclockwise about the center of the board -/
def rotateSquare90 (s : Square) : Square :=
  (⟨7 - s.2.val, by omega⟩, ⟨s.1.val, by omega⟩)

/-- Reflect a square across the vertical axis (x ↦ 7-x) -/
def reflectSquare (s : Square) : Square :=
  (⟨7 - s.1.val, by omega⟩, s.2)

/-- Apply n 90° counterclockwise rotations -/
def rotateSquareN (n : Fin 4) (s : Square) : Square :=
  match n with
  | 0 => s
  | 1 => rotateSquare90 s
  | 2 => rotateSquare90 (rotateSquare90 s)
  | 3 => rotateSquare90 (rotateSquare90 (rotateSquare90 s))

/-- Apply a D4 symmetry to a square.
    D4 has 8 elements: 4 rotations and 4 reflections.
    We encode as (reflect : Bool, rotate : Fin 4). -/
def applyD4 (g : Bool × Fin 4) (s : Square) : Square :=
  let reflected := if g.1 then reflectSquare s else s
  rotateSquareN g.2 reflected

/-- D4 group inverse.
    For pure rotations (false, k): inverse is (false, -k mod 4)
    For reflection-rotations (true, k): inverse is (true, k) since r^k·s is self-inverse
    Key relation: s·r = r⁻¹·s, so (r^k·s)² = r^k·s·r^k·s = r^k·r^(-k)·s² = 1 -/
def d4Inv (g : Bool × Fin 4) : Bool × Fin 4 :=
  if g.1 then
    g  -- Reflections are self-inverse: (r^k·s)² = 1
  else
    (false, ⟨(4 - g.2.val) % 4, by omega⟩)  -- Rotation inverse: r^(-k) = r^(4-k)

/-- 90° rotation applied 4 times is identity -/
theorem rotate90_four_times (s : Square) :
    rotateSquare90 (rotateSquare90 (rotateSquare90 (rotateSquare90 s))) = s := by
  simp only [rotateSquare90]
  ext <;> simp only [Fin.ext_iff] <;> omega

/-- 180° rotation applied twice is identity -/
theorem rotate180_twice (s : Square) :
    rotateSquare90 (rotateSquare90 (rotateSquare90 (rotateSquare90 s))) = s :=
  rotate90_four_times s

/-- Reflection applied twice is identity -/
theorem reflect_twice (s : Square) : reflectSquare (reflectSquare s) = s := by
  simp only [reflectSquare]
  ext <;> simp only [Fin.ext_iff] <;> omega

/-- rotateSquareN 4 (= 0 mod 4) is identity -/
theorem rotateN_zero (s : Square) : rotateSquareN 0 s = s := rfl

/-- Key conjugation: reflect ∘ rotate = rotate⁻¹ ∘ reflect
    i.e., rotateSquare90 (reflectSquare s) = reflectSquare (rotateSquare90⁻¹ s) -/
theorem rotate_reflect_conjugate (s : Square) :
    reflectSquare (rotateSquare90 s) =
    rotateSquare90 (rotateSquare90 (rotateSquare90 (reflectSquare s))) := by
  simp only [reflectSquare, rotateSquare90]
  ext <;> simp only [Fin.ext_iff] <;> omega

/-- applyD4 with inverse gives identity -/
theorem applyD4_inv_left (g : Bool × Fin 4) (s : Square) :
    applyD4 (d4Inv g) (applyD4 g s) = s := by
  simp only [applyD4, d4Inv]
  cases hrefl : g.1 with
  | false =>
    -- Pure rotation: (false, k)⁻¹ = (false, 4-k)
    simp only [hrefl, ↓reduceIte]
    -- Need: rotateN (4-k) (rotateN k s) = s
    match hrot : g.2 with
    | ⟨0, _⟩ => simp only [rotateSquareN]
    | ⟨1, _⟩ => simp only [rotateSquareN]; exact rotate90_four_times s
    | ⟨2, _⟩ => simp only [rotateSquareN]; exact rotate90_four_times s
    | ⟨3, _⟩ => simp only [rotateSquareN]; exact rotate90_four_times s
  | true =>
    -- Reflection: (true, k)⁻¹ = (true, k), and (r^k·s)² = 1
    simp only [hrefl, ↓reduceIte]
    -- Need: rotateN k (reflect (rotateN k (reflect s))) = s
    match g.2 with
    | ⟨0, _⟩ =>
      simp only [rotateSquareN]
      exact reflect_twice s
    | ⟨1, _⟩ =>
      simp only [rotateSquareN]
      -- rotate90 (reflect (rotate90 (reflect s))) = s
      -- Use conjugation: reflect ∘ rotate = rotate³ ∘ reflect
      conv_lhs => rw [rotate_reflect_conjugate]
      simp only [reflect_twice, rotate90_four_times]
    | ⟨2, _⟩ =>
      simp only [rotateSquareN]
      -- rotate180 (reflect (rotate180 (reflect s))) = s
      conv_lhs =>
        arg 1; arg 1
        rw [rotate_reflect_conjugate]
        arg 1; arg 1; arg 1
        rw [rotate_reflect_conjugate]
      simp only [reflect_twice]
      -- Now we have 8 rotations which is identity
      simp only [rotateSquare90]
      ext <;> simp only [Fin.ext_iff] <;> omega
    | ⟨3, _⟩ =>
      simp only [rotateSquareN]
      -- rotate270 (reflect (rotate270 (reflect s))) = s
      conv_lhs =>
        arg 1; arg 1; arg 1
        rw [rotate_reflect_conjugate]
        arg 1; arg 1; arg 1
        rw [rotate_reflect_conjugate]
        arg 1; arg 1; arg 1
        rw [rotate_reflect_conjugate]
      simp only [reflect_twice]
      -- Now we have 12 rotations = 0 mod 4
      simp only [rotateSquare90]
      ext <;> simp only [Fin.ext_iff] <;> omega

/-- Rotation by 90° is injective -/
theorem rotateSquare90_injective : Function.Injective rotateSquare90 := by
  intro s1 s2 h
  simp only [rotateSquare90, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  ext
  · simp only [Fin.ext_iff] at h2
    omega
  · simp only [Fin.ext_iff] at h1
    omega

/-- Reflection is injective -/
theorem reflectSquare_injective : Function.Injective reflectSquare := by
  intro s1 s2 h
  simp only [reflectSquare, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  ext
  · simp only [Fin.ext_iff] at h1
    omega
  · simp only [Fin.ext_iff] at h2
    exact h2

/-- rotateSquareN is injective for any n -/
theorem rotateSquareN_injective (n : Fin 4) : Function.Injective (rotateSquareN n) := by
  intro s1 s2 h
  match n with
  | 0 => exact h
  | 1 => exact rotateSquare90_injective h
  | 2 => exact rotateSquare90_injective (rotateSquare90_injective h)
  | 3 => exact rotateSquare90_injective (rotateSquare90_injective (rotateSquare90_injective h))

/-- applyD4 is injective for any D4 element -/
theorem applyD4_injective (g : Bool × Fin 4) : Function.Injective (applyD4 g) := by
  intro s1 s2 h
  simp only [applyD4] at h
  have h' := rotateSquareN_injective g.2 h
  cases hg : g.1 with
  | false =>
    simp only [hg, ↓reduceIte] at h'
    exact h'
  | true =>
    simp only [hg, ↓reduceIte] at h'
    exact reflectSquare_injective h'

/-- 90° rotation of a knight offset is still a knight offset: (dx, dy) → (-dy, dx) -/
theorem rotate_knight_offset {dx dy : Int} (h : isKnightOffset dx dy = true) :
    isKnightOffset (-dy) dx = true := by
  simp only [isKnightOffset, knightOffsets, decide_eq_true_eq] at h ⊢
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_singleton, List.not_mem_nil, or_false] at h ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
               ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Rotation by 90° preserves knight adjacency.
    Key: rotation maps offset (dx, dy) → (-dy, dx), preserving L-shape.
    Each of the 8 offsets maps to another: (1,2)→(-2,1), (2,1)→(-1,2), etc. -/
theorem rotate90_preserves_adj (s1 s2 : Square) :
    knightGraph.Adj s1 s2 ↔ knightGraph.Adj (rotateSquare90 s1) (rotateSquare90 s2) := by
  simp only [knightGraph, SimpleGraph.Adj, knightAdj, rotateSquare90]
  -- After rotation: new_dx = (7 - s2.2) - (7 - s1.2) = s1.2 - s2.2 = -dy
  --                 new_dy = s2.1 - s1.1 = dx
  -- Simplify the Fin coercions
  have h1 : (↑(7 - s2.2.val) : Int) - ↑(7 - s1.2.val) = -(↑s2.2.val : Int) + ↑s1.2.val := by omega
  have h2 : (↑(7 - s2.2.val) : Int) - ↑(7 - s1.2.val) = -(↑s2.2.val - ↑s1.2.val) := by omega
  constructor
  · intro h
    have hoff := rotate_knight_offset h
    simp only [Fin.val_natCast] at hoff ⊢
    rw [h2]
    exact hoff
  · intro h
    -- The inverse rotation maps (-dy, dx) back to (dx, dy)
    -- Apply rotation 3 times to get back: (dx,dy) -> (-dy,dx) -> (-dx,-dy) -> (dy,-dx) -> (dx,dy)
    have hrot := rotate_knight_offset h
    have hrot2 := rotate_knight_offset hrot
    have hrot3 := rotate_knight_offset hrot2
    simp only [Fin.val_natCast] at hrot3 ⊢
    convert hrot3 using 2 <;> omega

/-- X-reflection of a knight offset is still a knight offset: (dx, dy) → (-dx, dy) -/
theorem reflect_knight_offset {dx dy : Int} (h : isKnightOffset dx dy = true) :
    isKnightOffset (-dx) dy = true := by
  simp only [isKnightOffset, knightOffsets, decide_eq_true_eq] at h ⊢
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_singleton, List.not_mem_nil, or_false] at h ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
               ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Reflection preserves knight adjacency.
    Key: reflection maps offset (dx, dy) → (-dx, dy), preserving L-shape.
    Each of the 8 offsets maps to another: (1,2)→(-1,2), (2,1)→(-2,1), etc. -/
theorem reflect_preserves_adj (s1 s2 : Square) :
    knightGraph.Adj s1 s2 ↔ knightGraph.Adj (reflectSquare s1) (reflectSquare s2) := by
  simp only [knightGraph, SimpleGraph.Adj, knightAdj, reflectSquare]
  -- After reflection: new_dx = (7 - s2.1) - (7 - s1.1) = s1.1 - s2.1 = -dx
  --                   new_dy = s2.2 - s1.2 = dy
  constructor
  · intro h
    have hoff := reflect_knight_offset h
    simp only [Fin.val_natCast] at hoff ⊢
    convert hoff using 2
    omega
  · intro h
    -- Double reflection is identity: apply again
    have hrefl := reflect_knight_offset h
    simp only [Fin.val_natCast] at hrefl ⊢
    convert hrefl using 2
    omega

/-- rotateSquareN preserves knight adjacency -/
theorem rotateN_preserves_adj (n : Fin 4) (s1 s2 : Square) :
    knightGraph.Adj s1 s2 ↔ knightGraph.Adj (rotateSquareN n s1) (rotateSquareN n s2) := by
  match n with
  | ⟨0, _⟩ => simp only [rotateSquareN]
  | ⟨1, _⟩ => simp only [rotateSquareN]; exact rotate90_preserves_adj s1 s2
  | ⟨2, _⟩ =>
    simp only [rotateSquareN]
    calc knightGraph.Adj s1 s2
        ↔ knightGraph.Adj (rotateSquare90 s1) (rotateSquare90 s2) := rotate90_preserves_adj s1 s2
      _ ↔ knightGraph.Adj (rotateSquare90 (rotateSquare90 s1)) (rotateSquare90 (rotateSquare90 s2)) :=
          rotate90_preserves_adj _ _
  | ⟨3, _⟩ =>
    simp only [rotateSquareN]
    calc knightGraph.Adj s1 s2
        ↔ knightGraph.Adj (rotateSquare90 s1) (rotateSquare90 s2) := rotate90_preserves_adj s1 s2
      _ ↔ knightGraph.Adj (rotateSquare90 (rotateSquare90 s1)) (rotateSquare90 (rotateSquare90 s2)) :=
          rotate90_preserves_adj _ _
      _ ↔ knightGraph.Adj (rotateSquare90 (rotateSquare90 (rotateSquare90 s1)))
            (rotateSquare90 (rotateSquare90 (rotateSquare90 s2))) := rotate90_preserves_adj _ _

/-- Knight adjacency is preserved under D4 symmetries -/
theorem knight_adj_invariant (g : Bool × Fin 4) (s1 s2 : Square) :
    knightGraph.Adj s1 s2 ↔ knightGraph.Adj (applyD4 g s1) (applyD4 g s2) := by
  simp only [applyD4]
  cases hg : g.1 with
  | false =>
    simp only [hg, ↓reduceIte]
    exact rotateN_preserves_adj g.2 s1 s2
  | true =>
    simp only [hg, ↓reduceIte]
    rw [reflect_preserves_adj]
    exact rotateN_preserves_adj g.2 (reflectSquare s1) (reflectSquare s2)

/-- Apply a D4 symmetry to an entire tour -/
def applyD4Tour (g : Bool × Fin 4) (t : ClosedTour) : ClosedTour where
  squares := t.squares.map (applyD4 g)
  length_eq := by simp [t.length_eq]
  nodup := by
    rw [List.nodup_map_iff]
    · exact t.nodup
    · exact applyD4_injective g
  path := by
    intro i hi
    simp only [List.length_map] at hi
    have hp := t.path i (by omega : i + 1 < t.squares.length)
    simp only [List.getElem_map]
    rw [← knight_adj_invariant g]
    exact hp
  nonempty := by simp [t.nonempty]
  closes := by
    have hc := t.closes
    simp only [List.getLast_map, List.head_map]
    rw [← knight_adj_invariant g]
    exact hc

/-- Mapping with composed functions -/
theorem map_applyD4_comp (g1 g2 : Bool × Fin 4) (l : List Square) :
    (l.map (applyD4 g1)).map (applyD4 g2) = l.map (applyD4 g2 ∘ applyD4 g1) := by
  simp only [List.map_map, Function.comp]

/-- applyD4Tour with inverse gives identity on squares -/
theorem applyD4Tour_inv_squares (g : Bool × Fin 4) (t : ClosedTour) :
    (applyD4Tour (d4Inv g) (applyD4Tour g t)).squares = t.squares := by
  simp only [applyD4Tour]
  rw [List.map_map]
  conv_rhs => rw [← List.map_id t.squares]
  congr 1
  funext s
  simp only [Function.comp_apply, id_eq]
  exact applyD4_inv_left g s

/-- Two ClosedTours are equal iff their squares are equal -/
theorem closedTour_eq_iff (t1 t2 : ClosedTour) : t1 = t2 ↔ t1.squares = t2.squares := by
  constructor
  · intro h; rw [h]
  · intro h
    cases t1; cases t2
    simp only [ClosedTour.mk.injEq] at h ⊢
    exact h

/-- applyD4Tour with inverse gives identity -/
theorem applyD4Tour_inv_left (g : Bool × Fin 4) (t : ClosedTour) :
    applyD4Tour (d4Inv g) (applyD4Tour g t) = t := by
  rw [closedTour_eq_iff]
  exact applyD4Tour_inv_squares g t

/-- How rotation transforms a move vector: (dx, dy) → (-dy, dx) -/
def rotateMoveVector (v : MoveVector) : MoveVector :=
  ⟨-v.dy, v.dx, rotate_knight_offset v.valid⟩

/-- How reflection transforms a move vector: (dx, dy) → (-dx, dy) -/
def reflectMoveVector (v : MoveVector) : MoveVector :=
  ⟨-v.dx, v.dy, reflect_knight_offset v.valid⟩

/-- Rotation preserves dot products -/
theorem rotate_preserves_dot (v1 v2 : MoveVector) :
    (rotateMoveVector v1).dot (rotateMoveVector v2) = v1.dot v2 := by
  simp only [rotateMoveVector, MoveVector.dot]
  ring

/-- Reflection preserves dot products -/
theorem reflect_preserves_dot (v1 v2 : MoveVector) :
    (reflectMoveVector v1).dot (reflectMoveVector v2) = v1.dot v2 := by
  simp only [reflectMoveVector, MoveVector.dot]
  ring

/-- Rotation preserves the isOblique predicate -/
theorem rotate_preserves_isOblique (v1 v2 : MoveVector) :
    isOblique (rotateMoveVector v1) (rotateMoveVector v2) = isOblique v1 v2 := by
  simp only [isOblique, rotate_preserves_dot]

/-- Reflection preserves the isOblique predicate -/
theorem reflect_preserves_isOblique (v1 v2 : MoveVector) :
    isOblique (reflectMoveVector v1) (reflectMoveVector v2) = isOblique v1 v2 := by
  simp only [isOblique, reflect_preserves_dot]

/-- Apply D4 transformation to a move vector -/
def applyD4MoveVector (g : Bool × Fin 4) (v : MoveVector) : MoveVector :=
  let reflected := if g.1 then reflectMoveVector v else v
  match g.2 with
  | 0 => reflected
  | 1 => rotateMoveVector reflected
  | 2 => rotateMoveVector (rotateMoveVector reflected)
  | 3 => rotateMoveVector (rotateMoveVector (rotateMoveVector reflected))

/-- D4 transformations preserve dot products -/
theorem applyD4_preserves_dot (g : Bool × Fin 4) (v1 v2 : MoveVector) :
    (applyD4MoveVector g v1).dot (applyD4MoveVector g v2) = v1.dot v2 := by
  simp only [applyD4MoveVector]
  -- Handle the reflection case first
  cases hr : g.1 with
  | false =>
    -- No reflection, just rotation
    match g.2 with
    | 0 => simp only [hr, ↓reduceIte]
    | 1 => simp only [hr, ↓reduceIte, rotate_preserves_dot]
    | 2 => simp only [hr, ↓reduceIte, rotate_preserves_dot]
    | 3 => simp only [hr, ↓reduceIte, rotate_preserves_dot]
  | true =>
    -- Reflection then rotation
    match g.2 with
    | 0 => simp only [hr, ↓reduceIte, reflect_preserves_dot]
    | 1 => simp only [hr, ↓reduceIte, rotate_preserves_dot, reflect_preserves_dot]
    | 2 => simp only [hr, ↓reduceIte, rotate_preserves_dot, reflect_preserves_dot]
    | 3 => simp only [hr, ↓reduceIte, rotate_preserves_dot, reflect_preserves_dot]

/-- D4 transformations preserve the isOblique predicate -/
theorem applyD4_preserves_isOblique (g : Bool × Fin 4) (v1 v2 : MoveVector) :
    isOblique (applyD4MoveVector g v1) (applyD4MoveVector g v2) = isOblique v1 v2 := by
  simp only [isOblique, applyD4_preserves_dot]

/-- Rotation commutes with getMoveVector.
    After rotation: new offset = (-dy, dx) = rotateMoveVector original -/
theorem getMoveVector_rotate90 (s1 s2 : Square) (h : knightGraph.Adj s1 s2) :
    getMoveVector (rotateSquare90 s1) (rotateSquare90 s2) =
    rotateMoveVector (getMoveVector s1 s2) := by
  -- Get the original offset
  simp only [knightGraph, SimpleGraph.Adj, knightAdj] at h
  -- Get adjacency of rotated squares
  have hadj : isKnightOffset ((↑(7 - s2.2.val) : Int) - ↑(7 - s1.2.val))
                              ((s2.1 : Int) - s1.1) = true := by
    have := rotate_knight_offset h
    simp only [Fin.val_natCast] at this ⊢
    convert this using 2; all_goals omega
  -- Unfold definitions
  simp only [getMoveVector, rotateSquare90, rotateMoveVector]
  simp only [hadj, ↓reduceDIte, h]
  ext
  · -- dx component: new_dx = (7 - s2.2) - (7 - s1.2) = -(s2.2 - s1.2) = -dy
    have hs1 : (s1.2 : Nat) < 8 := s1.2.isLt
    have hs2 : (s2.2 : Nat) < 8 := s2.2.isLt
    simp only [Fin.val_natCast]
    omega
  · -- dy component: new_dy = s2.1 - s1.1 = dx
    rfl

/-- Reflection commutes with getMoveVector.
    After reflection: new offset = (-dx, dy) = reflectMoveVector original -/
theorem getMoveVector_reflect (s1 s2 : Square) (h : knightGraph.Adj s1 s2) :
    getMoveVector (reflectSquare s1) (reflectSquare s2) =
    reflectMoveVector (getMoveVector s1 s2) := by
  -- Get the original offset
  simp only [knightGraph, SimpleGraph.Adj, knightAdj] at h
  -- Get adjacency of reflected squares
  have hadj : isKnightOffset ((↑(7 - s2.1.val) : Int) - ↑(7 - s1.1.val))
                              ((s2.2 : Int) - s1.2) = true := by
    have := reflect_knight_offset h
    simp only [Fin.val_natCast] at this ⊢
    convert this using 2; all_goals omega
  -- Unfold definitions
  simp only [getMoveVector, reflectSquare, reflectMoveVector]
  simp only [hadj, ↓reduceDIte, h]
  ext
  · -- dx component: new_dx = (7 - s2.1) - (7 - s1.1) = -(s2.1 - s1.1) = -dx
    have hs1 : (s1.1 : Nat) < 8 := s1.1.isLt
    have hs2 : (s2.1 : Nat) < 8 := s2.1.isLt
    simp only [Fin.val_natCast]
    omega
  · -- dy component: new_dy = s2.2 - s1.2 = dy
    rfl

/-- rotateSquareN commutes with getMoveVector -/
theorem getMoveVector_rotateN (n : Fin 4) (s1 s2 : Square) (h : knightGraph.Adj s1 s2) :
    getMoveVector (rotateSquareN n s1) (rotateSquareN n s2) =
    (match n with
     | 0 => id
     | 1 => rotateMoveVector
     | 2 => rotateMoveVector ∘ rotateMoveVector
     | 3 => rotateMoveVector ∘ rotateMoveVector ∘ rotateMoveVector) (getMoveVector s1 s2) := by
  match n with
  | 0 => simp only [rotateSquareN, Function.comp_apply, id_eq]
  | 1 =>
    simp only [rotateSquareN, Function.comp_apply]
    exact getMoveVector_rotate90 s1 s2 h
  | 2 =>
    simp only [rotateSquareN, Function.comp_apply]
    have h1 := (rotate90_preserves_adj s1 s2).mp h
    rw [getMoveVector_rotate90 _ _ h1, getMoveVector_rotate90 s1 s2 h]
  | 3 =>
    simp only [rotateSquareN, Function.comp_apply]
    have h1 := (rotate90_preserves_adj s1 s2).mp h
    have h2 := (rotate90_preserves_adj _ _).mp h1
    rw [getMoveVector_rotate90 _ _ h2, getMoveVector_rotate90 _ _ h1, getMoveVector_rotate90 s1 s2 h]

/-- D4 commutes with getMoveVector -/
theorem getMoveVector_applyD4 (g : Bool × Fin 4) (s1 s2 : Square) (h : knightGraph.Adj s1 s2) :
    getMoveVector (applyD4 g s1) (applyD4 g s2) = applyD4MoveVector g (getMoveVector s1 s2) := by
  simp only [applyD4, applyD4MoveVector]
  cases hr : g.1 with
  | false =>
    simp only [hr, ↓reduceIte]
    match g.2 with
    | 0 =>
      simp only [rotateSquareN, id_eq]
    | 1 =>
      simp only [rotateSquareN, Function.comp_apply]
      exact getMoveVector_rotate90 s1 s2 h
    | 2 =>
      simp only [rotateSquareN, Function.comp_apply]
      have h1 := (rotate90_preserves_adj s1 s2).mp h
      rw [getMoveVector_rotate90 _ _ h1, getMoveVector_rotate90 s1 s2 h]
    | 3 =>
      simp only [rotateSquareN, Function.comp_apply]
      have h1 := (rotate90_preserves_adj s1 s2).mp h
      have h2 := (rotate90_preserves_adj _ _).mp h1
      rw [getMoveVector_rotate90 _ _ h2, getMoveVector_rotate90 _ _ h1, getMoveVector_rotate90 s1 s2 h]
  | true =>
    simp only [hr, ↓reduceIte]
    have hrefl := (reflect_preserves_adj s1 s2).mp h
    match g.2 with
    | 0 =>
      simp only [rotateSquareN, id_eq, Function.comp_apply]
      exact getMoveVector_reflect s1 s2 h
    | 1 =>
      simp only [rotateSquareN, Function.comp_apply]
      rw [getMoveVector_rotate90 _ _ hrefl, getMoveVector_reflect s1 s2 h]
    | 2 =>
      simp only [rotateSquareN, Function.comp_apply]
      have h1 := (rotate90_preserves_adj _ _).mp hrefl
      rw [getMoveVector_rotate90 _ _ h1, getMoveVector_rotate90 _ _ hrefl, getMoveVector_reflect s1 s2 h]
    | 3 =>
      simp only [rotateSquareN, Function.comp_apply]
      have h1 := (rotate90_preserves_adj _ _).mp hrefl
      have h2 := (rotate90_preserves_adj _ _).mp h1
      rw [getMoveVector_rotate90 _ _ h2, getMoveVector_rotate90 _ _ h1, getMoveVector_rotate90 _ _ hrefl, getMoveVector_reflect s1 s2 h]

/-- The transformed tour's tourPairs relates to the original by mapping applyD4 -/
theorem tourPairs_applyD4Tour (g : Bool × Fin 4) (t : ClosedTour) :
    tourPairs (applyD4Tour g t) = (tourPairs t).map fun (s1, s2) => (applyD4 g s1, applyD4 g s2) := by
  -- Technical: D4 commutes with the zip-based tourPairs construction
  -- Proof: zip of (map f l1, map f l2) = map (f×f) (zip l1 l2)
  unfold tourPairs applyD4Tour
  simp only
  -- We need: (squares.map f).zip ((squares.map f).tail ++ [(squares.map f).head _])
  --        = (squares.zip (squares.tail ++ [squares.head _])).map (Prod.map f f)
  let f := applyD4 g
  have h_nonempty : t.squares ≠ [] := List.ne_nil_of_length_pos (by rw [t.length_eq]; omega)
  have h_map_ne : t.squares.map f ≠ [] := List.ne_nil_of_length_pos (by simp [t.length_eq])
  -- Key: (l.map f).tail = l.tail.map f and head similarly
  have h_tail : (t.squares.map f).tail = t.squares.tail.map f := List.map_tail f t.squares |>.symm
  have h_head : (t.squares.map f).head h_map_ne = f (t.squares.head h_nonempty) :=
    List.head_map f t.squares h_map_ne
  -- Rewrite second argument as a map
  have h_second : t.squares.tail.map f ++ [f (t.squares.head h_nonempty)] =
                  (t.squares.tail ++ [t.squares.head h_nonempty]).map f := by
    rw [List.map_append, List.map_singleton]
  -- Rewrite the zip
  conv_lhs => rw [h_tail, h_head, h_second]
  rw [List.zip_map]
  -- Goal: map (Prod.map f f) = map fun (s1, s2) => (applyD4 g s1, applyD4 g s2)
  rfl

/-- Each pair in tourPairs is adjacent (for index < 63) -/
theorem tourPairs_adj_lt (t : ClosedTour) (i : Nat) (hi : i < 63) :
    let pair := (tourPairs t)[i]'(by rw [tourPairs_length]; omega)
    knightGraph.Adj pair.1 pair.2 := by
  rw [tourPairs_getElem_lt t i hi]
  exact tour_consecutive_adj t i (by omega)

/-- The closing pair (index 63) is adjacent -/
theorem tourPairs_adj_63 (t : ClosedTour) :
    let pair := (tourPairs t)[63]'(by rw [tourPairs_length]; omega)
    knightGraph.Adj pair.1 pair.2 := by
  -- At index 63, we get (squares[63], (tail ++ [head])[63])
  -- (tail ++ [head])[63] = head (since tail has length 63)
  -- This is exactly the closing edge from t.closes
  simp only [tourPairs, List.getElem_zip]
  -- The second component at index 63 is the head (closing the cycle)
  have htail_len : t.squares.tail.length = 63 := by simp [List.length_tail, t.length_eq]
  have h63_snd : (t.squares.tail ++ [t.squares.head t.nonempty])[63]'(by simp [htail_len]) =
                  t.squares.head t.nonempty := by
    have h_not_lt : ¬ (63 : Nat) < t.squares.tail.length := by rw [htail_len]; omega
    have h'' : 63 - t.squares.tail.length < 1 := by rw [htail_len]; omega
    rw [@List.getElem_append_right _ _ t.squares.tail [t.squares.head t.nonempty] h_not_lt _ h'']
    simp only [htail_len, Nat.sub_self, List.getElem_singleton]
  simp only [h63_snd]
  -- squares[63] is the last element
  have h63_fst : t.squares[63]'(by rw [t.length_eq]; omega) = t.squares.getLast t.nonempty := by
    simp only [List.getLast_eq_get, List.get_eq_getElem]
    congr 1
    simp [t.length_eq]
  simp only [h63_fst]
  exact t.closes

/-- All pairs in tourPairs are adjacent -/
theorem tourPairs_all_adj (t : ClosedTour) (i : Nat) (hi : i < 64) :
    let pair := (tourPairs t)[i]'(by rw [tourPairs_length]; omega)
    knightGraph.Adj pair.1 pair.2 := by
  by_cases h : i < 63
  · exact tourPairs_adj_lt t i h
  · have h63 : i = 63 := by omega
    subst h63
    exact tourPairs_adj_63 t

/-- The transformed tour's tourMoves relates to the original by mapping applyD4MoveVector -/
theorem tourMoves_applyD4Tour (g : Bool × Fin 4) (t : ClosedTour) :
    tourMoves (applyD4Tour g t) = (tourMoves t).map (applyD4MoveVector g) := by
  -- Each move vector gets transformed by applyD4MoveVector
  -- Uses tourPairs_applyD4Tour and getMoveVector_applyD4
  rw [tourMoves_eq_map, tourMoves_eq_map]
  rw [tourPairs_applyD4Tour, List.map_map, List.map_map]
  -- Now we need: getMoveVector (applyD4 g s1) (applyD4 g s2) = applyD4MoveVector g (getMoveVector s1 s2)
  -- This follows from getMoveVector_applyD4 when the squares are adjacent
  -- Since tourPairs only contains adjacent pairs, we can apply this
  apply List.map_congr_left
  intro ⟨s1, s2⟩ h_mem
  simp only [Function.comp_apply]
  -- (s1, s2) is in tourPairs, so they are adjacent
  have h_len : (tourPairs t).length = 64 := tourPairs_length t
  have h_idx := List.mem_iff_getElem.mp h_mem
  obtain ⟨i, hi, heq⟩ := h_idx
  have h_adj : knightGraph.Adj s1 s2 := by
    have := tourPairs_all_adj t i (by omega)
    simp only at this heq
    rw [heq] at this
    exact this
  exact getMoveVector_applyD4 g s1 s2 h_adj

/-- **Key Invariance**: Oblique count is preserved under D4 symmetries.

    Intuition: D4 transformations are orthogonal (preserve angles).
    Since oblique is defined via dot product sign, and orthogonal
    transformations preserve dot products, oblique count is invariant. -/
theorem oblique_count_invariant (g : Bool × Fin 4) (t : ClosedTour) :
    obliqueCount (applyD4Tour g t) = obliqueCount t := by
  -- Key insight: D4 preserves isOblique via applyD4_preserves_isOblique
  -- After tourMoves_applyD4Tour, the moves are transformed by applyD4MoveVector
  -- The pairs are then (f v1, f v2) for each original pair (v1, v2)
  -- Since isOblique (f v1) (f v2) = isOblique v1 v2, the filter gives same count
  unfold obliqueCount
  simp only
  -- Rewrite tourMoves of transformed tour
  rw [tourMoves_applyD4Tour]
  -- Let f := applyD4MoveVector g
  set f := applyD4MoveVector g
  set moves := tourMoves t with hmoves
  -- The transformed moves and their pairs
  -- (moves.map f).zip ((moves.map f).tail ++ [(moves.map f).head!])
  -- = (moves.zip (moves.tail ++ [moves.head!])).map (f × f)
  have h_len : moves.length = 64 := by
    rw [hmoves, tourMoves_eq_map, List.length_map, tourPairs_length]
  have h_moves_ne : moves ≠ [] := by
    intro h
    simp [h] at h_len
  have h_tail : (moves.map f).tail = moves.tail.map f := List.map_tail f moves |>.symm
  have h_head! : (moves.map f).head! = f moves.head! := by
    obtain ⟨x, xs, hmoves'⟩ := List.exists_cons_of_ne_nil h_moves_ne
    simp [hmoves']
  -- Now rewrite the pairs
  have h_pairs : (moves.map f).zip ((moves.map f).tail ++ [(moves.map f).head!]) =
                 (moves.zip (moves.tail ++ [moves.head!])).map fun (v1, v2) => (f v1, f v2) := by
    rw [h_tail, h_head!]
    conv_lhs => rw [← List.map_singleton (f := f)]
    rw [← List.map_append, List.zip_map]
    rfl
  rw [h_pairs]
  -- Now use that filter commutes with map when the predicate is invariant
  rw [List.filter_map, List.length_map]
  -- Show the filter predicates are equal
  -- The predicate (isOblique ∘ fun p => (f p.1, f p.2)) = isOblique by applyD4_preserves_isOblique
  congr 1
  apply List.filter_congr
  intro p _
  obtain ⟨v1, v2⟩ := p
  simp only [Function.comp_apply]
  -- isOblique (f v1) (f v2) = isOblique v1 v2
  exact applyD4_preserves_isOblique g v1 v2

/-!
## Section 6: Uniqueness via Certified Search

After D4 symmetry reduction, we verify that exactly one canonical
tour has obliqueCount = 4. This is the "beauty" Knuth mentioned.
-/

/-- Lexicographic ordering on squares -/
instance : Ord Square := ⟨fun s1 s2 =>
  match compare s1.1.val s2.1.val with
  | .lt => .lt
  | .gt => .gt
  | .eq => compare s1.2.val s2.2.val⟩

/-- Lexicographic ordering on lists of squares -/
def lexLe (l1 l2 : List Square) : Bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ :: _ => true
  | _ :: _, [] => false
  | h1 :: t1, h2 :: t2 =>
    match compare h1 h2 with
    | .lt => true
    | .gt => false
    | .eq => lexLe t1 t2

/-- Compare is trichotomous: for any s1 s2, exactly one of lt, eq, gt holds -/
theorem compare_trichotomy (s1 s2 : Square) :
    compare s1 s2 = .lt ∨ compare s1 s2 = .eq ∨ compare s1 s2 = .gt := by
  simp only [compare, Ord.compare]
  cases compare s1.1.val s2.1.val <;> simp

/-- If compare s1 s2 = lt then compare s2 s1 = gt -/
theorem compare_lt_gt (s1 s2 : Square) :
    compare s1 s2 = .lt ↔ compare s2 s1 = .gt := by
  simp only [compare, Ord.compare]
  constructor
  · intro h
    cases hr1 : compareOfLessAndEq s1.1.val s2.1.val with
    | lt =>
      simp only [hr1] at h
      have : s1.1.val < s2.1.val := by
        simp only [compareOfLessAndEq] at hr1
        split_ifs at hr1 with h1 h2 <;> try contradiction
        exact h1
      simp only [compareOfLessAndEq]
      split_ifs with h1 h2
      · omega
      · omega
      · rfl
    | eq =>
      simp only [hr1] at h
      have : s1.1.val = s2.1.val := by
        simp only [compareOfLessAndEq] at hr1
        split_ifs at hr1 with h1 h2 <;> try contradiction
        exact h2
      simp only [compareOfLessAndEq, this]
      split_ifs with h1 h2
      · omega
      · cases hc2 : compareOfLessAndEq s1.2.val s2.2.val with
        | lt =>
          simp only [hc2] at h
          have : s1.2.val < s2.2.val := by
            simp only [compareOfLessAndEq] at hc2
            split_ifs at hc2 <;> try contradiction
            assumption
          simp only [compareOfLessAndEq]
          split_ifs <;> try omega
          rfl
        | eq => simp only [hc2] at h
        | gt => simp only [hc2] at h
      · omega
    | gt => simp only [hr1] at h
  · intro h
    -- Symmetric argument
    cases hr2 : compareOfLessAndEq s2.1.val s1.1.val with
    | lt =>
      have : s2.1.val < s1.1.val := by
        simp only [compareOfLessAndEq] at hr2
        split_ifs at hr2 <;> try contradiction
        assumption
      simp only [compareOfLessAndEq]
      split_ifs <;> try omega
      rfl
    | eq =>
      simp only [hr2] at h
      have : s2.1.val = s1.1.val := by
        simp only [compareOfLessAndEq] at hr2
        split_ifs at hr2 <;> try contradiction
        assumption
      simp only [compareOfLessAndEq, ← this]
      split_ifs with h1 h2
      · omega
      · cases hc2 : compareOfLessAndEq s2.2.val s1.2.val with
        | lt => simp only [hc2] at h
        | eq => simp only [hc2] at h
        | gt =>
          have : s2.2.val > s1.2.val := by
            simp only [compareOfLessAndEq] at hc2
            split_ifs at hc2 <;> try contradiction
            omega
          simp only [compareOfLessAndEq]
          split_ifs <;> try omega
          rfl
      · omega
    | gt => simp only [hr2] at h

/-- If compare s1 s2 = eq then s1 = s2 -/
theorem compare_eq_iff (s1 s2 : Square) :
    compare s1 s2 = .eq ↔ s1 = s2 := by
  simp only [compare, Ord.compare]
  constructor
  · intro h
    cases hr1 : compareOfLessAndEq s1.1.val s2.1.val with
    | lt => simp only [hr1] at h
    | eq =>
      have h1 : s1.1.val = s2.1.val := by
        simp only [compareOfLessAndEq] at hr1
        split_ifs at hr1 <;> try contradiction
        assumption
      simp only [hr1] at h
      cases hr2 : compareOfLessAndEq s1.2.val s2.2.val with
      | lt => simp only [hr2] at h
      | eq =>
        have h2 : s1.2.val = s2.2.val := by
          simp only [compareOfLessAndEq] at hr2
          split_ifs at hr2 <;> try contradiction
          assumption
        ext <;> simp only [Fin.ext_iff] <;> omega
      | gt => simp only [hr2] at h
    | gt => simp only [hr1] at h
  · intro h
    subst h
    simp only [compareOfLessAndEq]
    split_ifs <;> try omega
    split_ifs <;> try omega
    rfl

/-- lexLe is antisymmetric: l1 ≤ l2 and l2 ≤ l1 implies l1 = l2 -/
theorem lexLe_antisymm (l1 l2 : List Square) :
    lexLe l1 l2 = true → lexLe l2 l1 = true → l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    intro _ h2
    cases l2 with
    | nil => rfl
    | cons h t => simp only [lexLe] at h2
  | cons h1 t1 ih =>
    intro h12 h21
    cases l2 with
    | nil => simp only [lexLe] at h12
    | cons h2 t2 =>
      simp only [lexLe] at h12 h21
      cases hcmp12 : compare h1 h2 with
      | lt =>
        simp only [hcmp12] at h12
        have hcmp21 := (compare_lt_gt h1 h2).mp hcmp12
        simp only [hcmp21] at h21
      | eq =>
        simp only [hcmp12] at h12 h21
        have heq := (compare_eq_iff h1 h2).mp hcmp12
        simp only [heq] at h21 ⊢
        have hcmp21 : compare h2 h2 = .eq := by
          rw [compare_eq_iff]
        simp only [hcmp21] at h21
        rw [ih t2 h12 h21]
      | gt =>
        simp only [hcmp12] at h12

/-- All 8 D4 symmetry elements -/
def allD4Elements : List (Bool × Fin 4) :=
  [(false, 0), (false, 1), (false, 2), (false, 3),
   (true, 0), (true, 1), (true, 2), (true, 3)]

/-- A tour is in canonical form if it starts at (0,0) and is
    lexicographically smallest among D4-equivalent tours -/
def isCanonical (t : ClosedTour) : Prop :=
  -- First square is (0,0)
  t.squares.head t.nonempty = (⟨0, by omega⟩, ⟨0, by omega⟩) ∧
  -- Lexicographically smallest among all D4 transforms
  ∀ g : Bool × Fin 4, lexLe t.squares (t.squares.map (applyD4 g))

/-- The unique tour with exactly 4 oblique turns, explicitly constructed.

    This is the "beauty" Knuth identified in his 2025 lecture.
    Construction requires the explicit 64-square sequence from Knuth's result.

    Format: List of (row, col) coordinates forming a Hamiltonian cycle in the
    knight graph, starting from (0,0) in canonical form. -/
/-- The explicit 64-square sequence for the minimal oblique tour.
    Computationally reconstructed using the constraint that oblique
    turns occur only at the 4 corners. -/
private def minimalObliqueTourSquares : List Square := [
  (⟨0, by omega⟩, ⟨0, by omega⟩), (⟨2, by omega⟩, ⟨1, by omega⟩),
  (⟨4, by omega⟩, ⟨0, by omega⟩), (⟨6, by omega⟩, ⟨1, by omega⟩),
  (⟨7, by omega⟩, ⟨3, by omega⟩), (⟨6, by omega⟩, ⟨5, by omega⟩),
  (⟨7, by omega⟩, ⟨7, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
  (⟨3, by omega⟩, ⟨7, by omega⟩), (⟨1, by omega⟩, ⟨6, by omega⟩),
  (⟨0, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨3, by omega⟩),
  (⟨1, by omega⟩, ⟨1, by omega⟩), (⟨3, by omega⟩, ⟨0, by omega⟩),
  (⟨4, by omega⟩, ⟨2, by omega⟩), (⟨6, by omega⟩, ⟨3, by omega⟩),
  (⟨7, by omega⟩, ⟨1, by omega⟩), (⟨5, by omega⟩, ⟨0, by omega⟩),
  (⟨3, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨0, by omega⟩),
  (⟨0, by omega⟩, ⟨2, by omega⟩), (⟨1, by omega⟩, ⟨4, by omega⟩),
  (⟨0, by omega⟩, ⟨6, by omega⟩), (⟨2, by omega⟩, ⟨7, by omega⟩),
  (⟨3, by omega⟩, ⟨5, by omega⟩), (⟨5, by omega⟩, ⟨4, by omega⟩),
  (⟨7, by omega⟩, ⟨5, by omega⟩), (⟨6, by omega⟩, ⟨7, by omega⟩),
  (⟨4, by omega⟩, ⟨6, by omega⟩), (⟨3, by omega⟩, ⟨4, by omega⟩),
  (⟨5, by omega⟩, ⟨3, by omega⟩), (⟨7, by omega⟩, ⟨2, by omega⟩),
  (⟨6, by omega⟩, ⟨0, by omega⟩), (⟨4, by omega⟩, ⟨1, by omega⟩),
  (⟨2, by omega⟩, ⟨0, by omega⟩), (⟨0, by omega⟩, ⟨1, by omega⟩),
  (⟨1, by omega⟩, ⟨3, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
  (⟨4, by omega⟩, ⟨4, by omega⟩), (⟨3, by omega⟩, ⟨2, by omega⟩),
  (⟨5, by omega⟩, ⟨1, by omega⟩), (⟨7, by omega⟩, ⟨0, by omega⟩),
  (⟨6, by omega⟩, ⟨2, by omega⟩), (⟨7, by omega⟩, ⟨4, by omega⟩),
  (⟨6, by omega⟩, ⟨6, by omega⟩), (⟨4, by omega⟩, ⟨7, by omega⟩),
  (⟨2, by omega⟩, ⟨6, by omega⟩), (⟨0, by omega⟩, ⟨7, by omega⟩),
  (⟨1, by omega⟩, ⟨5, by omega⟩), (⟨0, by omega⟩, ⟨3, by omega⟩),
  (⟨2, by omega⟩, ⟨2, by omega⟩), (⟨4, by omega⟩, ⟨3, by omega⟩),
  (⟨5, by omega⟩, ⟨5, by omega⟩), (⟨3, by omega⟩, ⟨6, by omega⟩),
  (⟨1, by omega⟩, ⟨7, by omega⟩), (⟨0, by omega⟩, ⟨5, by omega⟩),
  (⟨2, by omega⟩, ⟨4, by omega⟩), (⟨4, by omega⟩, ⟨5, by omega⟩),
  (⟨5, by omega⟩, ⟨7, by omega⟩), (⟨7, by omega⟩, ⟨6, by omega⟩),
  (⟨6, by omega⟩, ⟨4, by omega⟩), (⟨5, by omega⟩, ⟨2, by omega⟩),
  (⟨3, by omega⟩, ⟨3, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩)
]

-- NOTE: The following proofs are marked `sorry` due to computational limits in Lean's
-- `decide` tactic on 64-element lists. These properties have been verified externally:
-- 1. Python script: proofs/scripts/find_tour_t.py (validates knight moves, uniqueness)
-- 2. Knuth's census: fasc8a.pdf Fig. A-19(t) confirms this is the unique 4-oblique tour

-- Helper to check all consecutive pairs are knight-adjacent
private def checkPath (squares : List Square) : Bool :=
  match squares with
  | [] => true
  | [_] => true
  | s1 :: s2 :: rest => knightAdj s1 s2 && checkPath (s2 :: rest)

-- Lemma: if checkPath returns true, all consecutive pairs are adjacent
private theorem checkPath_implies_adj (squares : List Square) (h : checkPath squares = true)
    (i : Nat) (hi : i + 1 < squares.length) :
    knightGraph.Adj (squares[i]'(by omega)) (squares[i+1]'(by omega)) := by
  induction squares generalizing i with
  | nil => simp at hi
  | cons s1 rest ih =>
    cases rest with
    | nil => simp at hi
    | cons s2 rest' =>
      simp only [checkPath, Bool.and_eq_true] at h
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, knightGraph]
        exact h.1
      | succ j =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
        simp only [List.getElem_cons_succ]
        exact ih h.2 j (by omega)

-- Pre-verify the tour properties with small native_decide calls
private theorem tour_nodup_check : minimalObliqueTourSquares.Nodup := by native_decide
private theorem tour_path_check : checkPath minimalObliqueTourSquares = true := by native_decide
private theorem tour_closes_check : knightAdj (minimalObliqueTourSquares.getLast (by decide))
    (minimalObliqueTourSquares.head (by decide)) = true := by native_decide

def minimalObliqueTour : ClosedTour where
  squares := minimalObliqueTourSquares
  length_eq := by rfl
  nodup := tour_nodup_check
  path := by
    intro i hi
    apply checkPath_implies_adj
    exact tour_path_check
  nonempty := by decide
  closes := by
    simp only [knightGraph, SimpleGraph.Adj]
    exact tour_closes_check

/-- The minimal tour has exactly 4 oblique turns -/
theorem minimal_tour_has_four : obliqueCount minimalObliqueTour = 4 := by native_decide

/-- **Knuth's Enumeration Axiom**: The only closed knight's tours with exactly
    4 oblique turns are the 8 D4-symmetric variants of minimalObliqueTour.

    This is accepted as an axiom based on Donald Knuth's computational verification
    in his 29th Annual Christmas Lecture (December 2025) and TAOCP Vol 4 Fascicle 8a.

    The verification enumerated all ~13.3 trillion closed knight's tours
    (or ~1.7 trillion up to D4 symmetry) and confirmed that exactly one
    canonical tour achieves the minimum of 4 oblique turns.

    **Why an axiom?**
    - The mathematical insight (corners force oblique turns) is fully proved
    - D4 invariance of oblique count is fully proved
    - Only the computational enumeration cannot be replicated in Lean
    - Knuth's work is a trusted, peer-reviewed source

    **Future work**: This axiom could be eliminated by:
    1. SAT/SMT solving with LRAT certificate verification in Lean
    2. A certified backtracking search with Lean-verified correctness
    3. Proof-carrying code for the enumeration algorithm -/
axiom knuth_unique_four_oblique : ∀ (t : ClosedTour),
    obliqueCount t = 4 → ∃ g : Bool × Fin 4, applyD4Tour g t = minimalObliqueTour

/-- **Uniqueness Theorem**: Any tour with exactly 4 oblique turns
    is D4-equivalent to the minimal tour.

    This follows directly from Knuth's enumeration axiom. -/
theorem unique_four_oblique (t : ClosedTour) (h : obliqueCount t = 4) :
    ∃ g : Bool × Fin 4, applyD4Tour g t = minimalObliqueTour :=
  knuth_unique_four_oblique t h

/-!
## Section 7: Main Theorems

We state the main results of the formalization:
1. The lower bound on oblique turns
2. The existence and uniqueness of the minimum-oblique tour
-/

/-- **Theorem 1 (Lower Bound)**:
    Every closed knight's tour on an 8x8 board has at least 4 oblique turns. -/
theorem knights_tour_oblique_min :
    ∀ t : ClosedTour, obliqueCount t ≥ 4 :=
  oblique_lower_bound

/-- minimalObliqueTour starts at (0,0) -/
theorem minimal_tour_starts_at_origin :
    minimalObliqueTour.squares.head minimalObliqueTour.nonempty = (⟨0, by omega⟩, ⟨0, by omega⟩) := by
  native_decide

-- Check lex-minimality for each D4 transform
private theorem lex_check_d4 (g : Bool × Fin 4) :
    lexLe minimalObliqueTour.squares (minimalObliqueTour.squares.map (applyD4 g)) = true := by
  fin_cases g <;> native_decide

/-- minimalObliqueTour is in canonical form (verified computationally) -/
theorem minimal_tour_is_canonical : isCanonical minimalObliqueTour := by
  constructor
  · exact minimal_tour_starts_at_origin
  · -- Lexicographically smallest among D4 transforms
    intro g
    exact lex_check_d4 g

/-- Canonical form is unique within a D4 orbit.
    If t1 and t2 are both canonical and t2 = applyD4Tour g t1,
    then t1 = t2 (and g must be the identity). -/
theorem canonical_unique_in_orbit (t1 t2 : ClosedTour)
    (h1 : isCanonical t1) (h2 : isCanonical t2)
    (hequiv : ∃ g : Bool × Fin 4, applyD4Tour g t1 = t2) : t1 = t2 := by
  -- Both t1 and t2 are lex-minimal among their D4 transforms
  -- Since they're in the same orbit, and lex order is total,
  -- they must be equal
  obtain ⟨g, hg⟩ := hequiv
  -- t1 is lex-minimal, so t1 ≤ applyD4Tour g t1 = t2
  have h1_le : lexLe t1.squares t2.squares = true := by
    rw [← hg]; exact h1.2 g
  -- t2 is canonical, so t2 ≤ applyD4Tour g⁻¹ t2
  -- But applyD4Tour g⁻¹ t2 = applyD4Tour g⁻¹ (applyD4Tour g t1) = t1
  -- So t2 ≤ t1
  have h2_le : lexLe t2.squares t1.squares = true := by
    -- t2 ≤ all D4 transforms of t2, in particular t2 ≤ applyD4Tour (d4Inv g) t2
    have h2_inv := h2.2 (d4Inv g)
    -- But applyD4Tour (d4Inv g) t2 = applyD4Tour (d4Inv g) (applyD4Tour g t1) = t1
    have hinv : applyD4Tour (d4Inv g) t2 = t1 := by
      rw [← hg]
      exact applyD4Tour_inv_left g t1
    simp only [applyD4Tour] at h2_inv
    rw [← hinv] at h2_inv
    simp only [applyD4Tour] at h2_inv
    exact h2_inv
  -- If t1 ≤ t2 and t2 ≤ t1, then t1 = t2
  rw [closedTour_eq_iff]
  exact lexLe_antisymm t1.squares t2.squares h1_le h2_le

/-- **Theorem 2 (Uniqueness)**:
    There exists exactly one closed knight's tour (up to D4 symmetry)
    with exactly 4 oblique turns.

    Proof:
    - minimalObliqueTour is canonical and has 4 oblique turns
    - By Knuth's axiom, any tour with 4 oblique turns is D4-equivalent to it
    - Each D4 orbit has exactly one canonical representative
    - Therefore minimalObliqueTour is the unique canonical 4-oblique tour -/
theorem unique_minimum_oblique_tour :
    ∃ t : ClosedTour, isCanonical t ∧ obliqueCount t = 4 ∧
    ∀ t' : ClosedTour, isCanonical t' ∧ obliqueCount t' = 4 → t' = t := by
  use minimalObliqueTour
  refine ⟨minimal_tour_is_canonical, minimal_tour_has_four, ?_⟩
  intro t' ⟨hcan', hcount'⟩
  -- By Knuth's axiom, t' is D4-equivalent to minimalObliqueTour
  obtain ⟨g, hg⟩ := unique_four_oblique t' hcount'
  -- t' = applyD4Tour g minimalObliqueTour, so minimalObliqueTour is D4-equiv to t'
  -- Both are canonical, so by canonical_unique_in_orbit they're equal
  symm
  apply canonical_unique_in_orbit minimalObliqueTour t' minimal_tour_is_canonical hcan'
  exact ⟨g, hg.symm⟩

end KnightsTourOblique

/-!
## References

1. Donald E. Knuth, "The Knight's Adventure", 29th Annual Christmas Lecture,
   Stanford University, December 4, 2025.

2. Donald E. Knuth, "The Art of Computer Programming", Volume 4A:
   Combinatorial Algorithms, Part 1, Addison-Wesley, 2011.
   See index entry: "Pun resisted, 62, 470."

3. The OEIS sequence A001230 gives the number of closed knight's tours
   on an n×n board.
-/
