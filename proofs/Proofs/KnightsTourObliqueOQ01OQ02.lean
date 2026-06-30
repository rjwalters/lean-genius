/-
  Knight's Tour Oblique Angles: Rectangular Generalization (OQ-01 → OQ-02)

  Proves that every closed knight's tour on any m×n board (m, n ≥ 5)
  has at least 4 oblique (>90°) turns — one forced at each of the four
  corners of the board.

  This generalizes the square n×n result of `KnightsTourObliqueOQ01.lean`
  (`four_oblique_corners`) to *rectangular* boards. The key observation is
  that the oblique lower bound is purely a **corner phenomenon**: it depends
  only on the board having four corners, each of degree 2 in the knight
  graph, and is independent of the aspect ratio of the board. Squareness is
  never used.

  Key insight (unchanged from the square case): for m, n ≥ 5 each corner of
  the board has exactly 2 knight-adjacent squares, and the dot product of the
  entry and exit move vectors at any corner is always −4 < 0, hence the turn
  is oblique. Four distinct corners → ≥ 4 oblique turns. The proof is purely
  algebraic — no `native_decide`, no board enumeration.

  ## Status
  - [x] Parameterized rectangular board and knight graph for general m, n
  - [x] Corner neighbors theorem (degree 2) for all m, n ≥ 5
  - [x] Algebraic oblique proof at corners (dot product = −4, no native_decide)
  - [x] Four distinct corners pairwise distinct
  - [x] Main result: every closed tour has ≥ 4 oblique positions

  Parent proof: `KnightsTourObliqueOQ01.lean` (square n×n case).
  Open question (OQ-02 of OQ-01): does the oblique lower bound extend beyond
  square boards? Answer: yes, to all m×n boards with m, n ≥ 5, via the same
  corner mechanism — the bound is independent of the aspect ratio.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace KnightsTourObliqueRect

/-! ## Section 1: Parameterized Rectangular Board and Knight Graph -/

/-- A square on the m×n chessboard (rows indexed by `Fin m`, columns by `Fin n`). -/
abbrev SquareMN (m n : ℕ) := Fin m × Fin n

/-- The 8 possible knight move offsets -/
def knightOffsets : List (Int × Int) :=
  [(1, 2), (2, 1), (2, -1), (1, -2),
   (-1, -2), (-2, -1), (-2, 1), (-1, 2)]

/-- Check if a move offset is a knight offset -/
def isKnightOffset (dx dy : Int) : Bool :=
  (dx, dy) ∈ knightOffsets

/-- Two squares on the m×n board are knight-adjacent -/
def knightAdjMN (m n : ℕ) (s1 s2 : SquareMN m n) : Prop :=
  let dx := (s2.1 : Int) - (s1.1 : Int)
  let dy := (s2.2 : Int) - (s1.2 : Int)
  isKnightOffset dx dy

instance (m n : ℕ) : DecidableRel (knightAdjMN m n) := fun s1 s2 =>
  decidable_of_bool (isKnightOffset ((s2.1 : Int) - (s1.1 : Int))
                                    ((s2.2 : Int) - (s1.2 : Int)))
    (by simp [knightAdjMN])

/-- Negation of a knight offset is a knight offset -/
theorem neg_knight_offset {dx dy : Int} (h : isKnightOffset dx dy = true) :
    isKnightOffset (-dx) (-dy) = true := by
  simp only [isKnightOffset, knightOffsets, decide_eq_true_eq] at h ⊢
  aesop

/-- The knight graph on the m×n board -/
def knightGraphMN (m n : ℕ) : SimpleGraph (SquareMN m n) where
  Adj := knightAdjMN m n
  symm := by
    intro s1 s2 h
    simp only [knightAdjMN] at h ⊢
    have hdx : (s1.1 : Int) - (s2.1 : Int) = -((s2.1 : Int) - (s1.1 : Int)) := by ring
    have hdy : (s1.2 : Int) - (s2.2 : Int) = -((s2.2 : Int) - (s1.2 : Int)) := by ring
    rw [hdx, hdy]
    exact neg_knight_offset h
  loopless := by
    intro s h
    simp only [knightAdjMN, isKnightOffset, knightOffsets] at h
    simp at h

/-! ## Section 2: Move Vectors and Oblique Predicate -/

/-- A move vector (direction of a knight move) -/
structure MoveVector where
  dx : Int
  dy : Int
deriving DecidableEq, Repr

/-- Dot product of two move vectors -/
def MoveVector.dot (v1 v2 : MoveVector) : Int :=
  v1.dx * v2.dx + v1.dy * v2.dy

/-- A turn is oblique iff the dot product of consecutive move vectors is negative -/
def isOblique (v1 v2 : MoveVector) : Prop :=
  v1.dot v2 < 0

instance (v1 v2 : MoveVector) : Decidable (isOblique v1 v2) :=
  Int.decLt _ _

/-- Get the move vector from s1 to s2 -/
def getMoveVector {m n : ℕ} (s1 s2 : SquareMN m n) : MoveVector :=
  ⟨(s2.1 : Int) - (s1.1 : Int), (s2.2 : Int) - (s1.2 : Int)⟩

/-! ## Section 3: Closed Tour on m×n Board -/

/-- A closed knight's tour on an m×n board -/
structure ClosedTourMN (m n : ℕ) where
  squares : List (SquareMN m n)
  length_eq : squares.length = m * n
  nodup : squares.Nodup
  nonempty : squares ≠ []
  path : ∀ i (hi : i + 1 < squares.length),
    (knightGraphMN m n).Adj (squares[i]'(by omega)) (squares[i + 1]'hi)
  closes : (knightGraphMN m n).Adj
    (squares.getLast nonempty)
    (squares.head nonempty)

/-! ## Section 4: Corner Analysis for General m, n -/

/-- The four corners of the m×n board -/
def cornerTL (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) : SquareMN m n := (⟨0, by omega⟩, ⟨0, by omega⟩)
def cornerTR (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) : SquareMN m n := (⟨0, by omega⟩, ⟨n - 1, by omega⟩)
def cornerBL (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) : SquareMN m n := (⟨m - 1, by omega⟩, ⟨0, by omega⟩)
def cornerBR (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) : SquareMN m n := (⟨m - 1, by omega⟩, ⟨n - 1, by omega⟩)

/-- The four corners are pairwise distinct for m, n ≥ 2 -/
theorem corners_distinct (m n : ℕ) (hm : m ≥ 2) (hn : n ≥ 2) :
    cornerTL m n (by omega) (by omega) ≠ cornerTR m n (by omega) (by omega) ∧
    cornerTL m n (by omega) (by omega) ≠ cornerBL m n (by omega) (by omega) ∧
    cornerTL m n (by omega) (by omega) ≠ cornerBR m n (by omega) (by omega) ∧
    cornerTR m n (by omega) (by omega) ≠ cornerBL m n (by omega) (by omega) ∧
    cornerTR m n (by omega) (by omega) ≠ cornerBR m n (by omega) (by omega) ∧
    cornerBL m n (by omega) (by omega) ≠ cornerBR m n (by omega) (by omega) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [cornerTL, cornerTR, cornerBL, cornerBR, ne_eq, Prod.mk.injEq,
      Fin.mk.injEq, not_and] <;>
    omega

/-- For m, n ≥ 5, corner (0,0) has exactly neighbors (1,2) and (2,1) -/
theorem cornerTL_neighbors (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5) (s : SquareMN m n)
    (hadj : (knightGraphMN m n).Adj (cornerTL m n (by omega) (by omega)) s) :
    s = (⟨1, by omega⟩, ⟨2, by omega⟩) ∨ s = (⟨2, by omega⟩, ⟨1, by omega⟩) := by
  simp only [knightGraphMN, SimpleGraph.Adj, knightAdjMN, cornerTL] at hadj
  simp only [isKnightOffset, knightOffsets, List.mem_cons, Prod.mk.injEq,
    List.mem_singleton, List.mem_nil_iff, decide_eq_true_eq, or_false] at hadj
  rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                   ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; ext <;> simp_all [Fin.ext_iff] <;> omega
  · right; ext <;> simp_all [Fin.ext_iff] <;> omega
  · exfalso; have := s.2.isLt; omega
  · exfalso; have := s.2.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega

/-- For m, n ≥ 5, corner (0,n-1) has exactly neighbors (1,n-3) and (2,n-2) -/
theorem cornerTR_neighbors (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5) (s : SquareMN m n)
    (hadj : (knightGraphMN m n).Adj (cornerTR m n (by omega) (by omega)) s) :
    s = (⟨1, by omega⟩, ⟨n - 3, by omega⟩) ∨ s = (⟨2, by omega⟩, ⟨n - 2, by omega⟩) := by
  simp only [knightGraphMN, SimpleGraph.Adj, knightAdjMN, cornerTR] at hadj
  simp only [isKnightOffset, knightOffsets, List.mem_cons, Prod.mk.injEq,
    List.mem_singleton, List.mem_nil_iff, decide_eq_true_eq, or_false] at hadj
  rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                   ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso; have := s.2.isLt; omega
  · exfalso; have := s.2.isLt; omega
  · right; ext <;> simp_all [Fin.ext_iff] <;> omega
  · left; ext <;> simp_all [Fin.ext_iff] <;> omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega

/-- For m, n ≥ 5, corner (m-1,0) has exactly neighbors (m-3,1) and (m-2,2) -/
theorem cornerBL_neighbors (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5) (s : SquareMN m n)
    (hadj : (knightGraphMN m n).Adj (cornerBL m n (by omega) (by omega)) s) :
    s = (⟨m - 3, by omega⟩, ⟨1, by omega⟩) ∨ s = (⟨m - 2, by omega⟩, ⟨2, by omega⟩) := by
  simp only [knightGraphMN, SimpleGraph.Adj, knightAdjMN, cornerBL] at hadj
  simp only [isKnightOffset, knightOffsets, List.mem_cons, Prod.mk.injEq,
    List.mem_singleton, List.mem_nil_iff, decide_eq_true_eq, or_false] at hadj
  rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                   ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.2.isLt; omega
  · exfalso; have := s.2.isLt; omega
  · exfalso; have := s.2.isLt; omega
  · left; ext <;> simp_all [Fin.ext_iff] <;> omega
  · right; ext <;> simp_all [Fin.ext_iff] <;> omega

/-- For m, n ≥ 5, corner (m-1,n-1) has exactly neighbors (m-3,n-2) and (m-2,n-3) -/
theorem cornerBR_neighbors (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5) (s : SquareMN m n)
    (hadj : (knightGraphMN m n).Adj (cornerBR m n (by omega) (by omega)) s) :
    s = (⟨m - 3, by omega⟩, ⟨n - 2, by omega⟩) ∨ s = (⟨m - 2, by omega⟩, ⟨n - 3, by omega⟩) := by
  simp only [knightGraphMN, SimpleGraph.Adj, knightAdjMN, cornerBR] at hadj
  simp only [isKnightOffset, knightOffsets, List.mem_cons, Prod.mk.injEq,
    List.mem_singleton, List.mem_nil_iff, decide_eq_true_eq, or_false] at hadj
  rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                   ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · exfalso; have := s.1.isLt; omega
  · right; ext <;> simp_all [Fin.ext_iff] <;> omega
  · left; ext <;> simp_all [Fin.ext_iff] <;> omega
  · exfalso; have := s.2.isLt; omega
  · exfalso; have := s.2.isLt; omega

/-! ## Section 5: Oblique Turns at Corners (Algebraic Proof)

The core algebraic fact: at any corner of an m×n board (m, n ≥ 5), the turn
between the two possible neighbors is always oblique. The dot product of the
entry and exit move vectors is always −4.

For each corner, the two knight offsets from the corner are a pair from
{(±1,±2), (±2,±1)}, and the dot product (−offset₁) · offset₂ always equals
−(|1·2| + |2·1|) = −4 < 0, hence oblique. This is purely algebraic and, like
the corner-degree count, independent of the board's aspect ratio.
-/

/-- At corner (0,0), both possible turns are oblique.
    Entering from (1,2) → corner → (2,1): dot = (−1)(2)+(−2)(1) = −4.
    Entering from (2,1) → corner → (1,2): dot = (−2)(1)+(−1)(2) = −4. -/
theorem cornerTL_oblique (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5) (prev next : SquareMN m n)
    (hadj_prev : (knightGraphMN m n).Adj prev (cornerTL m n (by omega) (by omega)))
    (hadj_next : (knightGraphMN m n).Adj (cornerTL m n (by omega) (by omega)) next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev (cornerTL m n (by omega) (by omega)))
              (getMoveVector (cornerTL m n (by omega) (by omega)) next) := by
  have hp := cornerTL_neighbors m n hm hn prev ((knightGraphMN m n).symm hadj_prev)
  have hn' := cornerTL_neighbors m n hm hn next hadj_next
  rcases hp with rfl | rfl <;> rcases hn' with rfl | rfl
  · exact absurd rfl hne
  · show MoveVector.dot _ _ < 0
    simp only [getMoveVector, MoveVector.dot, cornerTL, Fin.val_mk]
    ring_nf; omega
  · show MoveVector.dot _ _ < 0
    simp only [getMoveVector, MoveVector.dot, cornerTL, Fin.val_mk]
    ring_nf; omega
  · exact absurd rfl hne

/-- At corner (0,n-1), both possible turns are oblique.
    Offsets: (1,−2) and (2,−1). Dot = (−1)(2)+(2)(−1) = −4. -/
theorem cornerTR_oblique (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5) (prev next : SquareMN m n)
    (hadj_prev : (knightGraphMN m n).Adj prev (cornerTR m n (by omega) (by omega)))
    (hadj_next : (knightGraphMN m n).Adj (cornerTR m n (by omega) (by omega)) next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev (cornerTR m n (by omega) (by omega)))
              (getMoveVector (cornerTR m n (by omega) (by omega)) next) := by
  have hp := cornerTR_neighbors m n hm hn prev ((knightGraphMN m n).symm hadj_prev)
  have hn' := cornerTR_neighbors m n hm hn next hadj_next
  rcases hp with rfl | rfl <;> rcases hn' with rfl | rfl
  · exact absurd rfl hne
  · show MoveVector.dot _ _ < 0
    simp only [getMoveVector, MoveVector.dot, cornerTR, Fin.val_mk]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
      Nat.cast_sub (show 3 ≤ n by omega)]
    ring_nf; omega
  · show MoveVector.dot _ _ < 0
    simp only [getMoveVector, MoveVector.dot, cornerTR, Fin.val_mk]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
      Nat.cast_sub (show 3 ≤ n by omega)]
    ring_nf; omega
  · exact absurd rfl hne

/-- At corner (m-1,0), both possible turns are oblique.
    Offsets: (−2,1) and (−1,2). Dot = (2)(−1)+(−1)(2) = −4. -/
theorem cornerBL_oblique (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5) (prev next : SquareMN m n)
    (hadj_prev : (knightGraphMN m n).Adj prev (cornerBL m n (by omega) (by omega)))
    (hadj_next : (knightGraphMN m n).Adj (cornerBL m n (by omega) (by omega)) next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev (cornerBL m n (by omega) (by omega)))
              (getMoveVector (cornerBL m n (by omega) (by omega)) next) := by
  have hp := cornerBL_neighbors m n hm hn prev ((knightGraphMN m n).symm hadj_prev)
  have hn' := cornerBL_neighbors m n hm hn next hadj_next
  rcases hp with rfl | rfl <;> rcases hn' with rfl | rfl
  · exact absurd rfl hne
  · show MoveVector.dot _ _ < 0
    simp only [getMoveVector, MoveVector.dot, cornerBL, Fin.val_mk]
    push_cast [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub (show 2 ≤ m by omega),
      Nat.cast_sub (show 3 ≤ m by omega)]
    ring_nf; omega
  · show MoveVector.dot _ _ < 0
    simp only [getMoveVector, MoveVector.dot, cornerBL, Fin.val_mk]
    push_cast [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub (show 2 ≤ m by omega),
      Nat.cast_sub (show 3 ≤ m by omega)]
    ring_nf; omega
  · exact absurd rfl hne

/-- At corner (m-1,n-1), both possible turns are oblique.
    Offsets: (−2,−1) and (−1,−2). Dot = (2)(−1)+(1)(−2) = −4. -/
theorem cornerBR_oblique (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5) (prev next : SquareMN m n)
    (hadj_prev : (knightGraphMN m n).Adj prev (cornerBR m n (by omega) (by omega)))
    (hadj_next : (knightGraphMN m n).Adj (cornerBR m n (by omega) (by omega)) next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev (cornerBR m n (by omega) (by omega)))
              (getMoveVector (cornerBR m n (by omega) (by omega)) next) := by
  have hp := cornerBR_neighbors m n hm hn prev ((knightGraphMN m n).symm hadj_prev)
  have hn' := cornerBR_neighbors m n hm hn next hadj_next
  rcases hp with rfl | rfl <;> rcases hn' with rfl | rfl
  · exact absurd rfl hne
  · show MoveVector.dot _ _ < 0
    simp only [getMoveVector, MoveVector.dot, cornerBR, Fin.val_mk]
    push_cast [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub (show 2 ≤ m by omega),
      Nat.cast_sub (show 3 ≤ m by omega), Nat.cast_sub (show 1 ≤ n by omega),
      Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega)]
    ring_nf; omega
  · show MoveVector.dot _ _ < 0
    simp only [getMoveVector, MoveVector.dot, cornerBR, Fin.val_mk]
    push_cast [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub (show 2 ≤ m by omega),
      Nat.cast_sub (show 3 ≤ m by omega), Nat.cast_sub (show 1 ≤ n by omega),
      Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega)]
    ring_nf; omega
  · exact absurd rfl hne

/-- At any corner of the m×n board, the turn is oblique -/
theorem corner_forces_oblique (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5)
    (c : SquareMN m n)
    (hc : c = cornerTL m n (by omega) (by omega) ∨ c = cornerTR m n (by omega) (by omega) ∨
          c = cornerBL m n (by omega) (by omega) ∨ c = cornerBR m n (by omega) (by omega))
    (prev next : SquareMN m n)
    (hadj_prev : (knightGraphMN m n).Adj prev c)
    (hadj_next : (knightGraphMN m n).Adj c next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev c) (getMoveVector c next) := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact cornerTL_oblique m n hm hn prev next hadj_prev hadj_next hne
  · exact cornerTR_oblique m n hm hn prev next hadj_prev hadj_next hne
  · exact cornerBL_oblique m n hm hn prev next hadj_prev hadj_next hne
  · exact cornerBR_oblique m n hm hn prev next hadj_prev hadj_next hne

/-! ## Section 6: Tour Properties -/

/-- A closed tour visits all m·n squares -/
theorem tour_visits_all (m n : ℕ) (t : ClosedTourMN m n) (s : SquareMN m n) :
    s ∈ t.squares := by
  have hcard : Fintype.card (SquareMN m n) = m * n := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have htoFinset : t.squares.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup t.nodup, t.length_eq, hcard]
  rw [← List.mem_toFinset, htoFinset]
  exact Finset.mem_univ s

/-- Cyclic adjacency in the tour -/
theorem tour_cyclic_adj (m n : ℕ) (t : ClosedTourMN m n) (i : Fin (m * n)) :
    (knightGraphMN m n).Adj
      (t.squares[i.val]'(by rw [t.length_eq]; exact i.isLt))
      (t.squares[(i.val + 1) % (m * n)]'(by
        rw [t.length_eq]; exact Nat.mod_lt _ (by have := i.isLt; omega))) := by
  by_cases h : i.val + 1 < m * n
  · simp only [Nat.mod_eq_of_lt h]
    exact t.path i.val (by rw [t.length_eq]; exact h)
  · have hi : i.val = m * n - 1 := by omega
    have hkey : (i.val + 1) % (m * n) = 0 := by
      rw [hi, Nat.sub_add_cancel (by have := i.isLt; omega), Nat.mod_self]
    have hlast : t.squares[i.val]'(by rw [t.length_eq]; exact i.isLt)
        = t.squares.getLast t.nonempty := by
      rw [List.getLast_eq_getElem]; congr 1
      rw [t.length_eq]; omega
    have hhead : t.squares[(i.val + 1) % (m * n)]'(by
          rw [t.length_eq]; exact Nat.mod_lt _ (by have := i.isLt; omega))
        = t.squares.head t.nonempty := by
      rw [List.head_eq_getElem]; congr 1
    rw [hlast, hhead]
    exact t.closes

/-- Distinct positions in a tour have distinct squares -/
theorem tour_index_neq (m n : ℕ) (t : ClosedTourMN m n) (i j : ℕ)
    (hi : i < m * n) (hj : j < m * n) (hne : i ≠ j) :
    t.squares[i]'(by rw [t.length_eq]; exact hi) ≠
    t.squares[j]'(by rw [t.length_eq]; exact hj) := by
  rw [ne_eq, t.nodup.getElem_inj_iff]
  exact hne

/-! ## Section 7: Main Theorem

Every closed knight's tour on an m×n board (m, n ≥ 5) has at least 4 oblique
turns. The proof establishes 4 distinct positions in the tour where the turn
is oblique — one at each corner of the board. Since each corner has exactly 2
knight-adjacent squares and the dot product of entry/exit vectors is always
−4 < 0, the turn at each corner is oblique. Crucially, the argument never uses
m = n: the oblique lower bound is a corner phenomenon, independent of the
board's aspect ratio.
-/

/-- **Theorem (Four Oblique Positions, Rectangular)**: Every closed knight's
    tour on an m×n board (m, n ≥ 5) has at least 4 positions where the turn is
    oblique, namely at the 4 corners of the board.

    This is the generalization of `KnightsTourObliqueOQ01.four_oblique_corners`
    from square n×n boards to arbitrary rectangular m×n boards. -/
theorem four_oblique_corners_rect (m n : ℕ) (hm : m ≥ 5) (hn : n ≥ 5) (t : ClosedTourMN m n) :
    ∃ (i₁ i₂ i₃ i₄ : Fin (m * n)),
      i₁.val ≠ i₂.val ∧ i₁.val ≠ i₃.val ∧ i₁.val ≠ i₄.val ∧
      i₂.val ≠ i₃.val ∧ i₂.val ≠ i₄.val ∧ i₃.val ≠ i₄.val ∧
      (let prev₁ := t.squares[(i₁.val + (m*n - 1)) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))
       let next₁ := t.squares[(i₁.val + 1) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))
       let c₁ := t.squares[i₁.val]'(by rw [t.length_eq]; exact i₁.isLt)
       isOblique (getMoveVector prev₁ c₁) (getMoveVector c₁ next₁)) ∧
      (let prev₂ := t.squares[(i₂.val + (m*n - 1)) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))
       let next₂ := t.squares[(i₂.val + 1) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))
       let c₂ := t.squares[i₂.val]'(by rw [t.length_eq]; exact i₂.isLt)
       isOblique (getMoveVector prev₂ c₂) (getMoveVector c₂ next₂)) ∧
      (let prev₃ := t.squares[(i₃.val + (m*n - 1)) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))
       let next₃ := t.squares[(i₃.val + 1) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))
       let c₃ := t.squares[i₃.val]'(by rw [t.length_eq]; exact i₃.isLt)
       isOblique (getMoveVector prev₃ c₃) (getMoveVector c₃ next₃)) ∧
      (let prev₄ := t.squares[(i₄.val + (m*n - 1)) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))
       let next₄ := t.squares[(i₄.val + 1) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))
       let c₄ := t.squares[i₄.val]'(by rw [t.length_eq]; exact i₄.isLt)
       isOblique (getMoveVector prev₄ c₄) (getMoveVector c₄ next₄)) := by
  have hpos : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  -- Board has at least 25 squares; omega needs this linear fact about the
  -- nonlinear product m * n (e.g. to rule out m * n = 2 at the wrap-around).
  have hbig : 25 ≤ m * n := by
    have := Nat.mul_le_mul hm hn
    omega
  -- Cyclic predecessor-then-successor returns the original index.
  have hcyc : ∀ (k : ℕ), k < m * n →
      ((k + (m * n - 1)) % (m * n) + 1) % (m * n) = k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpk
    · subst h0
      have hinner : (0 + (m * n - 1)) % (m * n) = m * n - 1 := by
        rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [hinner, Nat.sub_add_cancel (by omega), Nat.mod_self]
    · have hinner : (k + (m * n - 1)) % (m * n) = k - 1 := by
        rw [show k + (m * n - 1) = m * n + (k - 1) by omega, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hinner, Nat.sub_add_cancel hpk, Nat.mod_eq_of_lt hk]
  -- Cyclic predecessor and successor of an index are distinct (board size ≥ 25 ≥ 3).
  have hpn : ∀ (k : ℕ), k < m * n →
      (k + (m * n - 1)) % (m * n) ≠ (k + 1) % (m * n) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpk
    · subst h0
      have e1 : (0 + (m * n - 1)) % (m * n) = m * n - 1 := by
        rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      have e2 : (0 + 1) % (m * n) = 1 := by rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      rw [e1, e2]; omega
    · have hsplit : k + (m * n - 1) = m * n + (k - 1) := by omega
      have e1 : (k + (m * n - 1)) % (m * n) = k - 1 := by
        rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      by_cases hkm : k + 1 < m * n
      · rw [e1, Nat.mod_eq_of_lt hkm]; omega
      · have e2 : (k + 1) % (m * n) = 0 := by rw [show k + 1 = m * n by omega, Nat.mod_self]
        rw [e1, e2]; omega
  -- getElem at provably-equal indices yields equal elements.
  have hsqcong : ∀ {a b : ℕ} (ha : a < t.squares.length) (hb : b < t.squares.length),
      a = b → t.squares[a]'ha = t.squares[b]'hb := by
    intro a b ha hb hab; subst hab; rfl

  have hcTL : cornerTL m n (by omega) (by omega) ∈ t.squares := tour_visits_all m n t _
  have hcTR : cornerTR m n (by omega) (by omega) ∈ t.squares := tour_visits_all m n t _
  have hcBL : cornerBL m n (by omega) (by omega) ∈ t.squares := tour_visits_all m n t _
  have hcBR : cornerBR m n (by omega) (by omega) ∈ t.squares := tour_visits_all m n t _

  obtain ⟨⟨iTL, hiTL⟩, heqTL⟩ := List.mem_iff_get.mp hcTL
  obtain ⟨⟨iTR, hiTR⟩, heqTR⟩ := List.mem_iff_get.mp hcTR
  obtain ⟨⟨iBL, hiBL⟩, heqBL⟩ := List.mem_iff_get.mp hcBL
  obtain ⟨⟨iBR, hiBR⟩, heqBR⟩ := List.mem_iff_get.mp hcBR

  -- All indices are < m·n
  have hiTL_lt : iTL < m * n := by rw [t.length_eq] at hiTL; exact hiTL
  have hiTR_lt : iTR < m * n := by rw [t.length_eq] at hiTR; exact hiTR
  have hiBL_lt : iBL < m * n := by rw [t.length_eq] at hiBL; exact hiBL
  have hiBR_lt : iBR < m * n := by rw [t.length_eq] at hiBR; exact hiBR

  -- Corner indices are pairwise distinct
  have hdist := corners_distinct m n (by omega) (by omega)
  have hmkeq : ∀ {a b : ℕ} (ha : a < t.squares.length) (hb : b < t.squares.length),
      a = b → t.squares.get ⟨a, ha⟩ = t.squares.get ⟨b, hb⟩ := by
    intro a b ha hb hab; congr 1; exact Fin.ext hab
  have hne12 : iTL ≠ iTR := by
    intro h; apply hdist.1; rw [← heqTL, ← heqTR]; exact hmkeq hiTL hiTR h
  have hne13 : iTL ≠ iBL := by
    intro h; apply hdist.2.1; rw [← heqTL, ← heqBL]; exact hmkeq hiTL hiBL h
  have hne14 : iTL ≠ iBR := by
    intro h; apply hdist.2.2.1; rw [← heqTL, ← heqBR]; exact hmkeq hiTL hiBR h
  have hne23 : iTR ≠ iBL := by
    intro h; apply hdist.2.2.2.1; rw [← heqTR, ← heqBL]; exact hmkeq hiTR hiBL h
  have hne24 : iTR ≠ iBR := by
    intro h; apply hdist.2.2.2.2.1; rw [← heqTR, ← heqBR]; exact hmkeq hiTR hiBR h
  have hne34 : iBL ≠ iBR := by
    intro h; apply hdist.2.2.2.2.2; rw [← heqBL, ← heqBR]; exact hmkeq hiBL hiBR h

  refine ⟨⟨iTL, hiTL_lt⟩, ⟨iTR, hiTR_lt⟩, ⟨iBL, hiBL_lt⟩, ⟨iBR, hiBR_lt⟩,
          hne12, hne13, hne14, hne23, hne24, hne34, ?_, ?_, ?_, ?_⟩

  · -- Corner TL at position iTL
    have hadj_prev : (knightGraphMN m n).Adj
        (t.squares[(iTL + (m*n - 1)) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega))))
        (t.squares[iTL]'(by rw [t.length_eq]; exact hiTL_lt)) := by
      have h := tour_cyclic_adj m n t ⟨(iTL + (m*n - 1)) % (m*n), Nat.mod_lt _ hpos⟩
      rw [hsqcong (a := ((iTL + (m*n - 1)) % (m*n) + 1) % (m*n)) (b := iTL)
        (by rw [t.length_eq]; exact Nat.mod_lt _ hpos) (by rw [t.length_eq]; exact hiTL_lt)
        (hcyc iTL hiTL_lt)] at h
      exact h
    have hadj_next : (knightGraphMN m n).Adj
        (t.squares[iTL]'(by rw [t.length_eq]; exact hiTL_lt))
        (t.squares[(iTL + 1) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))) := by
      exact tour_cyclic_adj m n t ⟨iTL, hiTL_lt⟩
    have hpn_ne := hpn iTL hiTL_lt
    have hsq_ne := tour_index_neq m n t _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hpn_ne
    exact corner_forces_oblique m n hm hn _ (Or.inl heqTL) _ _ hadj_prev hadj_next hsq_ne

  · -- Corner TR at position iTR
    have hadj_prev : (knightGraphMN m n).Adj
        (t.squares[(iTR + (m*n - 1)) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega))))
        (t.squares[iTR]'(by rw [t.length_eq]; exact hiTR_lt)) := by
      have h := tour_cyclic_adj m n t ⟨(iTR + (m*n - 1)) % (m*n), Nat.mod_lt _ hpos⟩
      rw [hsqcong (a := ((iTR + (m*n - 1)) % (m*n) + 1) % (m*n)) (b := iTR)
        (by rw [t.length_eq]; exact Nat.mod_lt _ hpos) (by rw [t.length_eq]; exact hiTR_lt)
        (hcyc iTR hiTR_lt)] at h
      exact h
    have hadj_next : (knightGraphMN m n).Adj
        (t.squares[iTR]'(by rw [t.length_eq]; exact hiTR_lt))
        (t.squares[(iTR + 1) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))) := by
      exact tour_cyclic_adj m n t ⟨iTR, hiTR_lt⟩
    have hpn_ne := hpn iTR hiTR_lt
    have hsq_ne := tour_index_neq m n t _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hpn_ne
    exact corner_forces_oblique m n hm hn _ (Or.inr (Or.inl heqTR)) _ _ hadj_prev hadj_next hsq_ne

  · -- Corner BL at position iBL
    have hadj_prev : (knightGraphMN m n).Adj
        (t.squares[(iBL + (m*n - 1)) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega))))
        (t.squares[iBL]'(by rw [t.length_eq]; exact hiBL_lt)) := by
      have h := tour_cyclic_adj m n t ⟨(iBL + (m*n - 1)) % (m*n), Nat.mod_lt _ hpos⟩
      rw [hsqcong (a := ((iBL + (m*n - 1)) % (m*n) + 1) % (m*n)) (b := iBL)
        (by rw [t.length_eq]; exact Nat.mod_lt _ hpos) (by rw [t.length_eq]; exact hiBL_lt)
        (hcyc iBL hiBL_lt)] at h
      exact h
    have hadj_next : (knightGraphMN m n).Adj
        (t.squares[iBL]'(by rw [t.length_eq]; exact hiBL_lt))
        (t.squares[(iBL + 1) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))) := by
      exact tour_cyclic_adj m n t ⟨iBL, hiBL_lt⟩
    have hpn_ne := hpn iBL hiBL_lt
    have hsq_ne := tour_index_neq m n t _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hpn_ne
    exact corner_forces_oblique m n hm hn _ (Or.inr (Or.inr (Or.inl heqBL))) _ _ hadj_prev hadj_next hsq_ne

  · -- Corner BR at position iBR
    have hadj_prev : (knightGraphMN m n).Adj
        (t.squares[(iBR + (m*n - 1)) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega))))
        (t.squares[iBR]'(by rw [t.length_eq]; exact hiBR_lt)) := by
      have h := tour_cyclic_adj m n t ⟨(iBR + (m*n - 1)) % (m*n), Nat.mod_lt _ hpos⟩
      rw [hsqcong (a := ((iBR + (m*n - 1)) % (m*n) + 1) % (m*n)) (b := iBR)
        (by rw [t.length_eq]; exact Nat.mod_lt _ hpos) (by rw [t.length_eq]; exact hiBR_lt)
        (hcyc iBR hiBR_lt)] at h
      exact h
    have hadj_next : (knightGraphMN m n).Adj
        (t.squares[iBR]'(by rw [t.length_eq]; exact hiBR_lt))
        (t.squares[(iBR + 1) % (m*n)]'(by rw [t.length_eq]; exact Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega)))) := by
      exact tour_cyclic_adj m n t ⟨iBR, hiBR_lt⟩
    have hpn_ne := hpn iBR hiBR_lt
    have hsq_ne := tour_index_neq m n t _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hpn_ne
    exact corner_forces_oblique m n hm hn _ (Or.inr (Or.inr (Or.inr heqBR))) _ _ hadj_prev hadj_next hsq_ne

end KnightsTourObliqueRect
