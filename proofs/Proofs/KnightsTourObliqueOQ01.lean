/-
  Knight's Tour Oblique Angles: Generalized Lower Bound (OQ-01)

  Proves that every closed knight's tour on any n×n board (n ≥ 5)
  has at least 4 oblique (>90°) turns.

  This generalizes the 8×8 result from KnightsTourOblique.lean to
  all board sizes. The proof is purely algebraic — no native_decide.

  Key insight: For n ≥ 5, each corner of the board has exactly 2
  knight-adjacent squares. The dot product of the entry and exit
  move vectors at any corner is always −4, hence oblique.
  Four distinct corners → ≥ 4 oblique turns.

  ## Status
  - [x] Parameterized board and knight graph for general n
  - [x] Corner neighbors theorem (degree 2) for all n ≥ 5
  - [x] Algebraic oblique proof at corners (dot product = −4, no native_decide)
  - [x] Four distinct oblique positions exist
  - [ ] Counting connection to obliqueCountN (sorry — routine bookkeeping)

  Parent proof: KnightsTourOblique.lean (8×8 case)
  Open question: "Can similar oblique-angle bounds be proven for larger n×n boards?"
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace KnightsTourObliqueGeneral

/-! ## Section 1: Parameterized Board and Knight Graph -/

/-- A square on the n×n chessboard -/
abbrev SquareN (n : ℕ) := Fin n × Fin n

/-- The 8 possible knight move offsets -/
def knightOffsets : List (Int × Int) :=
  [(1, 2), (2, 1), (2, -1), (1, -2),
   (-1, -2), (-2, -1), (-2, 1), (-1, 2)]

/-- Check if a move offset is a knight offset -/
def isKnightOffset (dx dy : Int) : Bool :=
  (dx, dy) ∈ knightOffsets

/-- Two squares on the n×n board are knight-adjacent -/
def knightAdjN (n : ℕ) (s1 s2 : SquareN n) : Prop :=
  let dx := (s2.1 : Int) - (s1.1 : Int)
  let dy := (s2.2 : Int) - (s1.2 : Int)
  isKnightOffset dx dy

instance (n : ℕ) : DecidableRel (knightAdjN n) := fun s1 s2 =>
  decidable_of_bool (isKnightOffset ((s2.1 : Int) - (s1.1 : Int))
                                    ((s2.2 : Int) - (s1.2 : Int)))
    (by simp [knightAdjN])

/-- Negation of a knight offset is a knight offset -/
theorem neg_knight_offset {dx dy : Int} (h : isKnightOffset dx dy = true) :
    isKnightOffset (-dx) (-dy) = true := by
  simp only [isKnightOffset, knightOffsets, decide_eq_true_eq] at h ⊢
  aesop

/-- The knight graph on the n×n board -/
def knightGraphN (n : ℕ) : SimpleGraph (SquareN n) where
  Adj := knightAdjN n
  symm := by
    intro s1 s2 h
    simp only [knightAdjN] at h ⊢
    have hdx : (s1.1 : Int) - (s2.1 : Int) = -((s2.1 : Int) - (s1.1 : Int)) := by ring
    have hdy : (s1.2 : Int) - (s2.2 : Int) = -((s2.2 : Int) - (s1.2 : Int)) := by ring
    rw [hdx, hdy]
    exact neg_knight_offset h
  loopless := by
    intro s h
    simp only [knightAdjN, isKnightOffset, knightOffsets] at h
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
def getMoveVector {n : ℕ} (s1 s2 : SquareN n) : MoveVector :=
  ⟨(s2.1 : Int) - (s1.1 : Int), (s2.2 : Int) - (s1.2 : Int)⟩

/-! ## Section 3: Closed Tour on n×n Board -/

/-- A closed knight's tour on an n×n board -/
structure ClosedTourN (n : ℕ) where
  squares : List (SquareN n)
  length_eq : squares.length = n * n
  nodup : squares.Nodup
  path : ∀ i, i + 1 < squares.length →
    (knightGraphN n).Adj (squares[i]'(by omega)) (squares[i + 1]'(by omega))
  closes : (knightGraphN n).Adj
    (squares.getLast (by rw [length_eq]; omega))
    (squares.head (by rw [length_eq]; omega))
  nonempty : squares ≠ []

/-! ## Section 4: Corner Analysis for General n -/

/-- The four corners of the n×n board -/
def cornerTL (n : ℕ) (hn : n ≥ 1) : SquareN n := (⟨0, by omega⟩, ⟨0, by omega⟩)
def cornerTR (n : ℕ) (hn : n ≥ 1) : SquareN n := (⟨0, by omega⟩, ⟨n - 1, by omega⟩)
def cornerBL (n : ℕ) (hn : n ≥ 1) : SquareN n := (⟨n - 1, by omega⟩, ⟨0, by omega⟩)
def cornerBR (n : ℕ) (hn : n ≥ 1) : SquareN n := (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩)

/-- The four corners are pairwise distinct for n ≥ 2 -/
theorem corners_distinct (n : ℕ) (hn : n ≥ 2) :
    cornerTL n (by omega) ≠ cornerTR n (by omega) ∧
    cornerTL n (by omega) ≠ cornerBL n (by omega) ∧
    cornerTL n (by omega) ≠ cornerBR n (by omega) ∧
    cornerTR n (by omega) ≠ cornerBL n (by omega) ∧
    cornerTR n (by omega) ≠ cornerBR n (by omega) ∧
    cornerBL n (by omega) ≠ cornerBR n (by omega) := by
  simp only [cornerTL, cornerTR, cornerBL, cornerBR, ne_eq, Prod.mk.injEq, not_and]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro h
  all_goals simp only [Fin.mk.injEq] at h
  all_goals omega

/-- For n ≥ 5, corner (0,0) has exactly neighbors (1,2) and (2,1) -/
theorem cornerTL_neighbors (n : ℕ) (hn : n ≥ 5) (s : SquareN n)
    (hadj : (knightGraphN n).Adj (cornerTL n (by omega)) s) :
    s = (⟨1, by omega⟩, ⟨2, by omega⟩) ∨ s = (⟨2, by omega⟩, ⟨1, by omega⟩) := by
  simp only [knightGraphN, SimpleGraph.Adj, knightAdjN, cornerTL] at hadj
  simp only [isKnightOffset, knightOffsets, List.mem_cons, Prod.mk.injEq,
    List.mem_singleton, List.mem_nil_iff, decide_eq_true_eq] at hadj
  rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                   ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; ext <;> simp_all [Fin.ext_iff] <;> omega
  · right; ext <;> simp_all [Fin.ext_iff] <;> omega
  · exfalso; have := s.2.val_lt_last (by omega); omega
  · exfalso; have := s.2.val_lt_last (by omega); omega
  · exfalso; have := s.1.val_lt_last (by omega); omega
  · exfalso; have := s.1.val_lt_last (by omega); omega
  · exfalso; have := s.1.val_lt_last (by omega); omega
  · exfalso; have := s.1.val_lt_last (by omega); omega

/-- For n ≥ 5, corner (0,n-1) has exactly neighbors (1,n-3) and (2,n-2) -/
theorem cornerTR_neighbors (n : ℕ) (hn : n ≥ 5) (s : SquareN n)
    (hadj : (knightGraphN n).Adj (cornerTR n (by omega)) s) :
    s = (⟨1, by omega⟩, ⟨n - 3, by omega⟩) ∨ s = (⟨2, by omega⟩, ⟨n - 2, by omega⟩) := by
  simp only [knightGraphN, SimpleGraph.Adj, knightAdjN, cornerTR] at hadj
  simp only [isKnightOffset, knightOffsets, List.mem_cons, Prod.mk.injEq,
    List.mem_singleton, List.mem_nil_iff, decide_eq_true_eq] at hadj
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

/-- For n ≥ 5, corner (n-1,0) has exactly neighbors (n-3,1) and (n-2,2) -/
theorem cornerBL_neighbors (n : ℕ) (hn : n ≥ 5) (s : SquareN n)
    (hadj : (knightGraphN n).Adj (cornerBL n (by omega)) s) :
    s = (⟨n - 3, by omega⟩, ⟨1, by omega⟩) ∨ s = (⟨n - 2, by omega⟩, ⟨2, by omega⟩) := by
  simp only [knightGraphN, SimpleGraph.Adj, knightAdjN, cornerBL] at hadj
  simp only [isKnightOffset, knightOffsets, List.mem_cons, Prod.mk.injEq,
    List.mem_singleton, List.mem_nil_iff, decide_eq_true_eq] at hadj
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

/-- For n ≥ 5, corner (n-1,n-1) has exactly neighbors (n-3,n-2) and (n-2,n-3) -/
theorem cornerBR_neighbors (n : ℕ) (hn : n ≥ 5) (s : SquareN n)
    (hadj : (knightGraphN n).Adj (cornerBR n (by omega)) s) :
    s = (⟨n - 3, by omega⟩, ⟨n - 2, by omega⟩) ∨ s = (⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩) := by
  simp only [knightGraphN, SimpleGraph.Adj, knightAdjN, cornerBR] at hadj
  simp only [isKnightOffset, knightOffsets, List.mem_cons, Prod.mk.injEq,
    List.mem_singleton, List.mem_nil_iff, decide_eq_true_eq] at hadj
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

The core algebraic fact: at any corner of an n×n board (n ≥ 5), the turn
between the two possible neighbors is always oblique. The dot product of
the entry and exit move vectors is always −4.

For each corner, the two knight offsets from the corner are a pair from
{(±1,±2), (±2,±1)}. The dot product (−offset₁) · offset₂ always equals
−(|1·2| + |2·1|) = −4 < 0, hence oblique. This is purely algebraic.
-/

/-- At corner (0,0), both possible turns are oblique.
    Entering from (1,2) → corner → (2,1): dot = (−1)(2)+(−2)(1) = −4.
    Entering from (2,1) → corner → (1,2): dot = (−2)(1)+(−1)(2) = −4. -/
theorem cornerTL_oblique (n : ℕ) (hn : n ≥ 5) (prev next : SquareN n)
    (hadj_prev : (knightGraphN n).Adj prev (cornerTL n (by omega)))
    (hadj_next : (knightGraphN n).Adj (cornerTL n (by omega)) next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev (cornerTL n (by omega)))
              (getMoveVector (cornerTL n (by omega)) next) := by
  have hp := cornerTL_neighbors n hn prev ((knightGraphN n).symm hadj_prev)
  have hn' := cornerTL_neighbors n hn next hadj_next
  rcases hp with rfl | rfl <;> rcases hn' with rfl | rfl
  · exact absurd rfl hne
  · -- prev=(1,2), next=(2,1): dot = (-1)*2+(-2)*1 = -4
    show MoveVector.dot _ _ < 0
    simp [getMoveVector, MoveVector.dot, cornerTL]
    omega
  · -- prev=(2,1), next=(1,2): dot = (-2)*1+(-1)*2 = -4
    show MoveVector.dot _ _ < 0
    simp [getMoveVector, MoveVector.dot, cornerTL]
    omega
  · exact absurd rfl hne

/-- At corner (0,n-1), both possible turns are oblique.
    Offsets: (1,−2) and (2,−1). Dot = (−1)(2)+(2)(−1) = −4. -/
theorem cornerTR_oblique (n : ℕ) (hn : n ≥ 5) (prev next : SquareN n)
    (hadj_prev : (knightGraphN n).Adj prev (cornerTR n (by omega)))
    (hadj_next : (knightGraphN n).Adj (cornerTR n (by omega)) next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev (cornerTR n (by omega)))
              (getMoveVector (cornerTR n (by omega)) next) := by
  have hp := cornerTR_neighbors n hn prev ((knightGraphN n).symm hadj_prev)
  have hn' := cornerTR_neighbors n hn next hadj_next
  rcases hp with rfl | rfl <;> rcases hn' with rfl | rfl
  · exact absurd rfl hne
  · show MoveVector.dot _ _ < 0
    simp [getMoveVector, MoveVector.dot, cornerTR]
    omega
  · show MoveVector.dot _ _ < 0
    simp [getMoveVector, MoveVector.dot, cornerTR]
    omega
  · exact absurd rfl hne

/-- At corner (n-1,0), both possible turns are oblique.
    Offsets: (−2,1) and (−1,2). Dot = (2)(−1)+(−1)(2) = −4. -/
theorem cornerBL_oblique (n : ℕ) (hn : n ≥ 5) (prev next : SquareN n)
    (hadj_prev : (knightGraphN n).Adj prev (cornerBL n (by omega)))
    (hadj_next : (knightGraphN n).Adj (cornerBL n (by omega)) next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev (cornerBL n (by omega)))
              (getMoveVector (cornerBL n (by omega)) next) := by
  have hp := cornerBL_neighbors n hn prev ((knightGraphN n).symm hadj_prev)
  have hn' := cornerBL_neighbors n hn next hadj_next
  rcases hp with rfl | rfl <;> rcases hn' with rfl | rfl
  · exact absurd rfl hne
  · show MoveVector.dot _ _ < 0
    simp [getMoveVector, MoveVector.dot, cornerBL]
    omega
  · show MoveVector.dot _ _ < 0
    simp [getMoveVector, MoveVector.dot, cornerBL]
    omega
  · exact absurd rfl hne

/-- At corner (n-1,n-1), both possible turns are oblique.
    Offsets: (−2,−1) and (−1,−2). Dot = (2)(−1)+(1)(−2) = −4. -/
theorem cornerBR_oblique (n : ℕ) (hn : n ≥ 5) (prev next : SquareN n)
    (hadj_prev : (knightGraphN n).Adj prev (cornerBR n (by omega)))
    (hadj_next : (knightGraphN n).Adj (cornerBR n (by omega)) next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev (cornerBR n (by omega)))
              (getMoveVector (cornerBR n (by omega)) next) := by
  have hp := cornerBR_neighbors n hn prev ((knightGraphN n).symm hadj_prev)
  have hn' := cornerBR_neighbors n hn next hadj_next
  rcases hp with rfl | rfl <;> rcases hn' with rfl | rfl
  · exact absurd rfl hne
  · show MoveVector.dot _ _ < 0
    simp [getMoveVector, MoveVector.dot, cornerBR]
    omega
  · show MoveVector.dot _ _ < 0
    simp [getMoveVector, MoveVector.dot, cornerBR]
    omega
  · exact absurd rfl hne

/-- At any corner of the n×n board, the turn is oblique -/
theorem corner_forces_oblique (n : ℕ) (hn : n ≥ 5)
    (c : SquareN n)
    (hc : c = cornerTL n (by omega) ∨ c = cornerTR n (by omega) ∨
          c = cornerBL n (by omega) ∨ c = cornerBR n (by omega))
    (prev next : SquareN n)
    (hadj_prev : (knightGraphN n).Adj prev c)
    (hadj_next : (knightGraphN n).Adj c next)
    (hne : prev ≠ next) :
    isOblique (getMoveVector prev c) (getMoveVector c next) := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact cornerTL_oblique n hn prev next hadj_prev hadj_next hne
  · exact cornerTR_oblique n hn prev next hadj_prev hadj_next hne
  · exact cornerBL_oblique n hn prev next hadj_prev hadj_next hne
  · exact cornerBR_oblique n hn prev next hadj_prev hadj_next hne

/-! ## Section 6: Tour Properties -/

/-- A closed tour visits all n² squares -/
theorem tour_visits_all (n : ℕ) (t : ClosedTourN n) (s : SquareN n) :
    s ∈ t.squares := by
  have hcard : Fintype.card (SquareN n) = n * n := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have htoFinset : t.squares.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup t.nodup, t.length_eq, hcard]
  rw [← List.mem_toFinset, htoFinset]
  exact Finset.mem_univ s

/-- Cyclic adjacency in the tour -/
theorem tour_cyclic_adj (n : ℕ) (t : ClosedTourN n) (i : Fin (n * n)) :
    (knightGraphN n).Adj
      (t.squares[i.val]'(by rw [t.length_eq]; exact i.isLt))
      (t.squares[(i.val + 1) % (n * n)]'(by rw [t.length_eq]; omega)) := by
  by_cases h : i.val + 1 < n * n
  · simp only [Nat.mod_eq_of_lt h]
    exact t.path i.val h
  · have hi : i.val = n * n - 1 := by omega
    simp only [hi]
    have hmod : (n * n - 1 + 1) % (n * n) = 0 := by omega
    rw [hmod]
    have hlast : t.squares.getLast t.nonempty =
        t.squares[n * n - 1]'(by rw [t.length_eq]; omega) := by
      simp only [List.getLast_eq_getElem, t.length_eq]
    have hhead : t.squares.head t.nonempty =
        t.squares[0]'(by rw [t.length_eq]; omega) := by
      simp only [List.head_eq_getElem, t.length_eq]
    rw [← hlast, ← hhead]
    exact t.closes

/-- Distinct positions in a tour have distinct squares -/
theorem tour_index_neq (n : ℕ) (t : ClosedTourN n) (i j : ℕ)
    (hi : i < n * n) (hj : j < n * n) (hne : i ≠ j) :
    t.squares[i]'(by rw [t.length_eq]; exact hi) ≠
    t.squares[j]'(by rw [t.length_eq]; exact hj) := by
  intro heq
  have := List.Nodup.get_inj_iff t.nodup
  have h : (⟨i, by rw [t.length_eq]; exact hi⟩ : Fin t.squares.length) =
           ⟨j, by rw [t.length_eq]; exact hj⟩ := this.mp heq
  simp at h
  exact hne h

/-! ## Section 7: Main Theorem

Every closed knight's tour on an n×n board (n ≥ 5) has at least 4 oblique turns.

The proof establishes that there exist 4 distinct positions in the tour where
the turn is oblique — one at each corner of the board. Since each corner has
exactly 2 knight-adjacent squares and the dot product of entry/exit vectors
is always −4 < 0, the turn at each corner is oblique.
-/

/-- **Theorem (Four Oblique Positions)**: Every closed knight's tour on an
    n×n board (n ≥ 5) has at least 4 positions where the turn is oblique,
    namely at the 4 corners of the board.

    This is the generalization of the 8×8 lower bound to all n ≥ 5. -/
theorem four_oblique_corners (n : ℕ) (hn : n ≥ 5) (t : ClosedTourN n) :
    ∃ (i₁ i₂ i₃ i₄ : Fin (n * n)),
      i₁.val ≠ i₂.val ∧ i₁.val ≠ i₃.val ∧ i₁.val ≠ i₄.val ∧
      i₂.val ≠ i₃.val ∧ i₂.val ≠ i₄.val ∧ i₃.val ≠ i₄.val ∧
      -- At each corner position, the turn is oblique
      (let prev₁ := t.squares[(i₁.val + (n*n - 1)) % (n*n)]'(by rw [t.length_eq]; omega)
       let next₁ := t.squares[(i₁.val + 1) % (n*n)]'(by rw [t.length_eq]; omega)
       let c₁ := t.squares[i₁.val]'(by rw [t.length_eq]; exact i₁.isLt)
       isOblique (getMoveVector prev₁ c₁) (getMoveVector c₁ next₁)) ∧
      (let prev₂ := t.squares[(i₂.val + (n*n - 1)) % (n*n)]'(by rw [t.length_eq]; omega)
       let next₂ := t.squares[(i₂.val + 1) % (n*n)]'(by rw [t.length_eq]; omega)
       let c₂ := t.squares[i₂.val]'(by rw [t.length_eq]; exact i₂.isLt)
       isOblique (getMoveVector prev₂ c₂) (getMoveVector c₂ next₂)) ∧
      (let prev₃ := t.squares[(i₃.val + (n*n - 1)) % (n*n)]'(by rw [t.length_eq]; omega)
       let next₃ := t.squares[(i₃.val + 1) % (n*n)]'(by rw [t.length_eq]; omega)
       let c₃ := t.squares[i₃.val]'(by rw [t.length_eq]; exact i₃.isLt)
       isOblique (getMoveVector prev₃ c₃) (getMoveVector c₃ next₃)) ∧
      (let prev₄ := t.squares[(i₄.val + (n*n - 1)) % (n*n)]'(by rw [t.length_eq]; omega)
       let next₄ := t.squares[(i₄.val + 1) % (n*n)]'(by rw [t.length_eq]; omega)
       let c₄ := t.squares[i₄.val]'(by rw [t.length_eq]; exact i₄.isLt)
       isOblique (getMoveVector prev₄ c₄) (getMoveVector c₄ next₄)) := by
  -- Get corner positions in the tour
  have hnn : n * n ≥ 25 := by nlinarith

  have hcTL : cornerTL n (by omega) ∈ t.squares := tour_visits_all n t _
  have hcTR : cornerTR n (by omega) ∈ t.squares := tour_visits_all n t _
  have hcBL : cornerBL n (by omega) ∈ t.squares := tour_visits_all n t _
  have hcBR : cornerBR n (by omega) ∈ t.squares := tour_visits_all n t _

  obtain ⟨⟨iTL, hiTL⟩, heqTL⟩ := List.mem_iff_get.mp hcTL
  obtain ⟨⟨iTR, hiTR⟩, heqTR⟩ := List.mem_iff_get.mp hcTR
  obtain ⟨⟨iBL, hiBL⟩, heqBL⟩ := List.mem_iff_get.mp hcBL
  obtain ⟨⟨iBR, hiBR⟩, heqBR⟩ := List.mem_iff_get.mp hcBR

  -- All indices are < n²
  have hiTL_lt : iTL < n * n := by rw [t.length_eq] at hiTL; exact hiTL
  have hiTR_lt : iTR < n * n := by rw [t.length_eq] at hiTR; exact hiTR
  have hiBL_lt : iBL < n * n := by rw [t.length_eq] at hiBL; exact hiBL
  have hiBR_lt : iBR < n * n := by rw [t.length_eq] at hiBR; exact hiBR

  -- Corner indices are pairwise distinct
  have hdist := corners_distinct n (by omega)
  have hne12 : iTL ≠ iTR := by
    intro h; exact hdist.1 (heqTL.symm.trans (by rw [show iTL = iTR from h]; exact heqTR))
  have hne13 : iTL ≠ iBL := by
    intro h; exact hdist.2.1 (heqTL.symm.trans (by rw [show iTL = iBL from h]; exact heqBL))
  have hne14 : iTL ≠ iBR := by
    intro h; exact hdist.2.2.1 (heqTL.symm.trans (by rw [show iTL = iBR from h]; exact heqBR))
  have hne23 : iTR ≠ iBL := by
    intro h; exact hdist.2.2.2.1 (heqTR.symm.trans (by rw [show iTR = iBL from h]; exact heqBL))
  have hne24 : iTR ≠ iBR := by
    intro h; exact hdist.2.2.2.2.1 (heqTR.symm.trans (by rw [show iTR = iBR from h]; exact heqBR))
  have hne34 : iBL ≠ iBR := by
    intro h; exact hdist.2.2.2.2.2 (heqBL.symm.trans (by rw [show iBL = iBR from h]; exact heqBR))

  -- Use the corner indices
  refine ⟨⟨iTL, hiTL_lt⟩, ⟨iTR, hiTR_lt⟩, ⟨iBL, hiBL_lt⟩, ⟨iBR, hiBR_lt⟩,
          hne12, hne13, hne14, hne23, hne24, hne34, ?_, ?_, ?_, ?_⟩

  -- For each corner, prove the turn is oblique using corner_forces_oblique
  -- Helper: at corner position j, prev = squares[(j+n²-1)%n²], next = squares[(j+1)%n²]
  -- The prev→corner→next turn is oblique because both prev and next are the 2 corner neighbors.

  · -- Corner TL at position iTL
    have hadj_prev : (knightGraphN n).Adj
        (t.squares[(iTL + (n*n - 1)) % (n*n)]'(by rw [t.length_eq]; omega))
        (t.squares[iTL]'(by rw [t.length_eq]; exact hiTL_lt)) := by
      have h := tour_cyclic_adj n t ⟨(iTL + (n*n - 1)) % (n*n), by omega⟩
      have hmod : ((iTL + (n*n - 1)) % (n*n) + 1) % (n*n) = iTL := by omega
      rw [hmod] at h; exact h
    have hadj_next : (knightGraphN n).Adj
        (t.squares[iTL]'(by rw [t.length_eq]; exact hiTL_lt))
        (t.squares[(iTL + 1) % (n*n)]'(by rw [t.length_eq]; omega)) := by
      exact tour_cyclic_adj n t ⟨iTL, hiTL_lt⟩
    have hpn_ne : (iTL + (n*n - 1)) % (n*n) ≠ (iTL + 1) % (n*n) := by omega
    have hsq_ne := tour_index_neq n t _ _ (by omega) (by omega) hpn_ne
    rw [← heqTL] at hadj_prev hadj_next
    exact corner_forces_oblique n hn _ (Or.inl heqTL) _ _
      (heqTL ▸ hadj_prev) (heqTL ▸ hadj_next) hsq_ne

  · -- Corner TR at position iTR
    have hadj_prev : (knightGraphN n).Adj
        (t.squares[(iTR + (n*n - 1)) % (n*n)]'(by rw [t.length_eq]; omega))
        (t.squares[iTR]'(by rw [t.length_eq]; exact hiTR_lt)) := by
      have h := tour_cyclic_adj n t ⟨(iTR + (n*n - 1)) % (n*n), by omega⟩
      have hmod : ((iTR + (n*n - 1)) % (n*n) + 1) % (n*n) = iTR := by omega
      rw [hmod] at h; exact h
    have hadj_next : (knightGraphN n).Adj
        (t.squares[iTR]'(by rw [t.length_eq]; exact hiTR_lt))
        (t.squares[(iTR + 1) % (n*n)]'(by rw [t.length_eq]; omega)) := by
      exact tour_cyclic_adj n t ⟨iTR, hiTR_lt⟩
    have hpn_ne : (iTR + (n*n - 1)) % (n*n) ≠ (iTR + 1) % (n*n) := by omega
    have hsq_ne := tour_index_neq n t _ _ (by omega) (by omega) hpn_ne
    rw [← heqTR] at hadj_prev hadj_next
    exact corner_forces_oblique n hn _ (Or.inr (Or.inl heqTR)) _ _
      (heqTR ▸ hadj_prev) (heqTR ▸ hadj_next) hsq_ne

  · -- Corner BL at position iBL
    have hadj_prev : (knightGraphN n).Adj
        (t.squares[(iBL + (n*n - 1)) % (n*n)]'(by rw [t.length_eq]; omega))
        (t.squares[iBL]'(by rw [t.length_eq]; exact hiBL_lt)) := by
      have h := tour_cyclic_adj n t ⟨(iBL + (n*n - 1)) % (n*n), by omega⟩
      have hmod : ((iBL + (n*n - 1)) % (n*n) + 1) % (n*n) = iBL := by omega
      rw [hmod] at h; exact h
    have hadj_next : (knightGraphN n).Adj
        (t.squares[iBL]'(by rw [t.length_eq]; exact hiBL_lt))
        (t.squares[(iBL + 1) % (n*n)]'(by rw [t.length_eq]; omega)) := by
      exact tour_cyclic_adj n t ⟨iBL, hiBL_lt⟩
    have hpn_ne : (iBL + (n*n - 1)) % (n*n) ≠ (iBL + 1) % (n*n) := by omega
    have hsq_ne := tour_index_neq n t _ _ (by omega) (by omega) hpn_ne
    rw [← heqBL] at hadj_prev hadj_next
    exact corner_forces_oblique n hn _ (Or.inr (Or.inr (Or.inl heqBL))) _ _
      (heqBL ▸ hadj_prev) (heqBL ▸ hadj_next) hsq_ne

  · -- Corner BR at position iBR
    have hadj_prev : (knightGraphN n).Adj
        (t.squares[(iBR + (n*n - 1)) % (n*n)]'(by rw [t.length_eq]; omega))
        (t.squares[iBR]'(by rw [t.length_eq]; exact hiBR_lt)) := by
      have h := tour_cyclic_adj n t ⟨(iBR + (n*n - 1)) % (n*n), by omega⟩
      have hmod : ((iBR + (n*n - 1)) % (n*n) + 1) % (n*n) = iBR := by omega
      rw [hmod] at h; exact h
    have hadj_next : (knightGraphN n).Adj
        (t.squares[iBR]'(by rw [t.length_eq]; exact hiBR_lt))
        (t.squares[(iBR + 1) % (n*n)]'(by rw [t.length_eq]; omega)) := by
      exact tour_cyclic_adj n t ⟨iBR, hiBR_lt⟩
    have hpn_ne : (iBR + (n*n - 1)) % (n*n) ≠ (iBR + 1) % (n*n) := by omega
    have hsq_ne := tour_index_neq n t _ _ (by omega) (by omega) hpn_ne
    rw [← heqBR] at hadj_prev hadj_next
    exact corner_forces_oblique n hn _ (Or.inr (Or.inr (Or.inr heqBR))) _ _
      (heqBR ▸ hadj_prev) (heqBR ▸ hadj_next) hsq_ne

end KnightsTourObliqueGeneral
