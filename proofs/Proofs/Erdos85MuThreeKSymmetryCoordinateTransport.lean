import Proofs.Erdos85MuThreeKSymmetryNormalizedAdapter
import Proofs.Erdos85MuThreeKSymmetryCardBridge
import Proofs.Erdos85MuThreeMixedGridCode

/-! # Coordinate transport for the mu-three K relation -/

namespace Erdos85

def mu3NormalizeRelation
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (R : X → Y → Prop) : Fin 8 → Fin 8 → Prop :=
  fun x y => R (row.symm x) (column.symm y)

instance mu3NormalizeRelation_decidable
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (R : X → Y → Prop) [DecidableRel R] :
    DecidableRel (mu3NormalizeRelation row column R) := by
  intro x y
  unfold mu3NormalizeRelation
  infer_instance

def mu3NormalizeRowFiberEquiv
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (R : X → Y → Prop) (x : Fin 8) :
    {y : Fin 8 // mu3NormalizeRelation row column R x y} ≃
      {y : Y // R (row.symm x) y} where
  toFun y := ⟨column.symm y.1, y.2⟩
  invFun y := ⟨column y.1, by simpa [mu3NormalizeRelation] using y.2⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

def mu3NormalizeColumnFiberEquiv
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (R : X → Y → Prop) (y : Fin 8) :
    {x : Fin 8 // mu3NormalizeRelation row column R x y} ≃
      {x : X // R x (column.symm y)} where
  toFun x := ⟨row.symm x.1, x.2⟩
  invFun x := ⟨row x.1, by simpa [mu3NormalizeRelation] using x.2⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem mu3NormalizeRelation_row_card
    {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (R : X → Y → Prop) [DecidableRel R] (x : Fin 8) :
    ((Finset.univ : Finset (Fin 8)).filter fun y =>
      mu3NormalizeRelation row column R x y).card =
      ((Finset.univ : Finset Y).filter fun y => R (row.symm x) y).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (mu3NormalizeRowFiberEquiv row column R x)

theorem mu3NormalizeRelation_column_card
    {X Y : Type*} [Fintype X] [DecidableEq X]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (R : X → Y → Prop) [DecidableRel R] (y : Fin 8) :
    ((Finset.univ : Finset (Fin 8)).filter fun x =>
      mu3NormalizeRelation row column R x y).card =
      ((Finset.univ : Finset X).filter fun x => R x (column.symm y)).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (mu3NormalizeColumnFiberEquiv row column R y)

theorem mu3NormalizeRelation_twoRegular
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (R : X → Y → Prop) [DecidableRel R]
    (hR : RelationTwoRegular R) :
    RelationTwoRegular (mu3NormalizeRelation row column R) := by
  constructor
  · intro x
    rw [mu3NormalizeRelation_row_card]
    exact hR.1 (row.symm x)
  · intro y
    rw [mu3NormalizeRelation_column_card]
    exact hR.2 (column.symm y)

def mu3NormalizeRowSdiffFiberEquiv
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) (x x' : Fin 8) :
    {y : Fin 8 // mu3NormalizeRelation row column H x' y ∧
      ¬ mu3NormalizeRelation row column K x y} ≃
    {y : Y // H (row.symm x') y ∧ ¬ K (row.symm x) y} where
  toFun y := ⟨column.symm y.1, y.2⟩
  invFun y := ⟨column y.1, by
    simpa [mu3NormalizeRelation] using y.2⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

def mu3NormalizeColumnSdiffFiberEquiv
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) (y y' : Fin 8) :
    {x : Fin 8 // mu3NormalizeRelation row column H x y' ∧
      ¬ mu3NormalizeRelation row column K x y} ≃
    {x : X // H x (column.symm y') ∧ ¬ K x (column.symm y)} where
  toFun x := ⟨row.symm x.1, x.2⟩
  invFun x := ⟨row x.1, by
    simpa [mu3NormalizeRelation] using x.2⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem mu3NormalizeRelation_row_sdiff_symmetry
    {X Y : Type*} [Fintype X] [Fintype Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (h : ∀ x x', Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
      Fintype.card {y : Y // H x y ∧ ¬ K x' y})
    (x x' : Fin 8) :
    Fintype.card {y : Fin 8 //
      mu3NormalizeRelation row column H x' y ∧
        ¬ mu3NormalizeRelation row column K x y} =
    Fintype.card {y : Fin 8 //
      mu3NormalizeRelation row column H x y ∧
        ¬ mu3NormalizeRelation row column K x' y} := by
  rw [Fintype.card_congr
      (mu3NormalizeRowSdiffFiberEquiv row column H K x x'),
    Fintype.card_congr
      (mu3NormalizeRowSdiffFiberEquiv row column H K x' x)]
  exact h (row.symm x) (row.symm x')

theorem mu3NormalizeRelation_column_sdiff_symmetry
    {X Y : Type*} [Fintype X] [Fintype Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (h : ∀ y y', Fintype.card {x : X // H x y' ∧ ¬ K x y} =
      Fintype.card {x : X // H x y ∧ ¬ K x y'})
    (y y' : Fin 8) :
    Fintype.card {x : Fin 8 //
      mu3NormalizeRelation row column H x y' ∧
        ¬ mu3NormalizeRelation row column K x y} =
    Fintype.card {x : Fin 8 //
      mu3NormalizeRelation row column H x y ∧
        ¬ mu3NormalizeRelation row column K x y'} := by
  rw [Fintype.card_congr
      (mu3NormalizeColumnSdiffFiberEquiv row column H K y y'),
    Fintype.card_congr
      (mu3NormalizeColumnSdiffFiberEquiv row column H K y' y)]
  exact h (column.symm y) (column.symm y')

theorem mu3NormalizeRelation_row_inter_symmetry
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hH : RelationTwoRegular H)
    (hsymm : ∀ x x', Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
      Fintype.card {y : Y // H x y ∧ ¬ K x' y})
    (x x' : Fin 8) :
    (((Finset.univ.filter fun y =>
        mu3NormalizeRelation row column K x y)) ∩
      (Finset.univ.filter fun y =>
        mu3NormalizeRelation row column H x' y)).card =
    (((Finset.univ.filter fun y =>
        mu3NormalizeRelation row column K x' y)) ∩
      (Finset.univ.filter fun y =>
        mu3NormalizeRelation row column H x y)).card := by
  apply card_inter_eq_of_card_eq_of_card_sdiff_eq
  · rw [mu3NormalizeRelation_row_card,
      mu3NormalizeRelation_row_card]
    rw [hH.1 (row.symm x'), hH.1 (row.symm x)]
  · rw [show
        (Finset.univ.filter fun y => mu3NormalizeRelation row column H x' y) \
          (Finset.univ.filter fun y => mu3NormalizeRelation row column K x y) =
        (Finset.univ.filter fun y =>
          mu3NormalizeRelation row column H x' y ∧
            ¬ mu3NormalizeRelation row column K x y) by ext y; simp,
      show
        (Finset.univ.filter fun y => mu3NormalizeRelation row column H x y) \
          (Finset.univ.filter fun y => mu3NormalizeRelation row column K x' y) =
        (Finset.univ.filter fun y =>
          mu3NormalizeRelation row column H x y ∧
            ¬ mu3NormalizeRelation row column K x' y) by ext y; simp]
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact mu3NormalizeRelation_row_sdiff_symmetry
      row column H K hsymm x x'

theorem mu3NormalizeRelation_column_inter_symmetry
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hH : RelationTwoRegular H)
    (hsymm : ∀ y y', Fintype.card {x : X // H x y' ∧ ¬ K x y} =
      Fintype.card {x : X // H x y ∧ ¬ K x y'})
    (y y' : Fin 8) :
    (((Finset.univ.filter fun x =>
        mu3NormalizeRelation row column K x y)) ∩
      (Finset.univ.filter fun x =>
        mu3NormalizeRelation row column H x y')).card =
    (((Finset.univ.filter fun x =>
        mu3NormalizeRelation row column K x y')) ∩
      (Finset.univ.filter fun x =>
        mu3NormalizeRelation row column H x y)).card := by
  apply card_inter_eq_of_card_eq_of_card_sdiff_eq
  · rw [mu3NormalizeRelation_column_card,
      mu3NormalizeRelation_column_card]
    rw [hH.2 (column.symm y'), hH.2 (column.symm y)]
  · rw [show
        (Finset.univ.filter fun x => mu3NormalizeRelation row column H x y') \
          (Finset.univ.filter fun x => mu3NormalizeRelation row column K x y) =
        (Finset.univ.filter fun x =>
          mu3NormalizeRelation row column H x y' ∧
            ¬ mu3NormalizeRelation row column K x y) by ext x; simp,
      show
        (Finset.univ.filter fun x => mu3NormalizeRelation row column H x y) \
          (Finset.univ.filter fun x => mu3NormalizeRelation row column K x y') =
        (Finset.univ.filter fun x =>
          mu3NormalizeRelation row column H x y ∧
            ¬ mu3NormalizeRelation row column K x y') by ext x; simp]
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact mu3NormalizeRelation_column_sdiff_symmetry
      row column H K hsymm y y'

@[simp] theorem mu3NormalizeRelation_apply_coordinates
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (R : X → Y → Prop) (x : X) (y : Y) :
    mu3NormalizeRelation row column R (row x) (column y) ↔ R x y := by
  simp [mu3NormalizeRelation]

/-- Pull a normalized Boolean candidate table back to the original shores. -/
def mu3PullbackCandidate
    {X Y I : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (candidate : I → Fin 8 → Fin 8 → Bool) : I → X → Y → Bool :=
  fun i x y => candidate i (row x) (column y)

theorem mu3PullbackCandidate_exhaustive
    {X Y I : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (K : X → Y → Prop)
    (candidate : I → Fin 8 → Fin 8 → Bool)
    (h : ∃ i, ∀ x y,
      mu3NormalizeRelation row column K x y ↔ candidate i x y = true) :
    ∃ i, ∀ x y, K x y ↔
      mu3PullbackCandidate row column candidate i x y = true := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  intro x y
  simpa [mu3PullbackCandidate] using hi (row x) (column y)

end Erdos85

#print axioms Erdos85.mu3NormalizeRelation_twoRegular
#print axioms Erdos85.mu3NormalizeRelation_row_sdiff_symmetry
#print axioms Erdos85.mu3NormalizeRelation_column_sdiff_symmetry
#print axioms Erdos85.mu3NormalizeRelation_row_inter_symmetry
#print axioms Erdos85.mu3NormalizeRelation_column_inter_symmetry
#print axioms Erdos85.mu3PullbackCandidate_exhaustive
