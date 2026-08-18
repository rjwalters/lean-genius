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

theorem mu3NormalizedRowInter_card_eq
    (Hrows : Nat → Mu3KRow)
    (H K : Fin 8 → Fin 8 → Prop) [DecidableRel H] [DecidableRel K]
    (hH : ∀ x y, H x y ↔ y.val ∈ Hrows x.val)
    (x x' : Fin 8) :
    (((Finset.univ.filter fun y => K x y).image Fin.val) ∩
        Hrows x'.val).card =
      ((Finset.univ.filter fun y => K x y) ∩
        (Finset.univ.filter fun y => H x' y)).card := by
  have heq :
      ((Finset.univ.filter fun y => K x y).image Fin.val) ∩ Hrows x'.val =
        (((Finset.univ.filter fun y => K x y) ∩
          (Finset.univ.filter fun y => H x' y)).image Fin.val) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnK, hnH⟩ := Finset.mem_inter.mp hn
      obtain ⟨y, hyK, hyn⟩ := Finset.mem_image.mp hnK
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_inter.mpr ⟨hyK, ?_⟩, hyn⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (hH x' y).2 ?_⟩
      simpa [hyn] using hnH
    · intro hn
      obtain ⟨y, hy, hyn⟩ := Finset.mem_image.mp hn
      obtain ⟨hyK, hyH⟩ := Finset.mem_inter.mp hy
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_image.mpr ⟨y, hyK, hyn⟩, ?_⟩
      have := (hH x' y).1 (Finset.mem_filter.mp hyH).2
      simpa [hyn] using this
  rw [heq, Finset.card_image_of_injective _ Fin.val_injective]

theorem mu3NormalizedColumnInter_card_eq
    (Hrows : Nat → Mu3KRow)
    (H K : Fin 8 → Fin 8 → Prop) [DecidableRel H] [DecidableRel K]
    (hH : ∀ x y, H x y ↔ y.val ∈ Hrows x.val)
    (y y' : Fin 8) :
    (((Finset.univ.filter fun x => K x y).image Fin.val) ∩
        mu3HColumn Hrows y'.val).card =
      ((Finset.univ.filter fun x => K x y) ∩
        (Finset.univ.filter fun x => H x y')).card := by
  have heq :
      ((Finset.univ.filter fun x => K x y).image Fin.val) ∩
          mu3HColumn Hrows y'.val =
        (((Finset.univ.filter fun x => K x y) ∩
          (Finset.univ.filter fun x => H x y')).image Fin.val) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnK, hnH⟩ := Finset.mem_inter.mp hn
      obtain ⟨x, hxK, hxn⟩ := Finset.mem_image.mp hnK
      apply Finset.mem_image.mpr
      refine ⟨x, Finset.mem_inter.mpr ⟨hxK, ?_⟩, hxn⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (hH x y').2 ?_⟩
      have hnH' := Finset.mem_filter.mp hnH
      simpa [mu3HColumn, hxn] using hnH'.2
    · intro hn
      obtain ⟨x, hx, hxn⟩ := Finset.mem_image.mp hn
      obtain ⟨hxK, hxH⟩ := Finset.mem_inter.mp hx
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_image.mpr ⟨x, hxK, hxn⟩, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by simpa [hxn] using x.isLt), ?_⟩
      have := (hH x y').1 (Finset.mem_filter.mp hxH).2
      simpa [hxn] using this
  rw [heq, Finset.card_image_of_injective _ Fin.val_injective]

/-- Shape-facing exhaustive-provider socket.  Once coordinates identify the
ambient factor `H` and cycle compatibility supplies the sector equation, all
remaining degree/symmetry transport and candidate pullback is automatic. -/
theorem exists_mu3KSectorCandidate_of_coordinates
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (Hrows T : Nat → Mu3KRow)
    (hHtwo : RelationTwoRegular H) (hKtwo : RelationTwoRegular K)
    (hHcoord : ∀ x y,
      mu3NormalizeRelation row column H x y ↔ y.val ∈ Hrows x.val)
    (hsector : ∀ x : Fin 8,
      ((Finset.univ.filter fun y =>
          mu3NormalizeRelation row column K x y).image Fin.val) ∩
        Hrows x.val = T x.val)
    (hrowSymm : ∀ x x',
      Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
        Fintype.card {y : Y // H x y ∧ ¬ K x' y})
    (hcolumnSymm : ∀ y y',
      Fintype.card {x : X // H x y' ∧ ¬ K x y} =
        Fintype.card {x : X // H x y ∧ ¬ K x y'}) :
    ∃ i : {rows : Mu3KRows // rows ∈ mu3KSectorEnumeration Hrows T},
      ∀ x y, K x y ↔
        mu3PullbackCandidate row column
          (fun i : {rows : Mu3KRows // rows ∈ mu3KSectorEnumeration Hrows T} =>
            mu3KRowsCandidate i.1) i x y = true := by
  let Kn := mu3NormalizeRelation row column K
  let Hn := mu3NormalizeRelation row column H
  have hKnTwo : RelationTwoRegular Kn :=
    mu3NormalizeRelation_twoRegular row column K hKtwo
  have hrowI : ∀ x x' : Fin 8,
      (((Finset.univ.filter fun y => Kn x y).image Fin.val) ∩
          Hrows x'.val).card =
        (((Finset.univ.filter fun y => Kn x' y).image Fin.val) ∩
          Hrows x.val).card := by
    intro x x'
    rw [mu3NormalizedRowInter_card_eq Hrows Hn Kn hHcoord x x',
      mu3NormalizedRowInter_card_eq Hrows Hn Kn hHcoord x' x]
    exact mu3NormalizeRelation_row_inter_symmetry
      row column H K hHtwo hrowSymm x x'
  have hcolumnI : ∀ y y' : Fin 8,
      (((Finset.univ.filter fun x => Kn x y).image Fin.val) ∩
          mu3HColumn Hrows y'.val).card =
        (((Finset.univ.filter fun x => Kn x y').image Fin.val) ∩
          mu3HColumn Hrows y.val).card := by
    intro y y'
    rw [mu3NormalizedColumnInter_card_eq Hrows Hn Kn hHcoord y y',
      mu3NormalizedColumnInter_card_eq Hrows Hn Kn hHcoord y' y]
    exact mu3NormalizeRelation_column_inter_symmetry
      row column H K hHtwo hcolumnSymm y y'
  apply mu3PullbackCandidate_exhaustive row column K
    (fun i : {rows : Mu3KRows // rows ∈ mu3KSectorEnumeration Hrows T} =>
      mu3KRowsCandidate i.1)
  exact exists_mu3KSectorCandidate_of_normalized Hrows T Kn
    hKnTwo.1 hKnTwo.2 hsector hrowI hcolumnI

end Erdos85

#print axioms Erdos85.mu3NormalizeRelation_twoRegular
#print axioms Erdos85.mu3NormalizeRelation_row_sdiff_symmetry
#print axioms Erdos85.mu3NormalizeRelation_column_sdiff_symmetry
#print axioms Erdos85.mu3NormalizeRelation_row_inter_symmetry
#print axioms Erdos85.mu3NormalizeRelation_column_inter_symmetry
#print axioms Erdos85.mu3PullbackCandidate_exhaustive
#print axioms Erdos85.mu3NormalizedRowInter_card_eq
#print axioms Erdos85.mu3NormalizedColumnInter_card_eq
#print axioms Erdos85.exists_mu3KSectorCandidate_of_coordinates
