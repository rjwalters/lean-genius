import Proofs.Erdos85MuThreeAllTfShapeCoordinates

/-! # Exterior labels occupy the non-hole cells in the all-TF sector -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem mu3AllTf_cell_mem_iff
    (shape : Mu3AllTfShape) (x y : Fin 8) :
    x.val * 8 + y.val ∈ mu3AllTfCells shape ↔
      ¬ mu3AllTfInternal shape x.val y.val := by
  have hdiv : (x.val * 8 + y.val) / 8 = x.val := by omega
  have hmod : (x.val * 8 + y.val) % 8 = y.val := by omega
  simp [mu3AllTfCells, hdiv, hmod]
  omega

/-- A coordinate system on the positive and negative sign classes whose
holes are exactly the internal ambient edges. -/
structure Mu3InternalCoordinateModel
    {V : Type*} (G : SimpleGraph V)
    (P N : Type*) [DecidableEq P] [DecidableEq N]
    (pval : P → V) (nval : N → V) (shape : Mu3AllTfShape) where
  row : P ≃ Fin 8
  column : N ≃ Fin 8
  hole_iff : ∀ p n, G.Adj (pval p) (nval n) ↔
    mu3AllTfInternal shape (row p).val (column n).val

def mu3ExteriorCell
    {V P N W : Type*} (G : SimpleGraph V)
    [DecidableEq P] [DecidableEq N]
    (pval : P → V) (nval : N → V) (shape : Mu3AllTfShape)
    (model : Mu3InternalCoordinateModel G P N pval nval shape)
    (label : W → P × N) (w : W) : Nat :=
  (model.row (label w).1).val * 8 + (model.column (label w).2).val

theorem mu3ExteriorCell_mem_of_allTf
    {V P N W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq P] [DecidableEq N]
    (pval : P → V) (nval : N → V) (shape : Mu3AllTfShape)
    (model : Mu3InternalCoordinateModel G P N pval nval shape)
    (label : W → P × N)
    (center : W → V)
    (hadj : ∀ w, G.Adj (center w) (pval (label w).1) ∧
      G.Adj (center w) (nval (label w).2))
    (hallTf : ∀ p n, G.Adj (pval p) (nval n) →
      (triangleFreeEdgeGraph G).Adj (pval p) (nval n))
    (w : W) :
    mu3ExteriorCell G pval nval shape model label w ∈
      mu3AllTfCells shape := by
  change (model.row (label w).1).val * 8 +
    (model.column (label w).2).val ∈ mu3AllTfCells shape
  rw [mu3AllTf_cell_mem_iff]
  intro hhole
  have hpn : G.Adj (pval (label w).1) (nval (label w).2) :=
    (model.hole_iff _ _).2 hhole
  have htf := hallTf _ _ hpn
  have hzero :
      (G.neighborFinset (pval (label w).1) ∩
        G.neighborFinset (nval (label w).2)).card = 0 :=
    ((mem_triangleFreeNeighbors G _ _).mp
      ((triangleFreeEdgeGraph_adj G _ _).mp htf)).2
  have hcenter : center w ∈
      G.neighborFinset (pval (label w).1) ∩
        G.neighborFinset (nval (label w).2) :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr (hadj w).1.symm,
        (G.mem_neighborFinset _ _).mpr (hadj w).2.symm⟩
  rw [Finset.card_eq_zero.mp hzero] at hcenter
  exact Finset.notMem_empty _ hcenter

def mu3ExteriorOccupiedCoord
    {V P N W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq P] [DecidableEq N]
    (pval : P → V) (nval : N → V) (shape : Mu3AllTfShape)
    (model : Mu3InternalCoordinateModel G P N pval nval shape)
    (label : W → P × N) (center : W → V)
    (hadj : ∀ w, G.Adj (center w) (pval (label w).1) ∧
      G.Adj (center w) (nval (label w).2))
    (hallTf : ∀ p n, G.Adj (pval p) (nval n) →
      (triangleFreeEdgeGraph G).Adj (pval p) (nval n)) :
    W → {cell : Nat // cell ∈ mu3AllTfCells shape} := fun w =>
  ⟨mu3ExteriorCell G pval nval shape model label w,
    mu3ExteriorCell_mem_of_allTf G pval nval shape model label center
      hadj hallTf w⟩

theorem mu3ExteriorOccupiedCoord_injective
    {V P N W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq P] [DecidableEq N]
    (pval : P → V) (nval : N → V) (shape : Mu3AllTfShape)
    (model : Mu3InternalCoordinateModel G P N pval nval shape)
    (label : W → P × N) (hlabel : Function.Injective label)
    (center : W → V)
    (hadj : ∀ w, G.Adj (center w) (pval (label w).1) ∧
      G.Adj (center w) (nval (label w).2))
    (hallTf : ∀ p n, G.Adj (pval p) (nval n) →
      (triangleFreeEdgeGraph G).Adj (pval p) (nval n)) :
    Function.Injective
      (mu3ExteriorOccupiedCoord G pval nval shape model label center
        hadj hallTf) := by
  intro u v huv
  apply hlabel
  apply Prod.ext
  · apply model.row.injective
    apply Fin.ext
    have hval := congrArg (fun z => z.1) huv
    change (model.row (label u).1).val * 8 +
        (model.column (label u).2).val =
      (model.row (label v).1).val * 8 +
        (model.column (label v).2).val at hval
    omega
  · apply model.column.injective
    apply Fin.ext
    have hval := congrArg (fun z => z.1) huv
    change (model.row (label u).1).val * 8 +
        (model.column (label u).2).val =
      (model.row (label v).1).val * 8 +
        (model.column (label v).2).val at hval
    omega

/-- The complete exterior enumeration produced by an internal coordinate
model in the all-TF sector. -/
def mu3ExteriorEquivOfInternalCoordinateModel
    {V P N W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq P] [DecidableEq N]
    (pval : P → V) (nval : N → V) (shape : Mu3AllTfShape)
    (model : Mu3InternalCoordinateModel G P N pval nval shape)
    (label : W → P × N) (hlabel : Function.Injective label)
    (center : W → V)
    (hadj : ∀ w, G.Adj (center w) (pval (label w).1) ∧
      G.Adj (center w) (nval (label w).2))
    (hallTf : ∀ p n, G.Adj (pval p) (nval n) →
      (triangleFreeEdgeGraph G).Adj (pval p) (nval n))
    (hcard : Fintype.card W = 48) : Fin 48 ≃ W :=
  mu3ExteriorEquivOfCoordinateInjection shape hcard
    (mu3ExteriorOccupiedCoord G pval nval shape model label center hadj hallTf)
    (mu3ExteriorOccupiedCoord_injective G pval nval shape model label hlabel
      center hadj hallTf)

end

end Erdos85
