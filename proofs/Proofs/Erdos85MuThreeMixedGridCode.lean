import Proofs.Erdos85CrossEdgeTriangleDichotomy

/-!
# Uniform mixed grid code for the `mu = 3` exterior

This is the runtime-independent combinatorial target of the mixed-colouring
branch.  `H` is the internal ambient two-factor, `K` is the two-factor of
forbidden grid cells, and `C` is the exterior graph on `X × Y \ K`.
-/

open SimpleGraph

namespace Erdos85

/-- The bipartite graph associated to a relation between two shores. -/
def relationBipartiteGraph {X Y : Type*} (R : X → Y → Prop) :
    SimpleGraph (X ⊕ Y) where
  Adj a b := match a, b with
    | Sum.inl x, Sum.inr y => R x y
    | Sum.inr y, Sum.inl x => R x y
    | _, _ => False
  symm := by
    constructor
    intro a b
    cases a <;> cases b <;> simp_all
  loopless := by
    constructor
    intro a
    cases a <;> simp

/-- Two neighbours at every point on both shores. -/
def RelationTwoRegular {X Y : Type*} [Fintype X] [Fintype Y]
    (R : X → Y → Prop) [DecidableRel R] : Prop :=
  (∀ x, ((Finset.univ : Finset Y).filter fun y => R x y).card = 2) ∧
  (∀ y, ((Finset.univ : Finset X).filter fun x => R x y).card = 2)

/-- On every connected component of the `H`-factor, its edges are either all
`K`-edges or all disjoint from `K`. -/
def RelationFactorCycleCompatible {X Y : Type*}
    (H K : X → Y → Prop) : Prop :=
  ∀ c : (relationBipartiteGraph H).ConnectedComponent,
    (∀ x y, H x y → Sum.inl x ∈ c.supp → K x y) ∨
    (∀ x y, H x y → Sum.inl x ∈ c.supp → ¬ K x y)

/-- Cells outside the forbidden factor `K`. -/
def muThreeMixedCell {X Y : Type*} (K : X → Y → Prop) :=
  {p : X × Y // ¬ K p.1 p.2}

instance muThreeMixedCellDecidableEq {X Y : Type*}
    [DecidableEq X] [DecidableEq Y] (K : X → Y → Prop) :
    DecidableEq (muThreeMixedCell K) := by
  unfold muThreeMixedCell
  infer_instance

instance muThreeMixedCellFintype {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K] :
    Fintype (muThreeMixedCell K) := by
  unfold muThreeMixedCell
  infer_instance

/-- The exact uniform code conditions furnished by the graph-theoretic
reduction.  No all-triangle-free assumption (`H = K`) is made. -/
structure MuThreeMixedGridCode
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K))
    [DecidableRel C.Adj] : Prop where
  card_left : Fintype.card X = 8
  card_right : Fintype.card Y = 8
  H_twoRegular : RelationTwoRegular H
  K_twoRegular : RelationTwoRegular K
  cycle_compatible : RelationFactorCycleCompatible H K
  row_hit : ∀ (u : muThreeMixedCell K) (x : X),
    ((C.neighborFinset u).filter fun v => v.1.1 = x).card =
      if H x u.1.2 then 0 else 1
  column_hit : ∀ (u : muThreeMixedCell K) (y : Y),
    ((C.neighborFinset u).filter fun v => v.1.2 = y).card =
      if H u.1.1 y then 0 else 1
  rook : ∀ u v w, C.Adj u v → C.Adj u w → v ≠ w →
    v.1.1 ≠ w.1.1 ∧ v.1.2 ≠ w.1.2
  c4Free : ¬ containsC4 (muThreeMixedCell K) C

/-- Row-hit law in existence-and-uniqueness form. -/
theorem MuThreeMixedGridCode.existsUnique_row_neighbor_iff
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) :
    (∃! v, C.Adj u v ∧ v.1.1 = x) ↔ ¬ H x u.1.2 := by
  let R := (C.neighborFinset u).filter fun v => v.1.1 = x
  constructor
  · rintro ⟨v, hv, _⟩ hH
    have hvR : v ∈ R := Finset.mem_filter.mpr
      ⟨(C.mem_neighborFinset u v).mpr hv.1, hv.2⟩
    have hzero : R.card = 0 := by
      simpa [R, hH] using code.row_hit u x
    rw [Finset.card_eq_zero.mp hzero] at hvR
    simp at hvR
  · intro hnH
    have hone : R.card = 1 := by
      simpa [R, hnH] using code.row_hit u x
    obtain ⟨v, hvEq⟩ := Finset.card_eq_one.mp hone
    have hvR : v ∈ R := by rw [hvEq]; simp
    refine ⟨v, ⟨(C.mem_neighborFinset u v).mp (Finset.mem_filter.mp hvR).1,
      (Finset.mem_filter.mp hvR).2⟩, ?_⟩
    intro w hw
    have hwR : w ∈ R := Finset.mem_filter.mpr
      ⟨(C.mem_neighborFinset u w).mpr hw.1, hw.2⟩
    rw [hvEq] at hwR
    simpa using hwR

/-- Column dual of the row uniqueness law. -/
theorem MuThreeMixedGridCode.existsUnique_column_neighbor_iff
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) :
    (∃! v, C.Adj u v ∧ v.1.2 = y) ↔ ¬ H u.1.1 y := by
  let R := (C.neighborFinset u).filter fun v => v.1.2 = y
  constructor
  · rintro ⟨v, hv, _⟩ hH
    have hvR : v ∈ R := Finset.mem_filter.mpr
      ⟨(C.mem_neighborFinset u v).mpr hv.1, hv.2⟩
    have hzero : R.card = 0 := by
      simpa [R, hH] using code.column_hit u y
    rw [Finset.card_eq_zero.mp hzero] at hvR
    simp at hvR
  · intro hnH
    have hone : R.card = 1 := by
      simpa [R, hnH] using code.column_hit u y
    obtain ⟨v, hvEq⟩ := Finset.card_eq_one.mp hone
    have hvR : v ∈ R := by rw [hvEq]; simp
    refine ⟨v, ⟨(C.mem_neighborFinset u v).mp (Finset.mem_filter.mp hvR).1,
      (Finset.mem_filter.mp hvR).2⟩, ?_⟩
    intro w hw
    have hwR : w ∈ R := Finset.mem_filter.mpr
      ⟨(C.mem_neighborFinset u w).mpr hw.1, hw.2⟩
    rw [hvEq] at hwR
    simpa using hwR

/-- The precise uniform combinatorial terminal still to prove. -/
def MuThreeMixedGridCodeImpossible : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj],
    ¬ MuThreeMixedGridCode H K C

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.existsUnique_row_neighbor_iff
#print axioms Erdos85.MuThreeMixedGridCode.existsUnique_column_neighbor_iff
