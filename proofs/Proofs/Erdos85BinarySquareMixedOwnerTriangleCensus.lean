import Proofs.Erdos85BinarySquareMixedOwnerCubicTrace

/-! # Combinatorial census for mixed owner cubic traces -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ordered triples whose three cyclic edges lie in three prescribed graphs. -/
def cyclicColoredTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    Finset (V × V × V) :=
  Finset.univ.filter fun p =>
    A.Adj p.1 p.2.2 ∧ B.Adj p.2.2 p.2.1 ∧ C.Adj p.2.1 p.1

/-- A mixed cubic adjacency trace is the cardinality of the corresponding
ordered, cyclically colored triples. -/
theorem trace_three_adjMatrices_eq_card_cyclicColoredTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    Matrix.trace (A.adjMatrix ℤ * B.adjMatrix ℤ * C.adjMatrix ℤ) =
      (cyclicColoredTriples A B C).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  push_cast
  simp only [cyclicColoredTriples, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    SimpleGraph.adjMatrix_apply, -Finset.sum_const, -Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  by_cases hC : C.Adj z x <;> simp [hC]
  rw [Finset.card_eq_sum_ones]
  push_cast
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hA : A.Adj x y <;> by_cases hB : B.Adj y z <;> simp [hA, hB]

/-- In the four-component order-64 branch, every ordered triple of distinct
owner colors occurs on exactly `3584` ordered ambient vertex triples. -/
theorem orderSixtyFour_regular_fourComponents_card_mixedOwnerTriangles
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (cyclicColoredTriples
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)).card = 3584 := by
  have h := orderSixtyFour_regular_fourComponents_trace_three_distinct_ownerMatrices
    G hfree hreg hcount a b c hab hac hbc
  rw [trace_three_adjMatrices_eq_card_cyclicColoredTriples] at h
  exact_mod_cast h

set_option maxRecDepth 10000 in
/-- In particular, each ordered choice of three distinct owner colors occurs
on an ambient cyclic triangle. -/
theorem orderSixtyFour_regular_fourComponents_exists_mixedOwnerTriangle
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ x y z : Fin 64,
      (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x y ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y z ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z x := by
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  let C := componentOwnerGraph G (secondOrderDefectGraph G) c
  have hcard : (cyclicColoredTriples A B C).card = 3584 :=
    orderSixtyFour_regular_fourComponents_card_mixedOwnerTriangles
      G hfree hreg hcount a b c hab hac hbc
  have hnonempty : (cyclicColoredTriples A B C).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hnonempty
  have hp' : A.Adj p.1 p.2.2 ∧ B.Adj p.2.2 p.2.1 ∧ C.Adj p.2.1 p.1 := by
    change p ∈ Finset.univ.filter (fun p : Fin 64 × Fin 64 × Fin 64 =>
      A.Adj p.1 p.2.2 ∧ B.Adj p.2.2 p.2.1 ∧ C.Adj p.2.1 p.1) at hp
    exact (Finset.mem_filter.mp hp).2
  exact ⟨p.1, p.2.2, p.2.1, hp'⟩

end

end Erdos85
