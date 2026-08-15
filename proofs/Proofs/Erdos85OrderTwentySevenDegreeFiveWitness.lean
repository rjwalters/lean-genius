import Proofs.Erdos85Problem

/-!
# An order-27 degree-five witness

This finite certificate is a `C₄`-free graph with 68 edges: 26 vertices have
degree five and one has degree six.  It fills the only order not supplied by
the small polarity deletion patterns in the degree-five witness band.
-/

namespace Erdos85

def orderTwentySevenDegreeFiveEdges : List (Nat × Nat) := [
  (0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,16),(1,20),(1,26),(2,5),(2,9),
  (2,12),(2,18),(3,7),(3,10),(3,15),(3,22),(4,6),(4,8),(4,25),(5,11),
  (5,17),(5,23),(6,13),(6,15),(6,17),(6,24),(7,13),(7,14),(7,16),(7,22),
  (8,10),(8,14),(8,19),(8,25),(9,14),(9,20),(9,21),(9,24),(10,11),
  (10,15),(10,19),(11,13),(11,20),(11,23),(12,15),(12,16),(12,18),
  (12,25),(13,18),(13,20),(14,16),(14,24),(15,24),(16,17),(17,19),
  (17,21),(18,19),(18,26),(19,26),(20,21),(21,22),(21,25),(22,23),
  (22,25),(22,26),(23,24),(23,26)]

def orderTwentySevenDegreeFiveAdj (i j : Fin 27) : Prop :=
  (i.val, j.val) ∈ orderTwentySevenDegreeFiveEdges ∨
    (j.val, i.val) ∈ orderTwentySevenDegreeFiveEdges

instance : DecidableRel orderTwentySevenDegreeFiveAdj := fun i j => by
  unfold orderTwentySevenDegreeFiveAdj
  infer_instance

def orderTwentySevenDegreeFiveGraph : SimpleGraph (Fin 27) where
  Adj := orderTwentySevenDegreeFiveAdj
  symm.symm := by
    intro i j h
    unfold orderTwentySevenDegreeFiveAdj at h ⊢
    tauto
  loopless.irrefl := by native_decide

instance : DecidableRel orderTwentySevenDegreeFiveGraph.Adj := fun i j =>
  decidable_of_iff (orderTwentySevenDegreeFiveAdj i j) Iff.rfl

theorem orderTwentySevenDegreeFiveGraph_degree_ge :
    ∀ v, 5 ≤ orderTwentySevenDegreeFiveGraph.degree v := by
  native_decide

theorem orderTwentySevenDegreeFiveGraph_common_le_one :
    ∀ x y : Fin 27, x ≠ y →
      (orderTwentySevenDegreeFiveGraph.neighborFinset x ∩
        orderTwentySevenDegreeFiveGraph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem orderTwentySevenDegreeFiveGraph_not_containsC4 :
    ¬ containsC4 (Fin 27) orderTwentySevenDegreeFiveGraph :=
  not_containsC4_of_forall_common_le_one
    orderTwentySevenDegreeFiveGraph_common_le_one

theorem orderTwentySeven_degreeFive_witness :
    C4FreeMinDegreeWitness 27 5 := by
  refine ⟨orderTwentySevenDegreeFiveGraph, inferInstance, ?_,
    orderTwentySevenDegreeFiveGraph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  exact orderTwentySevenDegreeFiveGraph_degree_ge

end Erdos85
