import Proofs.Erdos85Problem

/-!
# A C4-free graph on 49 vertices with minimum degree 6

This is the graph obtained from the Erdős--Rényi polarity graph `ER(7)` by
deleting the closed neighborhood of an absolute point.  It has 168 edges:
42 vertices have degree 7 and seven vertices have degree 6.  The finite
checks below use `native_decide` (`Lean.ofReduceBool` is therefore disclosed).
-/

namespace Erdos85

/-- The 168-edge list of the order-49 witness. -/
def orderFortyNineDegreeSixEdges : List (Nat × Nat) :=
[(0, 42), (0, 43), (0, 44), (0, 45), (0, 46), (0, 47), (0, 48), (1, 5), (1, 17), (1, 23), (1, 29), (1, 35), (1, 41), (1, 42), (2, 8), (2, 14), (2, 19), (2, 26), (2, 31), (2, 38), (2, 42), (3, 4), (3, 11), (3, 16), (3, 22), (3, 28), (3, 34), (3, 42), (4, 10), (4, 15), (4, 21), (4, 33), (4, 40), (4, 42), (5, 7), (5, 13), (5, 18), (5, 25), (5, 37), (5, 42), (6, 36), (6, 37), (6, 38), (6, 39), (6, 40), (6, 41), (6, 48), (7, 11), (7, 15), (7, 20), (7, 26), (7, 36), (7, 47), (8, 14), (8, 22), (8, 25), (8, 33), (8, 36), (8, 45), (9, 10), (9, 17), (9, 18), (9, 27), (9, 34), (9, 36), (9, 44), (10, 13), (10, 23), (10, 31), (10, 36), (10, 46), (11, 16), (11, 19), (11, 29), (11, 32), (11, 36), (12, 18), (12, 19), (12, 20), (12, 21), (12, 22), (12, 23), (12, 48), (13, 14), (13, 28), (13, 32), (13, 37), (13, 46), (14, 29), (14, 34), (14, 40), (14, 47), (15, 27), (15, 35), (15, 38), (15, 45), (16, 17), (16, 25), (16, 31), (16, 39), (16, 43), (17, 26), (17, 33), (17, 41), (17, 44), (18, 21), (18, 25), (18, 34), (18, 38), (19, 35), (19, 37), (19, 44), (20, 23), (20, 28), (20, 33), (20, 39), (20, 47), (21, 26), (21, 32), (21, 40), (21, 43), (22, 27), (22, 41), (22, 46), (23, 29), (23, 31), (23, 45), (24, 30), (24, 31), (24, 32), (24, 33), (24, 34), (24, 35), (24, 48), (25, 30), (25, 39), (25, 45), (26, 30), (26, 46), (27, 29), (27, 30), (27, 37), (27, 43), (28, 30), (28, 38), (28, 44), (29, 30), (29, 40), (30, 48), (31, 38), (31, 43), (32, 41), (32, 45), (33, 37), (34, 35), (34, 47), (35, 39), (35, 46), (36, 48), (37, 43), (38, 41), (39, 40), (39, 46), (40, 44), (41, 47), (42, 48), (43, 47), (44, 45)]

def orderFortyNineDegreeSixAdj (i j : Fin 49) : Prop :=
  (i.val, j.val) ∈ orderFortyNineDegreeSixEdges ∨
    (j.val, i.val) ∈ orderFortyNineDegreeSixEdges

instance : DecidableRel orderFortyNineDegreeSixAdj := fun i j => by
  unfold orderFortyNineDegreeSixAdj
  infer_instance

def orderFortyNineDegreeSixGraph : SimpleGraph (Fin 49) where
  Adj := orderFortyNineDegreeSixAdj
  symm.symm := by
    intro i j h
    unfold orderFortyNineDegreeSixAdj at h ⊢
    tauto
  loopless.irrefl := by native_decide

instance : DecidableRel orderFortyNineDegreeSixGraph.Adj := fun i j =>
  decidable_of_iff (orderFortyNineDegreeSixAdj i j) Iff.rfl

/-- Every vertex has degree at least six. -/
theorem orderFortyNineDegreeSixGraph_degree_ge :
    ∀ v, 6 ≤ orderFortyNineDegreeSixGraph.degree v := by
  native_decide

/-- Distinct vertices have at most one common neighbor. -/
theorem orderFortyNineDegreeSixGraph_common_le_one :
    ∀ x y : Fin 49, x ≠ y →
      (orderFortyNineDegreeSixGraph.neighborFinset x ∩
        orderFortyNineDegreeSixGraph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem orderFortyNineDegreeSixGraph_not_containsC4 :
    ¬ containsC4 (Fin 49) orderFortyNineDegreeSixGraph :=
  not_containsC4_of_forall_common_le_one
    orderFortyNineDegreeSixGraph_common_le_one

/-- The checked order-49, minimum-degree-6 witness. -/
theorem orderFortyNine_degreeSix_witness :
    C4FreeMinDegreeWitness 49 6 := by
  refine ⟨orderFortyNineDegreeSixGraph, inferInstance, ?_,
    orderFortyNineDegreeSixGraph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  exact orderFortyNineDegreeSixGraph_degree_ge v

end Erdos85
