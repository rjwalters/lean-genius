import Proofs.Erdos85Problem

/-!
# The Boza order-35 witness

House of Graphs graph 56941, used in Boza's verification of
`R(C₄, K₁,₂₉) = 36`, is a six-regular `C₄`-free graph on 35 vertices.
This realizes `C4FreeMinDegreeWitness 35 6`.  The finite degree and
common-neighbor checks are discharged with `native_decide`.
-/

namespace Erdos85

/-- Edge list of House of Graphs graph 56941 (105 edges). -/
def boza35Edges : List (Nat × Nat) := [
  (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 6), (1, 11),
  (1, 15), (1, 28), (1, 31), (2, 3), (2, 12), (2, 20), (2, 23),
  (2, 24), (3, 13), (3, 16), (3, 25), (3, 26), (4, 5), (4, 18),
  (4, 21), (4, 27), (4, 33), (5, 14), (5, 19), (5, 30), (5, 32),
  (6, 17), (6, 22), (6, 29), (6, 34), (7, 11), (7, 12), (7, 16),
  (7, 17), (7, 18), (7, 19), (8, 13), (8, 20), (8, 27), (8, 29),
  (8, 30), (8, 31), (9, 14), (9, 21), (9, 24), (9, 26), (9, 28),
  (9, 34), (10, 15), (10, 22), (10, 23), (10, 25), (10, 32),
  (10, 33), (11, 12), (11, 13), (11, 14), (11, 15), (12, 20),
  (12, 21), (12, 22), (13, 14), (13, 25), (13, 27), (14, 32),
  (14, 34), (15, 23), (15, 26), (15, 30), (16, 18), (16, 26),
  (16, 31), (16, 32), (17, 19), (17, 23), (17, 27), (17, 34),
  (18, 24), (18, 29), (18, 33), (19, 25), (19, 28), (19, 30),
  (20, 31), (20, 33), (20, 34), (21, 22), (21, 26), (21, 27),
  (22, 29), (22, 32), (23, 24), (23, 27), (24, 28), (24, 29),
  (25, 28), (25, 33), (26, 30), (28, 31), (29, 30), (31, 32),
  (33, 34)
]

def boza35Adj (i j : Fin 35) : Prop :=
  ((i.val, j.val) ∈ boza35Edges ∨ (j.val, i.val) ∈ boza35Edges)

instance : DecidableRel boza35Adj := fun i j => by
  unfold boza35Adj
  infer_instance

def boza35Graph : SimpleGraph (Fin 35) where
  Adj := boza35Adj
  symm.symm := by
    intro i j h
    unfold boza35Adj at h ⊢
    tauto
  loopless.irrefl := by native_decide

instance : DecidableRel boza35Graph.Adj := fun i j =>
  decidable_of_iff (boza35Adj i j) Iff.rfl

theorem boza35Graph_degree : ∀ v, boza35Graph.degree v = 6 := by
  native_decide

theorem boza35Graph_common_le_one : ∀ x y : Fin 35, x ≠ y →
    (boza35Graph.neighborFinset x ∩ boza35Graph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem boza35Graph_not_containsC4 :
    ¬ containsC4 (Fin 35) boza35Graph :=
  not_containsC4_of_forall_common_le_one boza35Graph_common_le_one

/-- The checked order-35, minimum-degree-six witness. -/
theorem boza35_degreeSix_witness : C4FreeMinDegreeWitness 35 6 := by
  refine ⟨boza35Graph, inferInstance, ?_, boza35Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  rw [boza35Graph_degree v]

end Erdos85
