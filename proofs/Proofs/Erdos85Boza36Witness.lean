import Proofs.Erdos85Problem

/-!
# The Boza order-36 witness

House of Graphs graph 56942, used in Boza's verification of
`R(C₄, K₁,₃₀) = 37`, is a six-regular `C₄`-free graph on 36 vertices.
This realizes `C4FreeMinDegreeWitness 36 6`.  The finite degree and
common-neighbor checks are discharged with `native_decide`.
-/

namespace Erdos85

/-- Edge list of House of Graphs graph 56942 (108 edges). -/
def boza36Edges : List (Nat × Nat) := [
  (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 27), (1, 28),
  (1, 31), (1, 32), (1, 34), (2, 26), (2, 29), (2, 30), (2, 33), (2, 35),
  (3, 5), (3, 10), (3, 14), (3, 20), (3, 25), (4, 6), (4, 11), (4, 16),
  (4, 19), (4, 22), (5, 12), (5, 13), (5, 15), (5, 24), (6, 17), (6, 18),
  (6, 21), (6, 23), (7, 19), (7, 20), (7, 23), (7, 24), (7, 30), (7, 31),
  (8, 9), (8, 22), (8, 23), (8, 25), (8, 32), (8, 35), (9, 21), (9, 24),
  (9, 25), (9, 33), (9, 34), (10, 17), (10, 19), (10, 25), (10, 28),
  (10, 29), (11, 15), (11, 16), (11, 25), (11, 27), (11, 30), (12, 13),
  (12, 16), (12, 21), (12, 31), (12, 35), (13, 17), (13, 22), (13, 26),
  (13, 27), (14, 16), (14, 18), (14, 20), (14, 26), (14, 34), (15, 18),
  (15, 24), (15, 29), (15, 32), (16, 34), (16, 35), (17, 23), (17, 29),
  (17, 34), (18, 21), (18, 26), (18, 28), (19, 22), (19, 24), (19, 28),
  (20, 23), (20, 27), (20, 33), (21, 31), (21, 33), (22, 26), (22, 32),
  (23, 35), (24, 34), (25, 30), (26, 30), (27, 28), (27, 33), (28, 35),
  (29, 32), (29, 33), (30, 31), (31, 32)
]

def boza36Adj (i j : Fin 36) : Prop :=
  ((i.val, j.val) ∈ boza36Edges ∨ (j.val, i.val) ∈ boza36Edges)

instance : DecidableRel boza36Adj := fun i j => by
  unfold boza36Adj
  infer_instance

def boza36Graph : SimpleGraph (Fin 36) where
  Adj := boza36Adj
  symm.symm := by
    intro i j h
    unfold boza36Adj at h ⊢
    tauto
  loopless.irrefl := by native_decide

instance : DecidableRel boza36Graph.Adj := fun i j =>
  decidable_of_iff (boza36Adj i j) Iff.rfl

theorem boza36Graph_degree : ∀ v, boza36Graph.degree v = 6 := by
  native_decide

theorem boza36Graph_common_le_one : ∀ x y : Fin 36, x ≠ y →
    (boza36Graph.neighborFinset x ∩ boza36Graph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem boza36Graph_not_containsC4 :
    ¬ containsC4 (Fin 36) boza36Graph :=
  not_containsC4_of_forall_common_le_one boza36Graph_common_le_one

/-- The checked order-36, minimum-degree-six witness. -/
theorem boza36_degreeSix_witness : C4FreeMinDegreeWitness 36 6 := by
  refine ⟨boza36Graph, inferInstance, ?_, boza36Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  rw [boza36Graph_degree v]

end Erdos85
