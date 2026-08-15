import Proofs.Erdos85Problem

/-!
# The Boza order-37 through order-39 witnesses

House of Graphs graphs 56943, 56944, and 56945 are the six-regular
`C₄`-free graphs used in Boza's small Ramsey-number computations.  Their
finite degree and common-neighbor checks are discharged with `native_decide`.
-/

namespace Erdos85

def boza37Edges : List (Nat × Nat) := [
  (0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,28),(1,33),(1,34),(1,35),(1,36),
  (2,27),(2,29),(2,30),(2,31),(2,32),(3,4),(3,13),(3,17),(3,22),(3,23),
  (4,14),(4,15),(4,20),(4,25),(5,6),(5,12),(5,18),(5,19),(5,26),(6,11),
  (6,16),(6,21),(6,24),(7,11),(7,15),(7,19),(7,23),(7,29),(7,33),(8,13),
  (8,18),(8,20),(8,24),(8,32),(8,34),(9,12),(9,17),(9,21),(9,25),(9,30),
  (9,36),(10,14),(10,16),(10,22),(10,26),(10,31),(10,35),(11,13),(11,15),
  (11,21),(11,31),(12,14),(12,17),(12,19),(12,32),(13,18),(13,22),(13,30),
  (14,16),(14,20),(14,29),(15,25),(15,32),(15,35),(16,24),(16,30),(16,33),
  (17,23),(17,31),(17,34),(18,26),(18,29),(18,36),(19,22),(19,27),(19,33),
  (20,21),(20,27),(20,34),(21,27),(21,36),(22,27),(22,35),(23,24),(23,28),
  (23,29),(24,28),(24,32),(25,26),(25,28),(25,30),(26,28),(26,31),(27,28),
  (29,36),(30,33),(31,34),(32,35),(33,34),(35,36)]

def boza37Adj (i j : Fin 37) : Prop :=
  (i.val, j.val) ∈ boza37Edges ∨ (j.val, i.val) ∈ boza37Edges

instance : DecidableRel boza37Adj := fun i j => by unfold boza37Adj; infer_instance

def boza37Graph : SimpleGraph (Fin 37) where
  Adj := boza37Adj
  symm.symm := by intro i j h; unfold boza37Adj at h ⊢; tauto
  loopless.irrefl := by native_decide

instance : DecidableRel boza37Graph.Adj := fun i j =>
  decidable_of_iff (boza37Adj i j) Iff.rfl

theorem boza37Graph_degree : ∀ v, boza37Graph.degree v = 6 := by native_decide

theorem boza37Graph_common_le_one : ∀ x y : Fin 37, x ≠ y →
    (boza37Graph.neighborFinset x ∩ boza37Graph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem boza37Graph_not_containsC4 : ¬ containsC4 (Fin 37) boza37Graph :=
  not_containsC4_of_forall_common_le_one boza37Graph_common_le_one

theorem boza37_degreeSix_witness : C4FreeMinDegreeWitness 37 6 := by
  refine ⟨boza37Graph, inferInstance, ?_, boza37Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  rw [boza37Graph_degree v]

def boza38Edges : List (Nat × Nat) := [
  (0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,14),(1,17),(1,33),(1,37),
  (2,3),(2,16),(2,19),(2,29),(2,36),(3,18),(3,23),(3,28),(3,35),(4,5),
  (4,15),(4,22),(4,32),(4,34),(5,21),(5,26),(5,27),(5,31),(6,20),(6,24),
  (6,25),(6,30),(7,14),(7,21),(7,24),(7,28),(7,32),(7,36),(8,15),(8,17),
  (8,18),(8,27),(8,29),(8,30),(9,13),(9,23),(9,30),(9,31),(9,32),(9,37),
  (10,11),(10,25),(10,27),(10,35),(10,36),(10,37),(11,16),(11,22),(11,31),
  (11,33),(11,35),(12,13),(12,26),(12,28),(12,29),(12,33),(12,34),(13,19),
  (13,20),(13,34),(13,37),(14,15),(14,16),(14,28),(14,37),(15,16),(15,23),
  (15,34),(16,19),(16,31),(17,19),(17,26),(17,32),(17,35),(18,20),(18,22),
  (18,27),(18,28),(19,20),(19,21),(20,22),(20,25),(21,23),(21,24),(21,27),
  (22,32),(22,33),(23,25),(23,33),(24,30),(24,34),(24,35),(25,26),(25,36),
  (26,28),(26,31),(27,37),(29,30),(29,33),(29,36),(30,31),(32,36),(34,35)]

def boza38Adj (i j : Fin 38) : Prop :=
  (i.val, j.val) ∈ boza38Edges ∨ (j.val, i.val) ∈ boza38Edges

instance : DecidableRel boza38Adj := fun i j => by unfold boza38Adj; infer_instance

def boza38Graph : SimpleGraph (Fin 38) where
  Adj := boza38Adj
  symm.symm := by intro i j h; unfold boza38Adj at h ⊢; tauto
  loopless.irrefl := by native_decide

instance : DecidableRel boza38Graph.Adj := fun i j =>
  decidable_of_iff (boza38Adj i j) Iff.rfl

theorem boza38Graph_degree : ∀ v, boza38Graph.degree v = 6 := by native_decide

theorem boza38Graph_common_le_one : ∀ x y : Fin 38, x ≠ y →
    (boza38Graph.neighborFinset x ∩ boza38Graph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem boza38Graph_not_containsC4 : ¬ containsC4 (Fin 38) boza38Graph :=
  not_containsC4_of_forall_common_le_one boza38Graph_common_le_one

theorem boza38_degreeSix_witness : C4FreeMinDegreeWitness 38 6 := by
  refine ⟨boza38Graph, inferInstance, ?_, boza38Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  rw [boza38Graph_degree v]

def boza39Edges : List (Nat × Nat) := [
  (0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,30),(1,31),(1,33),(1,35),(1,38),
  (2,29),(2,32),(2,34),(2,36),(2,37),(3,4),(3,15),(3,16),(3,17),(3,25),
  (4,18),(4,19),(4,20),(4,26),(5,6),(5,13),(5,21),(5,22),(5,27),(6,14),
  (6,23),(6,24),(6,28),(7,15),(7,21),(7,26),(7,28),(7,33),(7,37),(8,10),
  (8,17),(8,18),(8,23),(8,27),(8,38),(9,12),(9,16),(9,22),(9,26),(9,32),
  (9,38),(10,20),(10,24),(10,25),(10,37),(10,38),(11,12),(11,25),(11,27),
  (11,28),(11,34),(11,35),(12,19),(12,28),(12,36),(12,38),(13,15),(13,20),
  (13,22),(13,35),(13,36),(14,15),(14,19),(14,23),(14,30),(14,32),(15,29),
  (15,38),(16,17),(16,21),(16,24),(16,30),(17,23),(17,33),(17,36),(18,19),
  (18,27),(18,29),(18,31),(19,30),(19,36),(20,24),(20,32),(20,35),(21,27),
  (21,30),(21,37),(22,25),(22,26),(22,31),(23,26),(23,34),(24,28),(24,29),
  (25,31),(25,37),(26,34),(27,32),(28,33),(29,31),(29,34),(30,35),(31,33),
  (32,33),(34,35),(36,37)]

def boza39Adj (i j : Fin 39) : Prop :=
  (i.val, j.val) ∈ boza39Edges ∨ (j.val, i.val) ∈ boza39Edges

instance : DecidableRel boza39Adj := fun i j => by unfold boza39Adj; infer_instance

def boza39Graph : SimpleGraph (Fin 39) where
  Adj := boza39Adj
  symm.symm := by intro i j h; unfold boza39Adj at h ⊢; tauto
  loopless.irrefl := by native_decide

instance : DecidableRel boza39Graph.Adj := fun i j =>
  decidable_of_iff (boza39Adj i j) Iff.rfl

theorem boza39Graph_degree : ∀ v, boza39Graph.degree v = 6 := by native_decide

theorem boza39Graph_common_le_one : ∀ x y : Fin 39, x ≠ y →
    (boza39Graph.neighborFinset x ∩ boza39Graph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem boza39Graph_not_containsC4 : ¬ containsC4 (Fin 39) boza39Graph :=
  not_containsC4_of_forall_common_le_one boza39Graph_common_le_one

theorem boza39_degreeSix_witness : C4FreeMinDegreeWitness 39 6 := by
  refine ⟨boza39Graph, inferInstance, ?_, boza39Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  rw [boza39Graph_degree v]

end Erdos85
