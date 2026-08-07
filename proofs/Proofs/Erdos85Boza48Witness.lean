import Proofs.Erdos85Problem

/-!
# The Boza witness: a C4-free graph on 48 vertices with minimum degree 7

Cayley graph of the group `Z24 x| Z2` (semidirect product with the order-2
action a -> 19*a) with symmetric connection set
S = {(0,1), (1,1), (5,1), (3,0), (21,0), (14,1), (22,1)}; every non-identity
group element has at most one representation t * s^-1 with s, t in S, hence
the graph is C4-free; |S| = 7 gives 7-regularity.  Vertices are numbered
2*a + b for (a, b) in Z24 x Z2.  This realizes `C4FreeMinDegreeWitness 48 7`
(the existence half of the finite drop at 49, cf. Boza's f(41) = 49).
The finite checks are discharged with `native_decide` (Lean.ofReduceBool
disclosed).
-/

namespace Erdos85

/-- Edge list of the 48-vertex witness (168 edges, lexicographic). -/
def boza48Edges : List (Nat × Nat) := [
  (0, 1), (0, 3), (0, 6), (0, 11), (0, 29), (0, 42), (0, 45), (1, 4),
  (1, 19), (1, 20), (1, 31), (1, 38), (1, 46), (2, 3), (2, 5), (2, 8),
  (2, 13), (2, 31), (2, 44), (2, 47), (3, 6), (3, 21), (3, 22), (3, 33),
  (3, 40), (4, 5), (4, 7), (4, 10), (4, 15), (4, 33), (4, 46), (5, 8),
  (5, 23), (5, 24), (5, 35), (5, 42), (6, 7), (6, 9), (6, 12), (6, 17),
  (6, 35), (7, 10), (7, 25), (7, 26), (7, 37), (7, 44), (8, 9), (8, 11),
  (8, 14), (8, 19), (8, 37), (9, 12), (9, 27), (9, 28), (9, 39), (9, 46),
  (10, 11), (10, 13), (10, 16), (10, 21), (10, 39), (11, 14), (11, 29), (11, 30),
  (11, 41), (12, 13), (12, 15), (12, 18), (12, 23), (12, 41), (13, 16), (13, 31),
  (13, 32), (13, 43), (14, 15), (14, 17), (14, 20), (14, 25), (14, 43), (15, 18),
  (15, 33), (15, 34), (15, 45), (16, 17), (16, 19), (16, 22), (16, 27), (16, 45),
  (17, 20), (17, 35), (17, 36), (17, 47), (18, 19), (18, 21), (18, 24), (18, 29),
  (18, 47), (19, 22), (19, 37), (19, 38), (20, 21), (20, 23), (20, 26), (20, 31),
  (21, 24), (21, 39), (21, 40), (22, 23), (22, 25), (22, 28), (22, 33), (23, 26),
  (23, 41), (23, 42), (24, 25), (24, 27), (24, 30), (24, 35), (25, 28), (25, 43),
  (25, 44), (26, 27), (26, 29), (26, 32), (26, 37), (27, 30), (27, 45), (27, 46),
  (28, 29), (28, 31), (28, 34), (28, 39), (29, 32), (29, 47), (30, 31), (30, 33),
  (30, 36), (30, 41), (31, 34), (32, 33), (32, 35), (32, 38), (32, 43), (33, 36),
  (34, 35), (34, 37), (34, 40), (34, 45), (35, 38), (36, 37), (36, 39), (36, 42),
  (36, 47), (37, 40), (38, 39), (38, 41), (38, 44), (39, 42), (40, 41), (40, 43),
  (40, 46), (41, 44), (42, 43), (42, 45), (43, 46), (44, 45), (44, 47), (46, 47)
]

/-- Adjacency as a decidable symmetric relation on `Fin 48`. -/
def boza48Adj (i j : Fin 48) : Prop :=
  ((i.val, j.val) ∈ boza48Edges ∨ (j.val, i.val) ∈ boza48Edges)

instance : DecidableRel boza48Adj := fun i j => by
  unfold boza48Adj; infer_instance

def boza48Graph : SimpleGraph (Fin 48) where
  Adj := boza48Adj
  symm.symm := by
    intro i j h
    unfold boza48Adj at h ⊢
    tauto
  loopless.irrefl := by native_decide

instance : DecidableRel boza48Graph.Adj := fun i j =>
  decidable_of_iff (boza48Adj i j) Iff.rfl

/-- The nonabelian Cayley witness is 7-regular. -/
theorem boza48Graph_degree : ∀ v, boza48Graph.degree v = 7 := by
  native_decide

/-- Every two distinct vertices have at most one common neighbor. -/
theorem boza48Graph_common_le_one : ∀ x y : Fin 48, x ≠ y →
    (boza48Graph.neighborFinset x ∩ boza48Graph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem boza48Graph_not_containsC4 :
    ¬ containsC4 (Fin 48) boza48Graph :=
  not_containsC4_of_forall_common_le_one boza48Graph_common_le_one

/-- The fully checked order-48, minimum-degree-7 witness. -/
theorem boza48_degreeSeven_witness : C4FreeMinDegreeWitness 48 7 := by
  refine ⟨boza48Graph, inferInstance, ?_, boza48Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  rw [boza48Graph_degree v]

end Erdos85
