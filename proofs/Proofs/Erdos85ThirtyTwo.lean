import Proofs.Erdos85GadgetExtension

/-!
# A 32-vertex witness for Erdős Problem 85

An exhaustive search through the exact gadget budgets found the following
construction.  Start with the order-five orthogonal polarity graph, delete
four absolute points, and attach a five-cycle.  Each cycle vertex has three
old neighbours.  The explicit edge list below is the resulting certificate;
the common-neighbour matrix is checked directly.
-/

namespace Erdos85

open SimpleGraph

def polarityCycle32Edges : List (Fin 32 × Fin 32) :=
  [(0,1), (0,4), (0,7), (0,12), (0,17), (0,22),
   (1,4), (1,5), (1,6), (2,3), (2,4), (2,11), (2,15), (2,19), (2,23),
   (3,4), (3,8), (3,14), (3,20), (3,26),
   (5,6), (5,11), (5,16), (5,21), (5,26),
   (6,8), (6,13), (6,18), (6,23),
   (7,22), (7,23), (7,24), (7,25), (7,26),
   (8,10), (8,14), (8,18), (8,22),
   (9,11), (9,13), (9,20), (9,22),
   (10,16), (10,19), (10,22),
   (11,15), (11,21), (11,22),
   (12,13), (12,14), (12,15), (12,16),
   (13,20), (13,23), (14,21), (14,25),
   (15,18), (15,24), (16,19), (16,26),
   (17,18), (17,19), (17,20), (17,21),
   (18,24), (19,23), (20,26), (21,25), (23,25), (24,26),
   -- The attached five-cycle on vertices 27,...,31.
   (27,30), (27,31), (28,29), (28,31), (29,30),
   -- Its five three-element old-neighbour selectors.
   (1,27), (14,27), (9,27),
   (25,28), (4,28), (18,28),
   (20,29), (25,29), (10,29),
   (1,30), (24,30), (10,30),
   (16,31), (9,31), (18,31)]

/-- The delete-four/add-five polarity-cycle witness. -/
def polarityCycle32 : SimpleGraph (Fin 32) where
  Adj i j := (i, j) ∈ polarityCycle32Edges ∨ (j, i) ∈ polarityCycle32Edges
  symm.symm := fun _ _ h => Or.symm h
  loopless.irrefl := by native_decide

instance : DecidableRel polarityCycle32.Adj := fun i j =>
  decidable_of_iff
    ((i, j) ∈ polarityCycle32Edges ∨ (j, i) ∈ polarityCycle32Edges) Iff.rfl

/-- Every vertex has degree at least five (in fact the degree sequence consists
of degrees five, six, and one degree seven). -/
theorem polarityCycle32_five_le_degree :
    ∀ v : Fin 32, 5 ≤ polarityCycle32.degree v := by native_decide

/-- Every distinct pair has at most one common neighbour. -/
theorem polarityCycle32_common_le_one :
    ∀ x y : Fin 32, x ≠ y →
      (polarityCycle32.neighborFinset x ∩
        polarityCycle32.neighborFinset y).card ≤ 1 := by native_decide

theorem polarityCycle32_not_containsC4 :
    ¬ containsC4 (Fin 32) polarityCycle32 :=
  not_containsC4_of_forall_common_le_one polarityCycle32_common_le_one

theorem polarityCycle32_five_le_minDegree :
    5 ≤ polarityCycle32.minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  exact polarityCycle32_five_le_degree

/-- **New lower bound at order 32:** `f(32) ≥ 6`. -/
theorem six_le_minDegreeForC4_thirtytwo :
    6 ≤ minDegreeForC4 32 := by
  have hw : C4FreeMinDegreeWitness 32 5 :=
    ⟨polarityCycle32, inferInstance, polarityCycle32_five_le_minDegree,
      polarityCycle32_not_containsC4⟩
  have hlt := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4
    (n := 32) (d := 5) (by norm_num)).1 hw
  omega

/-- **A new verified monotonicity step:** `f(31) ≤ f(32)`.  The universal
tight-point bound gives `f(31) ≤ 6`, while the explicit witness gives
`6 ≤ f(32)`. -/
theorem minDegreeForC4_thirtyone_le_thirtytwo :
    minDegreeForC4 31 ≤ minDegreeForC4 32 :=
  le_trans minDegreeForC4_thirtyone_le six_le_minDegreeForC4_thirtytwo

end Erdos85
