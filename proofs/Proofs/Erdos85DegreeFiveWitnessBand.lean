import Proofs.Erdos85ER7DeletionBand

/-!
# The finite degree-five witness band

The `ER(5)` polarity graph and three deletions supply orders 26, 28, 30,
and 31.  Four checked induced subgraphs of the already certified `ER(7)`
graph supply orders 29 and 32--34.  Together with the separate order-27
certificate, these fill every order from 26 through 34.
-/

namespace Erdos85

def er5X (i : Fin 31) : Nat := if i.val < 25 then 1 else 0
def er5Y (i : Fin 31) : Nat :=
  if i.val < 25 then i.val / 5 else if i.val < 30 then 1 else 0
def er5Z (i : Fin 31) : Nat :=
  if i.val < 25 then i.val % 5 else if i.val < 30 then i.val - 25 else 1
def er5Dot (i j : Fin 31) : Nat :=
  (er5X i * er5X j + er5Y i * er5Y j + er5Z i * er5Z j) % 5
def er5Adj (i j : Fin 31) : Prop := i ≠ j ∧ er5Dot i j = 0

instance : DecidableRel er5Adj := fun i j => by unfold er5Adj; infer_instance

def er5Graph : SimpleGraph (Fin 31) where
  Adj := er5Adj
  symm.symm := by native_decide
  loopless.irrefl := by native_decide

instance : DecidableRel er5Graph.Adj := fun i j =>
  decidable_of_iff (er5Adj i j) Iff.rfl

theorem er5Graph_degree_ge_five : ∀ v, 5 ≤ er5Graph.degree v := by native_decide
theorem er5Graph_common_le_one : ∀ x y : Fin 31, x ≠ y →
    (er5Graph.neighborFinset x ∩ er5Graph.neighborFinset y).card ≤ 1 := by
  native_decide
theorem er5Graph_not_containsC4 : ¬ containsC4 (Fin 31) er5Graph :=
  not_containsC4_of_forall_common_le_one er5Graph_common_le_one

theorem er5_degreeFive_witness : C4FreeMinDegreeWitness 31 5 := by
  refine ⟨er5Graph, inferInstance, ?_, er5Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  exact er5Graph_degree_ge_five

def er5DeleteGraph (S : Finset (Fin 31)) : SimpleGraph {v : Fin 31 // v ∉ S} :=
  er5Graph.induce {v | v ∉ S}

instance (S : Finset (Fin 31)) : DecidableRel (er5DeleteGraph S).Adj :=
  fun x y => (inferInstance : Decidable (er5Graph.Adj x.1 y.1))

theorem er5DeleteGraph_not_containsC4 (S : Finset (Fin 31)) :
    ¬ containsC4 {v : Fin 31 // v ∉ S} (er5DeleteGraph S) := by
  rintro ⟨f, hf, hadj⟩
  apply er5Graph_not_containsC4
  exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
    fun i j hij => hadj i j hij⟩

def er5Delete1 : Finset (Fin 31) := {24}
def er5Delete3 : Finset (Fin 31) := {10,15,30}
def er5Delete5 : Finset (Fin 31) := {5,10,15,20,30}

theorem er5_delete1_degreeFive_witness : C4FreeMinDegreeWitness 30 5 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er5DeleteGraph er5Delete1)
  · native_decide
  · native_decide
  · exact er5DeleteGraph_not_containsC4 er5Delete1

theorem er5_delete3_degreeFive_witness : C4FreeMinDegreeWitness 28 5 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er5DeleteGraph er5Delete3)
  · native_decide
  · native_decide
  · exact er5DeleteGraph_not_containsC4 er5Delete3

theorem er5_delete5_degreeFive_witness : C4FreeMinDegreeWitness 26 5 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er5DeleteGraph er5Delete5)
  · native_decide
  · native_decide
  · exact er5DeleteGraph_not_containsC4 er5Delete5

def er7DegreeFiveDelete29 : Finset (Fin 57) :=
  {0,5,9,12,14,16,17,18,21,22,23,25,26,27,28,29,31,32,34,35,36,38,39,46,51,52,53,56}
def er7DegreeFiveDelete32 : Finset (Fin 57) :=
  {0,1,2,10,11,13,17,19,20,25,27,28,30,36,37,38,40,41,45,46,47,50,51,52,54}
def er7DegreeFiveDelete33 : Finset (Fin 57) :=
  {0,1,7,10,11,14,15,18,20,21,23,27,33,37,38,42,43,44,46,47,48,51,52,56}
def er7DegreeFiveDelete34 : Finset (Fin 57) :=
  {7,12,17,23,28,32,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,53,56}

theorem er7_deleteTo29_degreeFive_witness : C4FreeMinDegreeWitness 29 5 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7DegreeFiveDelete29)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7DegreeFiveDelete29

theorem er7_deleteTo32_degreeFive_witness : C4FreeMinDegreeWitness 32 5 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7DegreeFiveDelete32)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7DegreeFiveDelete32

theorem er7_deleteTo33_degreeFive_witness : C4FreeMinDegreeWitness 33 5 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7DegreeFiveDelete33)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7DegreeFiveDelete33

theorem er7_deleteTo34_degreeFive_witness : C4FreeMinDegreeWitness 34 5 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7DegreeFiveDelete34)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7DegreeFiveDelete34

end Erdos85
