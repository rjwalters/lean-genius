import Proofs.Erdos85Relabel

/-!
# The order-57 polarity graph and a degree-six deletion band

Vertices are normalized projective points over `Z/7Z`: indices `0..48`
represent `(1,x,y)`, indices `49..55` represent `(0,1,y)`, and index `56`
represents `(0,0,1)`.  Orthogonality gives the Erdős--Rényi polarity graph
`ER(7)`.  Checked deletion sets retain minimum degree six at every order from
50 through 56.
-/

namespace Erdos85

def er7X (i : Fin 57) : Nat := if i.val < 49 then 1 else 0
def er7Y (i : Fin 57) : Nat :=
  if i.val < 49 then i.val / 7 else if i.val < 56 then 1 else 0
def er7Z (i : Fin 57) : Nat :=
  if i.val < 49 then i.val % 7 else if i.val < 56 then i.val - 49 else 1

def er7Dot (i j : Fin 57) : Nat :=
  (er7X i * er7X j + er7Y i * er7Y j + er7Z i * er7Z j) % 7

def er7Adj (i j : Fin 57) : Prop := i ≠ j ∧ er7Dot i j = 0

instance : DecidableRel er7Adj := fun i j => by unfold er7Adj; infer_instance

def er7Graph : SimpleGraph (Fin 57) where
  Adj := er7Adj
  symm.symm := by native_decide
  loopless.irrefl := by native_decide

instance : DecidableRel er7Graph.Adj := fun i j =>
  decidable_of_iff (er7Adj i j) Iff.rfl

theorem er7Graph_degree_ge_seven : ∀ v, 7 ≤ er7Graph.degree v := by
  native_decide

theorem er7Graph_common_le_one : ∀ x y : Fin 57, x ≠ y →
    (er7Graph.neighborFinset x ∩ er7Graph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem er7Graph_not_containsC4 : ¬ containsC4 (Fin 57) er7Graph :=
  not_containsC4_of_forall_common_le_one er7Graph_common_le_one

theorem er7_degreeSix_witness : C4FreeMinDegreeWitness 57 6 := by
  refine ⟨er7Graph, inferInstance, ?_, er7Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  exact (by have := er7Graph_degree_ge_seven v; omega)

def er7DeleteGraph (S : Finset (Fin 57)) : SimpleGraph {v : Fin 57 // v ∉ S} :=
  er7Graph.induce {v | v ∉ S}

instance (S : Finset (Fin 57)) : DecidableRel (er7DeleteGraph S).Adj :=
  fun x y => (inferInstance : Decidable (er7Graph.Adj x.1 y.1))

theorem er7DeleteGraph_not_containsC4 (S : Finset (Fin 57)) :
    ¬ containsC4 {v : Fin 57 // v ∉ S} (er7DeleteGraph S) := by
  rintro ⟨f, hf, hadj⟩
  apply er7Graph_not_containsC4
  exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
    fun i j hij => hadj i j hij⟩

def er7Delete1 : Finset (Fin 57) := {48}
def er7Delete2 : Finset (Fin 57) := {47, 48}
def er7Delete3 : Finset (Fin 57) := {7, 47, 48}
def er7Delete4 : Finset (Fin 57) := {0, 54, 55, 56}
def er7Delete5 : Finset (Fin 57) := {0, 53, 54, 55, 56}
def er7Delete6 : Finset (Fin 57) := {0, 52, 53, 54, 55, 56}
def er7Delete7 : Finset (Fin 57) := {0, 51, 52, 53, 54, 55, 56}

theorem er7_delete1_degreeSix_witness : C4FreeMinDegreeWitness 56 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7Delete1)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7Delete1

theorem er7_delete2_degreeSix_witness : C4FreeMinDegreeWitness 55 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7Delete2)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7Delete2

theorem er7_delete3_degreeSix_witness : C4FreeMinDegreeWitness 54 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7Delete3)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7Delete3

theorem er7_delete4_degreeSix_witness : C4FreeMinDegreeWitness 53 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7Delete4)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7Delete4

theorem er7_delete5_degreeSix_witness : C4FreeMinDegreeWitness 52 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7Delete5)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7Delete5

theorem er7_delete6_degreeSix_witness : C4FreeMinDegreeWitness 51 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7Delete6)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7Delete6

theorem er7_delete7_degreeSix_witness : C4FreeMinDegreeWitness 50 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er7DeleteGraph er7Delete7)
  · native_decide
  · native_decide
  · exact er7DeleteGraph_not_containsC4 er7Delete7

end Erdos85
