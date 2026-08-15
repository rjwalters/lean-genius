import Proofs.Erdos85Relabel

/-!
# The order-73 `ER(8)` polarity graph and its degree-six deletion band

`GF(8)` is represented in the polynomial basis modulo `X³+X+1`; addition is
bitwise xor and multiplication uses the displayed eight-by-eight table.
Normalized projective coordinates give 73 vertices.  Checked deletions of
sizes 4 through 15 yield degree-six witnesses at every order from 58 to 69.
-/

namespace Erdos85

def gf8MulTable : List Nat := [
  0,0,0,0,0,0,0,0, 0,1,2,3,4,5,6,7,
  0,2,4,6,3,1,7,5, 0,3,6,5,7,4,1,2,
  0,4,3,7,6,2,5,1, 0,5,1,4,2,7,3,6,
  0,6,7,1,5,3,2,4, 0,7,5,2,1,6,4,3]

def gf8Mul (a b : Nat) : Nat := gf8MulTable.getD (8 * a + b) 0

def er8X (i : Fin 73) : Nat := if i.val < 64 then 1 else 0
def er8Y (i : Fin 73) : Nat :=
  if i.val < 64 then i.val / 8 else if i.val < 72 then 1 else 0
def er8Z (i : Fin 73) : Nat :=
  if i.val < 64 then i.val % 8 else if i.val < 72 then i.val - 64 else 1

def er8Dot (i j : Fin 73) : Nat :=
  Nat.xor (gf8Mul (er8X i) (er8X j))
    (Nat.xor (gf8Mul (er8Y i) (er8Y j)) (gf8Mul (er8Z i) (er8Z j)))

def er8Adj (i j : Fin 73) : Prop := i ≠ j ∧ er8Dot i j = 0

instance : DecidableRel er8Adj := fun i j => by unfold er8Adj; infer_instance

def er8Graph : SimpleGraph (Fin 73) where
  Adj := er8Adj
  symm.symm := by native_decide
  loopless.irrefl := by native_decide

instance : DecidableRel er8Graph.Adj := fun i j =>
  decidable_of_iff (er8Adj i j) Iff.rfl

theorem er8Graph_degree_ge_eight : ∀ v, 8 ≤ er8Graph.degree v := by
  native_decide

theorem er8Graph_common_le_one : ∀ x y : Fin 73, x ≠ y →
    (er8Graph.neighborFinset x ∩ er8Graph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem er8Graph_not_containsC4 : ¬ containsC4 (Fin 73) er8Graph :=
  not_containsC4_of_forall_common_le_one er8Graph_common_le_one

def er8DeleteGraph (S : Finset (Fin 73)) : SimpleGraph {v : Fin 73 // v ∉ S} :=
  er8Graph.induce {v | v ∉ S}

instance (S : Finset (Fin 73)) : DecidableRel (er8DeleteGraph S).Adj :=
  fun x y => (inferInstance : Decidable (er8Graph.Adj x.1 y.1))

theorem er8DeleteGraph_not_containsC4 (S : Finset (Fin 73)) :
    ¬ containsC4 {v : Fin 73 // v ∉ S} (er8DeleteGraph S) := by
  rintro ⟨f, hf, hadj⟩
  apply er8Graph_not_containsC4
  exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
    fun i j hij => hadj i j hij⟩

def er8Delete4 : Finset (Fin 73) := {61,62,63,65}
def er8Delete5 : Finset (Fin 73) := {0,69,70,71,72}
def er8Delete6 : Finset (Fin 73) := {0,68,69,70,71,72}
def er8Delete7 : Finset (Fin 73) := {0,67,68,69,70,71,72}
def er8Delete8 : Finset (Fin 73) := {0,66,67,68,69,70,71,72}
def er8Delete9 : Finset (Fin 73) := {0,65,66,67,68,69,70,71,72}
def er8Delete10 : Finset (Fin 73) := {0,64,65,66,67,68,69,70,71,72}
def er8Delete11 : Finset (Fin 73) := {0,63,64,65,66,67,68,69,70,71,72}
def er8Delete12 : Finset (Fin 73) := {0,62,63,64,65,66,67,68,69,70,71,72}
def er8Delete13 : Finset (Fin 73) := {0,47,62,63,64,65,66,67,68,69,70,71,72}
def er8Delete14 : Finset (Fin 73) := {0,32,60,61,62,63,64,66,67,68,69,70,71,72}
def er8Delete15 : Finset (Fin 73) := {32,37,46,47,49,50,51,56,57,58,59,60,61,62,63}

theorem er8_delete4_degreeSix_witness : C4FreeMinDegreeWitness 69 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete4)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete4

theorem er8_delete5_degreeSix_witness : C4FreeMinDegreeWitness 68 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete5)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete5

theorem er8_delete6_degreeSix_witness : C4FreeMinDegreeWitness 67 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete6)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete6

theorem er8_delete7_degreeSix_witness : C4FreeMinDegreeWitness 66 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete7)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete7

theorem er8_delete8_degreeSix_witness : C4FreeMinDegreeWitness 65 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete8)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete8

theorem er8_delete9_degreeSix_witness : C4FreeMinDegreeWitness 64 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete9)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete9

theorem er8_delete10_degreeSix_witness : C4FreeMinDegreeWitness 63 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete10)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete10

theorem er8_delete11_degreeSix_witness : C4FreeMinDegreeWitness 62 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete11)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete11

theorem er8_delete12_degreeSix_witness : C4FreeMinDegreeWitness 61 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete12)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete12

theorem er8_delete13_degreeSix_witness : C4FreeMinDegreeWitness 60 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete13)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete13

theorem er8_delete14_degreeSix_witness : C4FreeMinDegreeWitness 59 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete14)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete14

theorem er8_delete15_degreeSix_witness : C4FreeMinDegreeWitness 58 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph er8Delete15)
  · native_decide
  · native_decide
  · exact er8DeleteGraph_not_containsC4 er8Delete15

end Erdos85
