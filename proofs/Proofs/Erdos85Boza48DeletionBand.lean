import Proofs.Erdos85Boza48Witness
import Proofs.Erdos85Relabel

/-!
# A degree-six deletion band from the Boza order-48 witness

The order-48 graph is seven-regular.  The eight checked deletion sets below
meet every retained neighborhood in at most one vertex, so deleting them
leaves minimum degree at least six.  This supplies degree-six witnesses at
every order from 40 through 47.
-/

namespace Erdos85

def boza48DeleteGraph (S : Finset (Fin 48)) : SimpleGraph {v : Fin 48 // v ∉ S} :=
  boza48Graph.induce {v | v ∉ S}

instance (S : Finset (Fin 48)) : DecidableRel (boza48DeleteGraph S).Adj :=
  fun x y => (inferInstance : Decidable (boza48Graph.Adj x.1 y.1))

theorem boza48DeleteGraph_not_containsC4 (S : Finset (Fin 48)) :
    ¬ containsC4 {v : Fin 48 // v ∉ S} (boza48DeleteGraph S) := by
  rintro ⟨f, hf, hadj⟩
  apply boza48Graph_not_containsC4
  exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
    fun i j hij => hadj i j hij⟩

def boza48Delete1 : Finset (Fin 48) := {47}
def boza48Delete2 : Finset (Fin 48) := {46, 47}
def boza48Delete3 : Finset (Fin 48) := {23, 46, 47}
def boza48Delete4 : Finset (Fin 48) := {9, 27, 46, 47}
def boza48Delete5 : Finset (Fin 48) := {0, 11, 18, 29, 47}
def boza48Delete6 : Finset (Fin 48) := {17, 18, 29, 36, 46, 47}
def boza48Delete7 : Finset (Fin 48) := {0, 11, 18, 26, 29, 32, 47}
def boza48Delete8 : Finset (Fin 48) := {1, 4, 9, 27, 40, 43, 46, 47}

theorem boza48_delete1_degreeSix_witness : C4FreeMinDegreeWitness 47 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (boza48DeleteGraph boza48Delete1)
  · native_decide
  · native_decide
  · exact boza48DeleteGraph_not_containsC4 boza48Delete1

theorem boza48_delete2_degreeSix_witness : C4FreeMinDegreeWitness 46 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (boza48DeleteGraph boza48Delete2)
  · native_decide
  · native_decide
  · exact boza48DeleteGraph_not_containsC4 boza48Delete2

theorem boza48_delete3_degreeSix_witness : C4FreeMinDegreeWitness 45 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (boza48DeleteGraph boza48Delete3)
  · native_decide
  · native_decide
  · exact boza48DeleteGraph_not_containsC4 boza48Delete3

theorem boza48_delete4_degreeSix_witness : C4FreeMinDegreeWitness 44 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (boza48DeleteGraph boza48Delete4)
  · native_decide
  · native_decide
  · exact boza48DeleteGraph_not_containsC4 boza48Delete4

theorem boza48_delete5_degreeSix_witness : C4FreeMinDegreeWitness 43 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (boza48DeleteGraph boza48Delete5)
  · native_decide
  · native_decide
  · exact boza48DeleteGraph_not_containsC4 boza48Delete5

theorem boza48_delete6_degreeSix_witness : C4FreeMinDegreeWitness 42 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (boza48DeleteGraph boza48Delete6)
  · native_decide
  · native_decide
  · exact boza48DeleteGraph_not_containsC4 boza48Delete6

theorem boza48_delete7_degreeSix_witness : C4FreeMinDegreeWitness 41 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (boza48DeleteGraph boza48Delete7)
  · native_decide
  · native_decide
  · exact boza48DeleteGraph_not_containsC4 boza48Delete7

theorem boza48_delete8_degreeSix_witness : C4FreeMinDegreeWitness 40 6 := by
  apply c4FreeMinDegreeWitness_of_card_eq (boza48DeleteGraph boza48Delete8)
  · native_decide
  · native_decide
  · exact boza48DeleteGraph_not_containsC4 boza48Delete8

end Erdos85
