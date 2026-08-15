import Proofs.Erdos85Relabel

/-!
# A degree-seven deletion band from ER(9)

We realize `𝔽₉ = 𝔽₃[t]/(t²+1)` explicitly, normalize projective points in
the usual three affine charts, and use orthogonality.  The ten listed points
are the absolute conic.  Deleting any initial segment leaves minimum degree
at least seven, giving witnesses at every order from 81 through 91.
-/

namespace Erdos85

/-- Addition in `𝔽₉`, with `3a+b` encoding `a+b t`. -/
def er9Add (x y : Nat) : Nat :=
  ((x / 3 + y / 3) % 3) * 3 + (x % 3 + y % 3) % 3

/-- Multiplication in `𝔽₉`, using `t² = -1 = 2`. -/
def er9Mul (x y : Nat) : Nat :=
  ((x / 3 * (y / 3) + 2 * (x % 3) * (y % 3)) % 3) * 3 +
    ((x / 3 * (y % 3) + (x % 3) * (y / 3)) % 3)

def er9X (i : Fin 91) : Nat := if i.val < 81 then 3 else 0
def er9Y (i : Fin 91) : Nat :=
  if i.val < 81 then i.val / 9 else if i.val < 90 then 3 else 0
def er9Z (i : Fin 91) : Nat :=
  if i.val < 81 then i.val % 9 else if i.val < 90 then i.val - 81 else 3

def er9Dot (i j : Fin 91) : Nat :=
  er9Add (er9Add (er9Mul (er9X i) (er9X j))
    (er9Mul (er9Y i) (er9Y j))) (er9Mul (er9Z i) (er9Z j))

def er9Adj (i j : Fin 91) : Prop := i ≠ j ∧ er9Dot i j = 0

instance : DecidableRel er9Adj := fun i j => by unfold er9Adj; infer_instance

def er9Graph : SimpleGraph (Fin 91) where
  Adj := er9Adj
  symm.symm := by native_decide
  loopless.irrefl := by native_decide

instance : DecidableRel er9Graph.Adj := fun i j =>
  decidable_of_iff (er9Adj i j) Iff.rfl

theorem er9Graph_degree_ge_nine : ∀ v, 9 ≤ er9Graph.degree v := by
  native_decide

theorem er9Graph_common_le_one : ∀ x y : Fin 91, x ≠ y →
    (er9Graph.neighborFinset x ∩ er9Graph.neighborFinset y).card ≤ 1 := by
  native_decide

theorem er9Graph_not_containsC4 : ¬ containsC4 (Fin 91) er9Graph :=
  not_containsC4_of_forall_common_le_one er9Graph_common_le_one

def er9DeleteGraph (S : Finset (Fin 91)) : SimpleGraph {v : Fin 91 // v ∉ S} :=
  er9Graph.induce {v | v ∉ S}

instance (S : Finset (Fin 91)) : DecidableRel (er9DeleteGraph S).Adj :=
  fun x y => (inferInstance : Decidable (er9Graph.Adj x.1 y.1))

theorem er9DeleteGraph_not_containsC4 (S : Finset (Fin 91)) :
    ¬ containsC4 {v : Fin 91 // v ∉ S} (er9DeleteGraph S) := by
  rintro ⟨f, hf, hadj⟩
  apply er9Graph_not_containsC4
  exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
    fun i j hij => hadj i j hij⟩

def er9Delete1 : Finset (Fin 91) := {1}
def er9Delete2 : Finset (Fin 91) := {1, 2}
def er9Delete3 : Finset (Fin 91) := {1, 2, 9}
def er9Delete4 : Finset (Fin 91) := {1, 2, 9, 18}
def er9Delete5 : Finset (Fin 91) := {1, 2, 9, 18, 30}
def er9Delete6 : Finset (Fin 91) := {1, 2, 9, 18, 30, 33}
def er9Delete7 : Finset (Fin 91) := {1, 2, 9, 18, 30, 33, 57}
def er9Delete8 : Finset (Fin 91) := {1, 2, 9, 18, 30, 33, 57, 60}
def er9Delete9 : Finset (Fin 91) := {1, 2, 9, 18, 30, 33, 57, 60, 82}
def er9Delete10 : Finset (Fin 91) := {1, 2, 9, 18, 30, 33, 57, 60, 82, 83}

private theorem er9_delete_degreeSeven_witness
    (S : Finset (Fin 91)) {n : Nat}
    (hcard : Fintype.card {v : Fin 91 // v ∉ S} = n)
    (hpos : 0 < n)
    (hdegree : ∀ v, 7 ≤ (er9DeleteGraph S).degree v) :
    C4FreeMinDegreeWitness n 7 := by
  letI : Nonempty {v : Fin 91 // v ∉ S} :=
    Fintype.card_pos_iff.mp (by simpa [hcard] using hpos)
  apply c4FreeMinDegreeWitness_of_card_eq (er9DeleteGraph S)
  · exact hcard
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    exact hdegree v
  · exact er9DeleteGraph_not_containsC4 S

theorem er9_degreeSeven_witness : C4FreeMinDegreeWitness 91 7 := by
  refine ⟨er9Graph, inferInstance, ?_, er9Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  exact (er9Graph_degree_ge_nine v).trans' (by norm_num)

theorem er9_delete1_degreeSeven_witness : C4FreeMinDegreeWitness 90 7 := by
  apply er9_delete_degreeSeven_witness er9Delete1 <;> native_decide
theorem er9_delete2_degreeSeven_witness : C4FreeMinDegreeWitness 89 7 := by
  apply er9_delete_degreeSeven_witness er9Delete2 <;> native_decide
theorem er9_delete3_degreeSeven_witness : C4FreeMinDegreeWitness 88 7 := by
  apply er9_delete_degreeSeven_witness er9Delete3 <;> native_decide
theorem er9_delete4_degreeSeven_witness : C4FreeMinDegreeWitness 87 7 := by
  apply er9_delete_degreeSeven_witness er9Delete4 <;> native_decide
theorem er9_delete5_degreeSeven_witness : C4FreeMinDegreeWitness 86 7 := by
  apply er9_delete_degreeSeven_witness er9Delete5 <;> native_decide
theorem er9_delete6_degreeSeven_witness : C4FreeMinDegreeWitness 85 7 := by
  apply er9_delete_degreeSeven_witness er9Delete6 <;> native_decide
theorem er9_delete7_degreeSeven_witness : C4FreeMinDegreeWitness 84 7 := by
  apply er9_delete_degreeSeven_witness er9Delete7 <;> native_decide
theorem er9_delete8_degreeSeven_witness : C4FreeMinDegreeWitness 83 7 := by
  apply er9_delete_degreeSeven_witness er9Delete8 <;> native_decide
theorem er9_delete9_degreeSeven_witness : C4FreeMinDegreeWitness 82 7 := by
  apply er9_delete_degreeSeven_witness er9Delete9 <;> native_decide
theorem er9_delete10_degreeSeven_witness : C4FreeMinDegreeWitness 81 7 := by
  apply er9_delete_degreeSeven_witness er9Delete10 <;> native_decide

/-- The continuous ER(9) degree-seven witness band. -/
theorem degreeSeven_witness_eightyOne_add (j : ℕ) (hj : j ≤ 10) :
    C4FreeMinDegreeWitness (81 + j) 7 := by
  interval_cases j <;>
    first
    | exact er9_delete10_degreeSeven_witness
    | exact er9_delete9_degreeSeven_witness
    | exact er9_delete8_degreeSeven_witness
    | exact er9_delete7_degreeSeven_witness
    | exact er9_delete6_degreeSeven_witness
    | exact er9_delete5_degreeSeven_witness
    | exact er9_delete4_degreeSeven_witness
    | exact er9_delete3_degreeSeven_witness
    | exact er9_delete2_degreeSeven_witness
    | exact er9_delete1_degreeSeven_witness
    | exact er9_degreeSeven_witness

end Erdos85
