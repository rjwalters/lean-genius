import Mathlib

/-! Finite subset coordinates under a supplied labeling equivalence. -/
namespace Erdos85

def finsetCoordinates {V : Type*} [DecidableEq V] {n : ℕ}
    (E : Finset V) (e : Fin n ≃ (↑E : Set V)) (S : Finset V) : Finset (Fin n) :=
  Finset.univ.filter fun i => (e i).val ∈ S

@[simp] theorem mem_finsetCoordinates {V : Type*} [DecidableEq V] {n : ℕ}
    (E : Finset V) (e : Fin n ≃ (↑E : Set V)) (S : Finset V) (i : Fin n) :
    i ∈ finsetCoordinates E e S ↔ (e i).val ∈ S := by
  simp [finsetCoordinates]

theorem finsetCoordinates_card {V : Type*} [DecidableEq V] {n : ℕ}
    (E : Finset V) (e : Fin n ≃ (↑E : Set V)) (S : Finset V) :
    (finsetCoordinates E e S).card = (S ∩ E).card := by
  apply Finset.card_bij (fun i _ => (e i).val)
  · intro i hi
    exact Finset.mem_inter.mpr ⟨(mem_finsetCoordinates E e S i).mp hi, (e i).property⟩
  · intro i hi j hj h
    exact e.injective (Subtype.ext h)
  · intro x hx
    refine ⟨e.symm ⟨x,(Finset.mem_inter.mp hx).2⟩, ?_, ?_⟩
    · apply (mem_finsetCoordinates E e S _).mpr
      simpa using (Finset.mem_inter.mp hx).1
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨x,(Finset.mem_inter.mp hx).2⟩)

theorem finsetCoordinates_inter {V : Type*} [DecidableEq V] {n : ℕ}
    (E : Finset V) (e : Fin n ≃ (↑E : Set V)) (S T : Finset V) :
    finsetCoordinates E e S ∩ finsetCoordinates E e T = finsetCoordinates E e (S ∩ T) := by
  ext i
  simp

theorem finsetCoordinates_biUnion {V I : Type*} [DecidableEq V] [DecidableEq I] {n : ℕ}
    (E : Finset V) (e : Fin n ≃ (↑E : Set V)) (A : Finset I) (S : I → Finset V) :
    A.biUnion (fun x => finsetCoordinates E e (S x)) = finsetCoordinates E e (A.biUnion S) := by
  ext i
  simp

end Erdos85
#print axioms Erdos85.finsetCoordinates_card
#print axioms Erdos85.finsetCoordinates_inter
#print axioms Erdos85.finsetCoordinates_biUnion
