import Proofs.Erdos85C4FreeRegularAdjacencyCube

/-! # Cubic-walk mass on the nonneighbor sector -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Vertices other than `a` that are not adjacent to `a`. -/
def cubicNonneighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) : Finset V :=
  (Finset.univ.erase a).filter fun b ↦ ¬ G.Adj a b

/-- The cubic row mass outside the diagonal and open neighborhood is what
remains after subtracting the `d` adjacent entries, each equal to `2d-1`,
from the total row mass `d^3`. -/
theorem c4Free_regular_cubicNonneighborMass_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    (∑ b ∈ cubicNonneighborFinset G a, A3 a b) =
      (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a := by
  classical
  dsimp only
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let N := G.neighborFinset a
  let Q := cubicNonneighborFinset G a
  have hN : (Finset.univ.erase a).filter (fun b ↦ G.Adj a b) = N := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      N, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨_, hab⟩
      exact hab
    · intro hab
      refine ⟨⟨?_, trivial⟩, hab⟩
      intro hba
      subst b
      exact G.loopless.irrefl a hab
  have hQ : (Finset.univ.erase a).filter (fun b ↦ ¬ G.Adj a b) = Q := rfl
  have hneighbor : (∑ b ∈ N, A3 a b) =
      (d : ℤ) * (2 * (d : ℤ) - 1) := by
    calc
      _ = ∑ _b ∈ N, (2 * (d : ℤ) - 1) := by
        apply Finset.sum_congr rfl
        intro b hb
        apply c4Free_regular_adjMatrix_cube_apply_of_adj G hfree d hreg
        exact (G.mem_neighborFinset a b).mp hb
      _ = (d : ℤ) * (2 * (d : ℤ) - 1) := by
        simp [N, G.card_neighborFinset_eq_degree, hreg]
        ring
  have hsplitErase := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ.erase a) (p := fun b ↦ G.Adj a b)
    (f := fun b ↦ A3 a b)
  rw [hN, hQ] at hsplitErase
  have hsplitDiag := Finset.sum_erase_add
    (s := (Finset.univ : Finset V)) (f := fun b ↦ A3 a b)
      (Finset.mem_univ a)
  have hrow : (∑ b : V, A3 a b) = (d : ℤ) ^ 3 := by
    simpa [A3] using regular_adjMatrix_cube_row_sum G d hreg a
  rw [← hsplitErase, hneighbor] at hsplitDiag
  change (∑ b ∈ Q, A3 a b) =
    (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a
  omega

/-- Specialization to the h305 service parameters: the 41 nonneighbor
entries in a cubic row have total mass `150 - A3(a,a)`. -/
theorem sixRegular_fortyEight_cubicNonneighborMass_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    (∑ b ∈ cubicNonneighborFinset G a, A3 a b) = 150 - A3 a a := by
  have h := c4Free_regular_cubicNonneighborMass_eq G hfree 6 hreg a
  norm_num at h ⊢
  exact h

end

end Erdos85

#print axioms Erdos85.c4Free_regular_cubicNonneighborMass_eq
#print axioms Erdos85.sixRegular_fortyEight_cubicNonneighborMass_eq
