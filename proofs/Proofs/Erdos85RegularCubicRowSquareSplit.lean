import Proofs.Erdos85C4FreeRegularCubicNonneighborMass

/-! # Arbitrary-degree cubic row-square decomposition

Node: F.3 GENERALIZATION.  This removes the degree-six and order-48
specialization from the local sixth-moment row ledger.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- For a `d`-regular C4-free graph, one cubic row splits into its diagonal,
the fixed adjacent value `2d-1`, and the nonneighbor sector. -/
theorem regular_c4Free_cube_row_square_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    (∑ b, (A3 a b) ^ 2) =
      (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
        ∑ b ∈ cubicNonneighborFinset G a, (A3 a b) ^ 2 := by
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
  have hneighbor : (∑ b ∈ N, (A3 a b) ^ 2) =
      (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 := by
    calc
      _ = ∑ _b ∈ N, (2 * (d : ℤ) - 1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        have hbval : A3 a b = 2 * (d : ℤ) - 1 := by
          change (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a b =
            2 * (d : ℤ) - 1
          exact c4Free_regular_adjMatrix_cube_apply_of_adj
            G hfree d hreg ((G.mem_neighborFinset a b).mp hb)
        rw [hbval]
      _ = (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 := by
        simp [N, G.card_neighborFinset_eq_degree, hreg]
  have hsplitErase := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ.erase a) (p := fun b ↦ G.Adj a b)
    (f := fun b ↦ (A3 a b) ^ 2)
  rw [hN, hQ] at hsplitErase
  have hsplitDiag := Finset.sum_erase_add
    (s := (Finset.univ : Finset V)) (f := fun b ↦ (A3 a b) ^ 2)
      (Finset.mem_univ a)
  rw [← hsplitErase, hneighbor] at hsplitDiag
  simpa [A3, Q, add_assoc, add_left_comm, add_comm] using hsplitDiag.symm

/-- The degree-six row split is recovered by direct specialization, showing
that the q-generic statement is a genuine replacement for the old local
ledger rather than a parallel interface. -/
theorem sixRegular_c4Free_cube_row_square_split_of_general
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    (∑ b, (A3 a b) ^ 2) =
      6 * 11 ^ 2 + (A3 a a) ^ 2 +
        ∑ b ∈ cubicNonneighborFinset G a, (A3 a b) ^ 2 := by
  simpa using regular_c4Free_cube_row_square_split G hfree 6 hreg a

end


end Erdos85

#print axioms Erdos85.regular_c4Free_cube_row_square_split
#print axioms Erdos85.sixRegular_c4Free_cube_row_square_split_of_general
