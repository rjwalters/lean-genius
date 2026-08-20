import Proofs.Erdos85CubicTraceParity
import Proofs.Erdos85CubicRowSquareExcess
import Proofs.Erdos85C4FreeRegularCubicNonneighborMass

/-! # Global cubic histogram excess ledger -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The cubic-square mass of one service row splits into six fixed edge
entries, its diagonal, and its 41 nonneighbor entries. -/
theorem sixRegular_c4Free_cube_row_square_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    (∑ b, (A3 a b) ^ 2) =
      6 * 11 ^ 2 + (A3 a a) ^ 2 +
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
  have hneighbor : (∑ b ∈ N, (A3 a b) ^ 2) = 6 * 11 ^ 2 := by
    calc
      _ = ∑ _b ∈ N, (11 : ℤ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        have hbval : A3 a b = 11 := by
          change (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a b = 11
          simpa using c4Free_regular_adjMatrix_cube_apply_of_adj
            G hfree 6 hreg ((G.mem_neighborFinset a b).mp hb)
        rw [hbval]
      _ = 6 * 11 ^ 2 := by
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

/-- Exact global trace ledger: `61056 = 48*1272` is the universal row
baseline, while the displayed sum records the diagonal choice and every
departure of a nonneighbor entry from three or four. -/
theorem sixRegular_fortyEight_trace_six_eq_baseline_add_histogramExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    let A := G.adjMatrix ℤ
    let A3 := A * A * A
    Matrix.trace (A ^ 6) = 61056 +
      ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
        ∑ b ∈ cubicNonneighborFinset G a,
          (A3 a b - 3) * (A3 a b - 4)) := by
  classical
  dsimp only
  let A := G.adjMatrix ℤ
  let A3 := A * A * A
  have hA : A.IsSymm := by
    simpa [A] using (SimpleGraph.isSymm_adjMatrix G ℤ)
  rw [trace_pow_six_eq_sum_cube_apply_sq A hA]
  have hpow : A ^ 3 = A3 := by simp [A3, pow_succ]
  simp_rw [hpow]
  calc
    (∑ a, ∑ b, (A3 a b) ^ 2) =
        ∑ a, (1284 - 7 * A3 a a + (A3 a a) ^ 2 +
          ∑ b ∈ cubicNonneighborFinset G a,
            (A3 a b - 3) * (A3 a b - 4)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sixRegular_c4Free_cube_row_square_split G hfree hreg a]
      have hcardQ := sixRegular_fortyEight_cubicNonneighborFinset_card
        G hcard hreg a
      have hmass := sixRegular_fortyEight_cubicNonneighborMass_eq
        G hfree hreg a
      rw [fortyOne_sum_sq_eq_baseline_add_excess
        (cubicNonneighborFinset G a) (fun b ↦ A3 a b) (A3 a a)
        hcardQ hmass]
      ring
    _ = ∑ a, ((1272 : ℤ) + ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
          ∑ b ∈ cubicNonneighborFinset G a,
            (A3 a b - 3) * (A3 a b - 4))) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 61056 + ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
          ∑ b ∈ cubicNonneighborFinset G a,
            (A3 a b - 3) * (A3 a b - 4)) := by
      rw [Finset.sum_add_distrib]
      simp [hcard]

/-- The strict spectral result plus trace parity forces at least `194` units
of global diagonal/histogram excess above the `61056` baseline. -/
theorem sixRegular_fortyEight_histogramExcess_ge_194
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (hstrict : 61248 < Matrix.trace ((G.adjMatrix ℤ) ^ 6)) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    194 ≤ ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
      ∑ b ∈ cubicNonneighborFinset G a,
        (A3 a b - 3) * (A3 a b - 4)) := by
  dsimp only
  have heven := even_trace_adjMatrix_pow_six G
  have htrace := even_strict_sixthMoment_ge_61250 _ heven hstrict
  rw [sixRegular_fortyEight_trace_six_eq_baseline_add_histogramExcess
    G hfree hcard hreg] at htrace
  omega

end

end Erdos85

#print axioms Erdos85.sixRegular_c4Free_cube_row_square_split
#print axioms Erdos85.sixRegular_fortyEight_trace_six_eq_baseline_add_histogramExcess
#print axioms Erdos85.sixRegular_fortyEight_histogramExcess_ge_194
