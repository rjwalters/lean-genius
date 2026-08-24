import Proofs.Erdos85FinalDyadicExceptionalFullDefectPairCensus

/-!
# Defect-regular capacity for the full exceptional family

A complete defect cross from `F` to a disjoint family `E` consumes `|E|`
of every vertex's defect degree.  The remaining capacity bounds twice the
number of edges internal to `F`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A complete cross into a disjoint family consumes the corresponding
degree capacity at every vertex of `F`. -/
theorem twice_supportedEdges_add_cross_le_regular_capacity
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {d : ℕ} (hreg : ∀ v, D.degree v = d)
    (F E : Finset V) (hFE : Disjoint F E)
    (hcross : ∀ ⦃v w⦄, v ∈ F → w ∈ E → D.Adj v w) :
    2 * (supportedEdgeGraph D F).edgeFinset.card + F.card * E.card ≤
      d * F.card := by
  have hpoint : ∀ v ∈ F,
      (D.neighborFinset v ∩ F).card + E.card ≤ d := by
    intro v hv
    have hEsub : E ⊆ D.neighborFinset v := by
      intro w hw
      simpa [SimpleGraph.mem_neighborFinset] using hcross hv hw
    have hdisj : Disjoint (D.neighborFinset v ∩ F) E := by
      apply Finset.disjoint_left.mpr
      intro w hwF hwE
      exact Finset.disjoint_left.mp hFE (Finset.mem_inter.mp hwF).2 hwE
    have hunion : D.neighborFinset v ∩ F ∪ E ⊆ D.neighborFinset v := by
      intro w hw
      rcases Finset.mem_union.mp hw with hwF | hwE
      · exact (Finset.mem_inter.mp hwF).1
      · exact hEsub hwE
    calc
      (D.neighborFinset v ∩ F).card + E.card =
          (D.neighborFinset v ∩ F ∪ E).card := by
        rw [Finset.card_union_of_disjoint hdisj]
      _ ≤ (D.neighborFinset v).card := Finset.card_le_card hunion
      _ = d := by rw [D.card_neighborFinset_eq_degree, hreg]
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  rw [sum_internal_incidence_eq_twice_supported_edges D F] at hsum
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/-- Canonical full/empty specialization in the square-order defect graph. -/
theorem binarySquare_fullDefectEdges_add_full_empty_le_capacity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V) :
    2 * (supportedEdgeGraph (secondOrderDefectGraph G)
          (fullLineCenters G S q)).edgeFinset.card +
        (fullLineCenters G S q).card * (emptyLineCenters G S).card ≤
      (q - 1) * (fullLineCenters G S q).card := by
  apply twice_supportedEdges_add_cross_le_regular_capacity
    (secondOrderDefectGraph G)
    (binarySquare_regular_secondOrderDefect_degree_eq
      G hfree hq hreg hcard)
  · exact fullLineCenters_disjoint_emptyLineCenters G S (by omega)
  · intro v w hv hw
    exact binarySquare_full_empty_secondOrderDefect_adj
      G hfree (by omega) hreg S
        ((mem_fullLineCenters G S q v).mp hv)
        ((mem_emptyLineCenters G S w).mp hw)

/-- Substituting the exact energy census into defect regularity gives a
strictly sharper residual bound than the complete-pair bound. -/
theorem finalDyadic_exceptionalCensusResidual_add_full_empty_le_capacity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (2 * (r : ℤ)) ^ 2 + ((q : ℤ) - 1) * c -
        ((S.card : ℤ) +
          3 * (finalDyadicPositiveHighCutCenters G S q r).card +
          (finalDyadicNegativeHighCutCenters G S j r).card) -
        2 * (((emptyLineCenters G S).card.choose 2 : ℕ) : ℤ) +
        2 * (((fullLineCenters G S q).card : ℤ) *
          (emptyLineCenters G S).card) +
        ((fullLineCenters G S q).card : ℤ) *
          (emptyLineCenters G S).card ≤
      ((q - 1 : ℕ) : ℤ) * (fullLineCenters G S q).card := by
  have heq := finalDyadic_twice_fullDefectEdges_eq_exceptionalCensusResidual
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf hsupport hemptyClique
  have hcap := binarySquare_fullDefectEdges_add_full_empty_le_capacity
    G hfree hq hreg hcard S
  have hcapZ :
      2 * ((supportedEdgeGraph (secondOrderDefectGraph G)
          (fullLineCenters G S q)).edgeFinset.card : ℤ) +
        ((fullLineCenters G S q).card : ℤ) *
          (emptyLineCenters G S).card ≤
        ((q - 1 : ℕ) : ℤ) * (fullLineCenters G S q).card := by
    exact_mod_cast hcap
  rw [heq] at hcapZ
  exact hcapZ

end

end Erdos85

#print axioms Erdos85.twice_supportedEdges_add_cross_le_regular_capacity
#print axioms
  Erdos85.binarySquare_fullDefectEdges_add_full_empty_le_capacity
#print axioms
  Erdos85.finalDyadic_exceptionalCensusResidual_add_full_empty_le_capacity
