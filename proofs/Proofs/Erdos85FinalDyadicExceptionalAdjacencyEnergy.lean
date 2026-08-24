import Proofs.Erdos85FinalDyadicExceptionalAdjacencyProfile

/-!
# Energy of the final exceptional adjacency profile

The four pointwise adjacency levels give an exact quadratic norm in terms of
the two high defect-cut classes.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The squared norm of the canonical exceptional adjacency image is
`|S| + 3|P| + |M|`. -/
theorem finalDyadic_exceptionalAdjacencyBalance_sum_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j) :
    ∑ v : V, (finalDyadicExceptionalAdjacencyBalance G S q v) ^ 2 =
      (S.card : ℤ) +
        3 * (finalDyadicPositiveHighCutCenters G S q r).card +
        (finalDyadicNegativeHighCutCenters G S j r).card := by
  let balance := finalDyadicExceptionalAdjacencyBalance G S q
  let P := finalDyadicPositiveHighCutCenters G S q r
  let M := finalDyadicNegativeHighCutCenters G S j r
  have hpos : ∀ v ∈ S,
      (balance v) ^ 2 = (1 : ℤ) + if v ∈ P then 3 else 0 := by
    intro v hv
    have hlevel := finalDyadic_positiveShore_exceptionalAdjacencyBalance
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf v hv
    change balance v = if v ∈ P then 2 else 1 at hlevel
    rw [hlevel]
    by_cases hvP : v ∈ P <;> simp [hvP]
  have hneg : ∀ v ∈ (Sᶜ : Finset V),
      (balance v) ^ 2 = if v ∈ M then (1 : ℤ) else 0 := by
    intro v hv
    have hvNot : v ∉ S := Finset.mem_compl.mp hv
    have hlevel := finalDyadic_negativeShore_exceptionalAdjacencyBalance
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf v hvNot
    change balance v = if v ∈ M then -1 else 0 at hlevel
    rw [hlevel]
    by_cases hvM : v ∈ M <;> simp [hvM]
  have hPsub : P ⊆ S := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hMsub : M ⊆ (Sᶜ : Finset V) := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hsumPos : ∑ v ∈ S, (balance v) ^ 2 =
      (S.card : ℤ) + 3 * P.card := by
    calc
      _ = ∑ v ∈ S, ((1 : ℤ) + if v ∈ P then 3 else 0) := by
        apply Finset.sum_congr rfl
        exact hpos
      _ = (S.card : ℤ) + 3 * P.card := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
        have hSP : S ∩ P = P := Finset.inter_eq_right.mpr hPsub
        rw [hSP]
        simp
        ring
  have hsumNeg : ∑ v ∈ (Sᶜ : Finset V), (balance v) ^ 2 =
      (M.card : ℤ) := by
    calc
      _ = ∑ v ∈ (Sᶜ : Finset V),
          (if v ∈ M then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        exact hneg
      _ = (M.card : ℤ) := by
        rw [Finset.sum_ite_mem]
        have hSM : (Sᶜ : Finset V) ∩ M = M :=
          Finset.inter_eq_right.mpr hMsub
        rw [hSM]
        simp
  have hunion : S ∪ (Sᶜ : Finset V) = Finset.univ := by ext x; simp
  have hdisjoint : Disjoint S (Sᶜ : Finset V) := by
    rw [Finset.disjoint_left]
    simp
  change (∑ v ∈ (Finset.univ : Finset V), (balance v) ^ 2) =
    (S.card : ℤ) + 3 * (P.card : ℤ) + (M.card : ℤ)
  rw [← hunion, Finset.sum_union hdisjoint,
    hsumPos, hsumNeg]

end

end Erdos85

#print axioms Erdos85.finalDyadic_exceptionalAdjacencyBalance_sum_sq
