import Proofs.Erdos85FinalDyadicEndpointHalfResidualProfile

/-!
# Saturation of the endpoint residual cell

The residual cell has size `r(q-1)`.  The nonexceptional layer sends exactly
`r` edges per vertex into it, saturating the full degree of every residual
vertex back into the nonexceptional layer.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The endpoint residual cell outside both the shore and negative-high class
has cardinality `r(q-1)`. -/
theorem finalDyadic_endpoint_residualCell_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    ((Finset.univ : Finset V) \ (S ∪
      finalDyadicNegativeHighCutCenters G S j r)).card = r * (q - 1) := by
  let m := 2 ^ j
  let M := finalDyadicNegativeHighCutCenters G S j r
  let W := (Finset.univ : Finset V) \ (S ∪ M)
  have hScardZ : (S.card : ℤ) = 2 * (m : ℤ) * m + r := by
    have hcardZ : (Fintype.card V : ℤ) = (q : ℤ) ^ 2 := by
      rw [hcard]
      push_cast
      ring
    rw [hcardZ, hqa] at hdisp
    change 2 * (S.card : ℤ) - (2 * (m : ℤ)) ^ 2 = 2 * (r : ℤ)
      at hdisp
    nlinarith
  have hMcard := finalDyadic_negativeHigh_card_eq_q_mul_empty
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique
  change M.card = q * (emptyLineCenters G S).card at hMcard
  have hpop := finalDyadic_endpoint_full_empty_card_eq
    G hqa hreg S hdiv hdisp (by omega) hsupport
  have hEcard := hpop.1
  change (emptyLineCenters G S).card = m - r at hEcard
  have hMS : Disjoint M S := by
    rw [Finset.disjoint_left]
    intro x hxM hxS
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hxM).1) hxS
  have hunionCard : (S ∪ M).card = S.card + M.card := by
    rw [Finset.card_union_of_disjoint hMS.symm]
  have hpart := Finset.card_sdiff_add_card_inter
    (Finset.univ : Finset V) (S ∪ M)
  have hinter : (Finset.univ : Finset V) ∩ (S ∪ M) = S ∪ M := by simp
  rw [hinter, Finset.card_univ, hcard, hunionCard] at hpart
  change W.card + (S.card + M.card) = q * q at hpart
  have hpartZ : (W.card : ℤ) + ((S.card : ℤ) + M.card) =
      (q : ℤ) * q := by
    exact_mod_cast hpart
  have hMcardZ : (M.card : ℤ) = (q : ℤ) * (m - r : ℕ) := by
    exact_mod_cast hMcard.trans (congrArg (q * ·) hEcard)
  have hqaZ : (q : ℤ) = 2 * (m : ℤ) := by exact_mod_cast hqa
  have hmrZ : ((m - r : ℕ) : ℤ) = (m : ℤ) - r := by
    rw [Nat.cast_sub (by omega : r ≤ m)]
  have hqsubZ : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  change W.card = r * (q - 1)
  apply Int.ofNat_inj.mp
  push_cast
  rw [hmrZ] at hMcardZ
  nlinarith

/-- Every residual-cell vertex spends its entire graph degree in the
nonexceptional layer. -/
theorem finalDyadic_endpoint_residual_neighbor_inter_nonexceptional_card_eq_q
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    ∀ w ∈ (Finset.univ : Finset V) \ (S ∪
        finalDyadicNegativeHighCutCenters G S j r),
      (G.neighborFinset w ∩
        ((Finset.univ : Finset V) \ exceptionalSignedSupport G S q)).card = q := by
  let M := finalDyadicNegativeHighCutCenters G S j r
  let H := (Finset.univ : Finset V) \ exceptionalSignedSupport G S q
  let W := (Finset.univ : Finset V) \ (S ∪ M)
  have hHcard : H.card = q * (q - 1) := by
    dsimp only [H]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      hcard, hsupport]
    have hqpos : 0 < q := by omega
    have hsplit : q * (q - 1) + q = q * q := by
      calc
        q * (q - 1) + q = q * ((q - 1) + 1) := by ring
        _ = q * q := by rw [Nat.sub_add_cancel hqpos]
    omega
  have hWcard : W.card = r * (q - 1) :=
    finalDyadic_endpoint_residualCell_card_eq
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique
  have hleft : ∑ z ∈ H, (G.neighborFinset z ∩ W).card = H.card * r := by
    calc
      _ = ∑ _z ∈ H, r := by
        apply Finset.sum_congr rfl
        intro z hzH
        have hzNotSupport : z ∉ exceptionalSignedSupport G S q :=
          (Finset.mem_sdiff.mp hzH).2
        rw [show G.neighborFinset z ∩ W =
            G.neighborFinset z \ (S ∪ M) by
          ext v
          simp [W]]
        exact
          (finalDyadic_endpoint_nonexceptional_residual_degree_profile
            G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
              hsupport hemptyClique hzNotSupport).2.2
      _ = H.card * r := by simp
  have hcomm := sum_card_neighbor_inter_comm G H W
  rw [hleft] at hcomm
  have hright : ∑ w ∈ W, (G.neighborFinset w ∩ H).card = q * W.card := by
    rw [← hcomm, hHcard, hWcard]
    ring
  have hle : ∀ w ∈ W, (G.neighborFinset w ∩ H).card ≤ q := by
    intro w _hw
    calc
      _ ≤ (G.neighborFinset w).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  exact eq_bound_of_sum_eq_card_mul W
    (fun w => (G.neighborFinset w ∩ H).card) q hle hright

end


end Erdos85

#print axioms Erdos85.finalDyadic_endpoint_residualCell_card_eq
#print axioms
  Erdos85.finalDyadic_endpoint_residual_neighbor_inter_nonexceptional_card_eq_q
