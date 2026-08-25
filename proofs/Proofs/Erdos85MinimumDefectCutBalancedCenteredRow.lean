import Proofs.Erdos85IncidenceEqualitySupportClassification
import Proofs.Erdos85DefectMaxEdgeConnectivity

/-!
# Balanced centered rows on minimum defect cuts

For any `q`-vertex shore in a binary square-order graph, the centered
incidence row has squared energy equal to the second-order-defect cut.  At
the minimum even cut value `q`, the C4 support sandwich and the bounded-below
minimum-energy classifier force exactly `q/2` entries `+1` and `q/2` entries
`-1`.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- A `q`-vertex defect cut of size exactly `q` has a balanced signed-unit
centered incidence row. -/
theorem binarySquare_minimumDefectCut_centeredRow_balanced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 8 ≤ q)
    (hfour : 4 ∣ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (hScard : S.card = q)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G) S = q) :
    let y := (G.adjMatrix ℤ).mulVec (finsetIndicatorInt S) -
      (1 : V → ℤ)
    (finiteVectorSupport y).card = q ∧
      2 * (Finset.univ.filter fun v => y v = 1).card = q ∧
      2 * (Finset.univ.filter fun v => y v = -1).card = q := by
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℤ
  let chi := finsetIndicatorInt S
  let one : V → ℤ := fun _ => 1
  let y := A.mulVec chi - one
  have hScardMul : S.card = q * 1 := by simpa using hScard
  have henergy : ∑ v, y v ^ 2 = (q : ℤ) := by
    have he := c4Free_regular_centeredShore_energy_eq_defectCut
      G hfree hreg hcard S hScardMul
    dsimp only at he
    simpa [y, A, chi, one, D, hcut] using he
  have hsum : ∑ v, y v = 0 := by
    have hs := regular_squareOrder_centeredShore_sum_eq_zero
      G hreg hcard S hScardMul
    dsimp only at hs
    simpa [y, A, chi, one] using hs
  have hyne : y ≠ 0 := by
    intro hy0
    have hz : ∑ v, y v ^ 2 = 0 := by simp [hy0]
    rw [henergy] at hz
    have hqne : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    exact hqne hz
  have hbounds : 2 ≤ (finiteVectorSupport y).card ∧
      (finiteVectorSupport y).card ≤ q := by
    have hb := integerZeroSum_support_card_bounds_of_sq_sum_eq
      y hyne hsum henergy
    simpa using hb
  have hlower : (finiteVectorSupport y).card *
      (q - (finiteVectorSupport y).card + 1) ≤
      (finiteVectorSupport (A.mulVec y)).card := by
    exact c4Free_regular_int_mulVecSupport_lower
      G hfree hreg y hbounds.2
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ v, D.degree v = q - 1 := by
    intro v
    have hd := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus v
    change D.degree v = (q - 3) + 2 at hd
    omega
  have himage0 := c4Free_regular_centeredShore_image_eq_defectLaplacian
    G hfree hreg S hScardMul
  have himage : A.mulVec y = fun v =>
      finsetGraphLaplacianIndicator D S v := by
    change A.mulVec y =
      (((q : ℤ) - 1) • (1 : Matrix V V ℤ) - D.adjMatrix ℤ).mulVec chi
      at himage0
    rw [himage0]
    funext v
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    change (((q : ℤ) - 1) * finsetIndicatorInt S v -
      (D.adjMatrix ℤ).mulVec (finsetIndicatorInt S) v) =
        finsetGraphLaplacianIndicator D S v
    rw [adjMatrix_mulVec_finsetIndicatorInt_apply]
    by_cases hv : v ∈ S <;>
      simp [finsetGraphLaplacianIndicator, hDreg v, hv,
        Nat.cast_sub (by omega : 1 ≤ q)]
  have hupper : (finiteVectorSupport (A.mulVec y)).card ≤ 2 * q := by
    rw [himage]
    change (Finset.univ.filter fun v =>
      finsetGraphLaplacianIndicator D S v ≠ 0).card ≤ 2 * q
    have hu := card_support_finsetGraphLaplacianIndicator_le_two_mul_cutSize D S
    simpa [D, hcut] using hu
  have hmul : (finiteVectorSupport y).card *
      (q - (finiteVectorSupport y).card + 1) ≤ 2 * q :=
    hlower.trans hupper
  have hlowerEntry : ∀ v, (-1 : ℤ) ≤ y v := by
    intro v
    change (-1 : ℤ) ≤ A.mulVec chi v - 1
    have hnonneg : (0 : ℤ) ≤ A.mulVec chi v := by
      rw [adjMatrix_mulVec_finsetIndicatorInt_apply]
      exact_mod_cast (Nat.zero_le
        (G.neighborFinset v ∩ S).card)
    omega
  exact minimumEnergy_support_eq_self_and_balanced_of_neg_one_le
    y hq hbounds.1 hbounds.2 hmul hsum henergy hfour hlowerEntry

end

end Erdos85

#print axioms Erdos85.binarySquare_minimumDefectCut_centeredRow_balanced
