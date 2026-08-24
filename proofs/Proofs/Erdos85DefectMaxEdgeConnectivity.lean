import Proofs.Erdos85DefectCutCenteredZeroSum
import Proofs.Erdos85DefectCutLaplacianSupport
import Proofs.Erdos85IntegerZeroSumSupportBounds
import Proofs.Erdos85DefectCutSupportArithmetic
import Proofs.Erdos85UniqueNeighborMulVecSupportInt

open SimpleGraph
namespace Erdos85
noncomputable section

set_option maxHeartbeats 800000 in
theorem false_of_binarySquare_small_defectCut_of_centered_energy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (hScard : S.card = q * a)
    (hcutPos : 0 < finsetGraphCutSize (secondOrderDefectGraph G) S)
    (hcutSmall : finsetGraphCutSize (secondOrderDefectGraph G) S ≤ q - 2)
    (henergy :
      let A := G.adjMatrix ℤ
      let chi := finsetIndicatorInt S
      let one : V → ℤ := fun _ => 1
      let y := A.mulVec chi - (a : ℤ) • one
      ∑ x, y x ^ 2 =
        (finsetGraphCutSize (secondOrderDefectGraph G) S : ℤ)) : False := by
  let A := G.adjMatrix ℤ
  let D := secondOrderDefectGraph G
  let chi := finsetIndicatorInt S
  let one : V → ℤ := fun _ => 1
  let y := A.mulVec chi - (a : ℤ) • one
  let delta := finsetGraphCutSize D S
  let m := (finiteVectorSupport y).card
  have hy : y ≠ 0 := by
    intro hy0
    have hzero : ∑ x, y x ^ 2 = 0 := by simp [hy0]
    have : (delta : ℤ) = 0 := by
      rw [← henergy]
      exact hzero
    have : delta = 0 := by exact_mod_cast this
    have hpos : 0 < delta := by simpa [delta] using hcutPos
    omega
  have hysum : ∑ x, y x = 0 := by
    exact regular_squareOrder_centeredShore_sum_eq_zero
      G hreg hcard S hScard
  have hbounds : 2 ≤ m ∧ m ≤ delta := by
    exact integerZeroSum_support_card_bounds_of_sq_sum_eq
      y hy hysum henergy
  have hmQ : m ≤ q := hbounds.2.trans (hcutSmall.trans (Nat.sub_le q 2))
  have hlower : m * (q - m + 1) ≤
      (finiteVectorSupport (A.mulVec y)).card := by
    exact c4Free_regular_int_mulVecSupport_lower G hfree hreg y hmQ
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have himage0 := c4Free_regular_centeredShore_image_eq_defectLaplacian
    G hfree hreg S hScard
  have himage : A.mulVec y = fun x => finsetGraphLaplacianIndicator D S x := by
    rw [himage0]
    funext x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    change
      (((q : ℤ) - 1) * finsetIndicatorInt S x -
        (D.adjMatrix ℤ).mulVec (finsetIndicatorInt S) x) =
        finsetGraphLaplacianIndicator D S x
    rw [adjMatrix_mulVec_finsetIndicatorInt_apply]
    by_cases hx : x ∈ S <;>
      simp [finsetGraphLaplacianIndicator, hDreg x, hx,
        Nat.cast_sub (by omega : 1 ≤ q)]
  have hsupportEq : finiteVectorSupport (A.mulVec y) =
      Finset.univ.filter (fun x => finsetGraphLaplacianIndicator D S x ≠ 0) := by
    rw [himage]
    rfl
  have hupper : (finiteVectorSupport (A.mulVec y)).card ≤ 2 * delta := by
    rw [hsupportEq]
    exact card_support_finsetGraphLaplacianIndicator_le_two_mul_cutSize D S
  exact false_of_supportLower_le_two_mul_cut
    hbounds.1 hbounds.2 hcutSmall (hlower.trans hupper)

#print axioms false_of_binarySquare_small_defectCut_of_centered_energy

end
end Erdos85

