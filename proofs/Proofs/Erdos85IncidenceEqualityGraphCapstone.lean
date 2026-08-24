import Proofs.Erdos85IncidenceEqualityTriangleFreeDegree
import Proofs.Erdos85DefectMaxEdgeConnectivity
import Proofs.Erdos85ConnectedIncidenceBottleneckRowRepresentation

/-!
# Graph capstone for equality in the incidence-energy bound

If a closed defect neighborhood has cut exactly `q`, the centered incidence
error has energy `q`.  The C4 support lower bound and the cut-endpoint upper
bound supply the equality classifier's sandwich, forcing the marked
triangle-free-edge degree to be zero or two.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
theorem binarySquare_closedDefectNeighborhood_cut_eq_degree_imp_triangleFreeDegree_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 8 ≤ q)
    (hqEven : Even q) (hfour : 4 ∣ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (x : V)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G)
      (insert x ((secondOrderDefectGraph G).neighborFinset x)) = q) :
    (triangleFreeEdgeGraph G).degree x = 0 ∨
      (triangleFreeEdgeGraph G).degree x = 2 := by
  let D := secondOrderDefectGraph G
  let S := insert x (D.neighborFinset x)
  let A := G.adjMatrix ℤ
  let chi := finsetIndicatorInt S
  let one : V → ℤ := fun _ => 1
  let y := A.mulVec chi - one
  let J := Matrix.of (fun _ _ : V => (1 : ℤ))
  let z := fun v => (A * D.adjMatrix ℤ - (J - A)) v x
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ v, D.degree v = q - 1 := by
    intro v
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus v
    change D.degree v = (q - 3) + 2 at h
    omega
  have hScard : S.card = q * 1 := by
    simp [S, hDreg x]
    omega
  have henergy : ∑ v, y v ^ 2 = (q : ℤ) := by
    have he := c4Free_regular_centeredShore_energy_eq_defectCut
      G hfree hreg hcard S hScard
    dsimp only at he
    simpa [y, A, chi, one, D, S, hcut] using he
  have hsum : ∑ v, y v = 0 := by
    have hs := regular_squareOrder_centeredShore_sum_eq_zero
      G hreg hcard S hScard
    dsimp only at hs
    simpa [y, A, chi, one] using hs
  have hyne : y ≠ 0 := by
    intro hy0
    have : ∑ v, y v ^ 2 = 0 := by simp [hy0]
    rw [henergy] at this
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    exact hq0 this
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
  have himage0 := c4Free_regular_centeredShore_image_eq_defectLaplacian
    G hfree hreg S hScard
  have himage : A.mulVec y = fun v =>
      finsetGraphLaplacianIndicator D S v := by
    change A.mulVec y =
      (((q : ℤ) - 1) • (1 : Matrix V V ℤ) - D.adjMatrix ℤ).mulVec
        (finsetIndicatorInt S) at himage0
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
    simpa [D, S, hcut] using hu
  have hmul : (finiteVectorSupport y).card *
      (q - (finiteVectorSupport y).card + 1) ≤ 2 * q :=
    hlower.trans hupper
  have hyz : y = z := by
    funext v
    have hr := incidenceBottleneck_apply_eq_closedNeighborhood_incidenceError
      G D x v
    change z v = A.mulVec (finsetIntIndicator S) v - 1 at hr
    rw [hr]
    dsimp [y, chi, one]
    rfl
  have hmloz : 2 ≤ (finiteVectorSupport z).card := by
    rw [← hyz]
    exact hbounds.1
  have hmhiz : (finiteVectorSupport z).card ≤ q := by
    rw [← hyz]
    exact hbounds.2
  have hmulz : (finiteVectorSupport z).card *
      (q - (finiteVectorSupport z).card + 1) ≤ 2 * q := by
    rw [← hyz]
    exact hmul
  have hsumz : ∑ v, z v = 0 := by rw [← hyz]; exact hsum
  have henergyz : ∑ v, z v ^ 2 = (q : ℤ) := by rw [← hyz]; exact henergy
  exact binarySquare_minimumIncidenceEnergy_triangleFreeDegree_eq_zero_or_two
    G hfree hq hqEven hfour hreg x hmloz hmhiz hmulz hsumz henergyz

end

end Erdos85

#print axioms Erdos85.binarySquare_closedDefectNeighborhood_cut_eq_degree_imp_triangleFreeDegree_zero_or_two
