import Proofs.Erdos85IncidenceEqualityMarkedDegree
import Proofs.Erdos85BinaryIncidenceBottleneckEnergy

/-!
# Triangle-free degree at minimum bottleneck energy

This attaches the abstract marked-degree equality classifier to the literal
incidence-bottleneck column.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquare_minimumIncidenceEnergy_triangleFreeDegree_eq_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 8 ≤ q)
    (hqEven : Even q) (hfour : 4 ∣ q)
    (hreg : ∀ v, G.degree v = q) (x : V) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let y := fun v => (A * D - (J - A)) v x
    2 ≤ (finiteVectorSupport y).card →
    (finiteVectorSupport y).card ≤ q →
    (finiteVectorSupport y).card *
      (q - (finiteVectorSupport y).card + 1) ≤ 2 * q →
    (∑ v, y v = 0) →
    (∑ v, y v ^ 2 = (q : ℤ)) →
    (triangleFreeEdgeGraph G).degree x = 0 ∨
      (triangleFreeEdgeGraph G).degree x = 2 := by
  dsimp only
  intro hmlo hmhi hmul hsum henergy
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := Matrix.of (fun _ _ : V => (1 : ℤ))
  let y := fun v => (A * D - (J - A)) v x
  have hdiag : y x = ((triangleFreeEdgeGraph G).degree x : ℤ) - 1 := by
    dsimp [y, A, D, J]
    exact incidenceBottleneck_diag_eq_triangleFreeDegree_sub_one G x
  have htEven : Even ((triangleFreeEdgeGraph G).degree x) :=
    binarySquare_regular_triangleFree_degree_even G hfree hqEven hreg x
  have hodd : Odd (y x) := by
    obtain ⟨k, hk⟩ := htEven
    refine ⟨k - 1, ?_⟩
    rw [hdiag]
    push_cast [hk]
    ring
  exact minimumEnergy_markedDegree_eq_zero_or_two
    y hq hmlo hmhi hmul hsum henergy hfour x hodd
      ((triangleFreeEdgeGraph G).degree x) hdiag

end

end Erdos85

#print axioms Erdos85.binarySquare_minimumIncidenceEnergy_triangleFreeDegree_eq_zero_or_two
