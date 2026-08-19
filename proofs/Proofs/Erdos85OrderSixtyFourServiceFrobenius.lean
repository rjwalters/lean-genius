import Proofs.Erdos85ExcessThreeServiceFrobenius
import Proofs.Erdos85OrderSixtyFourTriangleFreeColorOrder
import Proofs.Erdos85AntipodalCycleReservoir

/-!
# Antipodal-service Frobenius budget at order 64

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Exact order-64 antipodal service budget.**  In the all-size-sixteen
stratum, let `a` count vertices of triangle-free degree two.  The factorial
second moment of `A C`, the mixed chord moment, and the antipodal cube trace
sum to `2688 - 22a`. -/
theorem orderSixtyFour_allSixteen_service_factorialMoment_add_chord_add_cube_eq
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let a := (Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card
    (∑ x : Fin 64, ∑ y : Fin 64,
        (A * C) x y * ((A * C) x y - 1)) +
        Matrix.trace (T * C * C) + Matrix.trace (C * C * C) =
      2688 - 22 * (a : ℤ) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix (Fin 64)
  let a := (Finset.univ.filter fun x : Fin 64 =>
    (triangleFreeEdgeGraph G).degree x = 2).card
  have htdeg : ∀ x, (triangleFreeEdgeGraph G).degree x = 0 ∨
      (triangleFreeEdgeGraph G).degree x = 2 :=
    orderSixtyFour_allSixteen_triangleFree_degree_zero_or_two
      G hfree hreg hsize
  have hcdeg (x : Fin 64) : (antipodalGraph G).degree x =
      if (triangleFreeEdgeGraph G).degree x = 2 then 5 else 7 := by
    have h := antipodalGraph_degree_eq_excess_add_two_sub_triangleFree
      G hfree (d := 8) (e := 5) (by omega) hreg (by norm_num) x
    have hcardTf : (triangleFreeNeighbors G x).card =
        (triangleFreeEdgeGraph G).degree x := by
      rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
        triangleFreeEdgeGraph_neighborFinset]
    rw [h, hcardTf]
    rcases htdeg x with hx | hx <;> simp [hx]
  have hC2 : Matrix.trace (C * C) = 448 - 2 * (a : ℤ) := by
    rw [show Matrix.trace (C * C) =
        ∑ x : Fin 64, ((antipodalGraph G).degree x : ℤ) by
      simpa [C] using trace_adjMatrix_sq_eq_sum_degrees (antipodalGraph G)]
    calc
      (∑ x : Fin 64, ((antipodalGraph G).degree x : ℤ)) =
          ∑ x : Fin 64, ((7 : ℤ) -
            if (triangleFreeEdgeGraph G).degree x = 2 then 2 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hcdeg]
        split <;> simp_all
      _ = 448 - 2 * (a : ℤ) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
        simp [a]
        ring
  have hJC2 : Matrix.trace (J * (C * C)) = 3136 - 24 * (a : ℤ) := by
    have h := trace_onesMatrix_mul_adjMatrix_sq_eq_sum_degree_sq
      (antipodalGraph G)
    change Matrix.trace (J * (C * C)) = _ at h
    rw [h]
    calc
      (∑ x : Fin 64, ((antipodalGraph G).degree x : ℤ) ^ 2) =
          ∑ x : Fin 64, ((49 : ℤ) -
            if (triangleFreeEdgeGraph G).degree x = 2 then 24 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hcdeg]
        split <;> simp_all
      _ = 3136 - 24 * (a : ℤ) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
        simp [a]
        ring
  have hA2 : A * A = (7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) + J - D := by
    simpa [A, D, J] using
      adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hD : D = C + T := by
    simpa [D, C, T] using
      secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G
  have hDC2 : Matrix.trace (D * (C * C)) =
      Matrix.trace (T * C * C) + Matrix.trace (C * C * C) := by
    calc
      Matrix.trace (D * (C * C)) =
          Matrix.trace ((C + T) * (C * C)) := by rw [hD]
      _ = Matrix.trace (C * (C * C)) + Matrix.trace (T * (C * C)) := by
        rw [Matrix.add_mul, Matrix.trace_add]
      _ = Matrix.trace (T * C * C) + Matrix.trace (C * C * C) := by
        have hTC : T * (C * C) = T * C * C := by noncomm_ring
        have hCC : C * (C * C) = C * C * C := by noncomm_ring
        rw [hTC, hCC]
        ring
  have hAsym : ∀ x y, A x y = A y x := by
    intro x y
    simpa [A] using congrFun (congrFun (SimpleGraph.transpose_adjMatrix G) y) x
  have hCsym : ∀ x y, C x y = C y x := by
    intro x y
    simpa [C] using congrFun (congrFun
      (SimpleGraph.transpose_adjMatrix (antipodalGraph G)) y) x
  have hQ : (∑ x : Fin 64, ∑ y : Fin 64, ((A * C) x y) ^ 2) =
      6272 - 38 * (a : ℤ) -
        (Matrix.trace (T * C * C) + Matrix.trace (C * C * C)) := by
    rw [sum_mul_entry_sq_eq_trace_sq_mul_sq A C hAsym hCsym, hA2,
      Matrix.sub_mul, Matrix.add_mul, smul_mul_assoc, Matrix.one_mul,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, hC2, hJC2, hDC2]
    simp
    ring
  have hMass : (∑ x : Fin 64, ∑ y : Fin 64, (A * C) x y) =
      3584 - 16 * (a : ℤ) := by
    have h := sum_mul_adjMatrix_entry_eq_degree_mul_sum_degrees
      G (antipodalGraph G) hreg
    change (∑ x : Fin 64, ∑ y : Fin 64, (A * C) x y) = _ at h
    rw [h, ← trace_adjMatrix_sq_eq_sum_degrees (antipodalGraph G)]
    change (8 : ℤ) * Matrix.trace (C * C) = _
    rw [hC2]
    ring
  calc
    (∑ x : Fin 64, ∑ y : Fin 64,
          (A * C) x y * ((A * C) x y - 1)) +
          Matrix.trace (T * C * C) + Matrix.trace (C * C * C) =
        ((∑ x : Fin 64, ∑ y : Fin 64, ((A * C) x y) ^ 2) -
          ∑ x : Fin 64, ∑ y : Fin 64, (A * C) x y) +
          Matrix.trace (T * C * C) + Matrix.trace (C * C * C) := by
      congr 2
      calc
        (∑ x : Fin 64, ∑ y : Fin 64,
            (A * C) x y * ((A * C) x y - 1)) =
            ∑ x : Fin 64, ∑ y : Fin 64,
              (((A * C) x y) ^ 2 - (A * C) x y) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ = (∑ x : Fin 64, ∑ y : Fin 64, ((A * C) x y) ^ 2) -
            ∑ x : Fin 64, ∑ y : Fin 64, (A * C) x y := by
          simp_rw [Finset.sum_sub_distrib]
    _ = 2688 - 22 * (a : ℤ) := by rw [hQ, hMass]; ring

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_allSixteen_service_factorialMoment_add_chord_add_cube_eq
