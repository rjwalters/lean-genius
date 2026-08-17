import Proofs.Erdos85OrderSixtyFourComponentComplexGram
import Proofs.Erdos85ComponentLocalObstruction

/-! # Commutation of the exterior Gram correction -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a block identity `A² + Q = aI + J - D`, the correction `Q`
commutes with both `A` and `D` as soon as `A`, `D`, and `J` commute
pairwise in the required directions. -/
theorem correction_comm_of_sq_add_eq
    {K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]
    (A D J Q : Matrix n n K) (a : K)
    (hid : A * A + Q = a • (1 : Matrix n n K) + J - D)
    (hAD : A * D = D * A) (hAJ : A * J = J * A)
    (hDJ : D * J = J * D) :
    A * Q = Q * A ∧ D * Q = Q * D := by
  have hQ : Q = a • (1 : Matrix n n K) + J - D - A * A := by
    calc
      Q = (A * A + Q) - A * A := by noncomm_ring
      _ = (a • (1 : Matrix n n K) + J - D) - A * A := by rw [hid]
  have hDAA : D * (A * A) = (A * A) * D := by
    calc
      D * (A * A) = (D * A) * A := by rw [Matrix.mul_assoc]
      _ = (A * D) * A := by rw [← hAD]
      _ = A * (D * A) := by rw [Matrix.mul_assoc]
      _ = A * (A * D) := by rw [← hAD]
      _ = (A * A) * D := by rw [Matrix.mul_assoc]
  constructor
  · rw [hQ]
    noncomm_ring [hAD, hAJ]
  · rw [hQ]
    noncomm_ring [hDAA, hDJ]

/-- Over `ℂ`, the adjacency matrix of a regular graph commutes with the
base-changed all-ones matrix. -/
theorem adjMatrix_comm_onesMatrix_complex_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (hreg : ∀ x, H.degree x = d) :
    H.adjMatrix ℂ *
        (FriendshipTheoremOQ01.onesMatrix V).map (Int.castRingHom ℂ) =
      (FriendshipTheoremOQ01.onesMatrix V).map (Int.castRingHom ℂ) *
        H.adjMatrix ℂ := by
  have hz : H.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V =
      FriendshipTheoremOQ01.onesMatrix V * H.adjMatrix ℤ := by
    calc
      _ = (d : ℤ) • FriendshipTheoremOQ01.onesMatrix V :=
        FriendshipTheoremOQ01.adjMatrix_mul_ones H d hreg
      _ = _ := (onesMatrix_mul_adjMatrix_of_regular H d hreg).symm
  have hc := congrArg (fun M ↦ M.map (Int.castRingHom ℂ)) hz
  simpa only [Matrix.map_mul, adjMatrix_map_intCast] using hc

/-- On every order-64 defect component, the exterior Gram matrix commutes
with both the internal ambient adjacency block and the internal defect
adjacency block. -/
theorem orderSixtyFour_defectComponent_exteriorGram_comm
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hlocal : ∀ x : c.supp, (G.induce c.supp).degree x = 2) :
    let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
    let A := (G.induce c.supp).adjMatrix ℂ
    let D := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ
    A * (B * Matrix.conjTranspose B) =
        (B * Matrix.conjTranspose B) * A ∧
      D * (B * Matrix.conjTranspose B) =
        (B * Matrix.conjTranspose B) * D := by
  classical
  let Dg := secondOrderDefectGraph G
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  let A := (G.induce c.supp).adjMatrix ℂ
  let D := (Dg.induce c.supp).adjMatrix ℂ
  let J := (FriendshipTheoremOQ01.onesMatrix c.supp).map
    (Int.castRingHom ℂ)
  have hid :=
    orderSixtyFour_defectComponent_internal_sq_add_exteriorGram_complex
      G hfree hmin hcover c
  change A * A + B * Matrix.conjTranspose B =
      (7 : ℂ) • (1 : Matrix c.supp c.supp ℂ) + J - D at hid
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hAD :=
    adjMatrix_comm_secondOrderDefect_induce_component_of_regular_complex
      G hfree hreg c
  change A * D = D * A at hAD
  have hDregGlobal : ∀ x : Fin 64, Dg.degree x = 7 :=
    (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
  have hDlocal : ∀ x : c.supp, (Dg.induce c.supp).degree x = 7 := by
    intro x
    rw [degree_induce_connectedComponent_supp Dg c x]
    exact hDregGlobal x
  have hAJ := adjMatrix_comm_onesMatrix_complex_of_regular
    (G.induce c.supp) 2 hlocal
  have hDJ := adjMatrix_comm_onesMatrix_complex_of_regular
    (Dg.induce c.supp) 7 hDlocal
  change A * J = J * A at hAJ
  change D * J = J * D at hDJ
  exact correction_comm_of_sq_add_eq A D J
    (B * Matrix.conjTranspose B) 7 hid hAD hAJ hDJ

end

end Erdos85
