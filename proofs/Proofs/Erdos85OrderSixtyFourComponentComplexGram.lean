import Proofs.Erdos85OrderSixtyFourComponentGramIdentity

/-! # Complex exterior Gram identity on an order-64 defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The two off-diagonal adjacency blocks across a vertex cut are conjugate
transposes. -/
theorem adjMatrix_toBlock_compl_eq_conjTranspose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Prop) [DecidablePred p] :
    (G.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) p =
      Matrix.conjTranspose
        ((G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)) := by
  ext i j
  simp [Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply, G.adj_comm]

/-- Complex Hermitian form of the component square identity.  Writing `B`
for the incidence block from `c` to its exterior, the additional term is
literally the positive-semidefinite Gram matrix `B Bᴴ`. -/
theorem orderSixtyFour_defectComponent_internal_sq_add_exteriorGram_complex
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
    (G.induce c.supp).adjMatrix ℂ * (G.induce c.supp).adjMatrix ℂ +
        B * Matrix.conjTranspose B =
      (7 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
        (FriendshipTheoremOQ01.onesMatrix c.supp).map
          (Int.castRingHom ℂ) -
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ := by
  classical
  let D := secondOrderDefectGraph G
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular
    G hfree hreg
  have hsqC : G.adjMatrix ℂ * G.adjMatrix ℂ =
      (7 : ℂ) • (1 : Matrix (Fin 64) (Fin 64) ℂ) +
        (FriendshipTheoremOQ01.onesMatrix (Fin 64)).map
          (Int.castRingHom ℂ) - D.adjMatrix ℂ := by
    have h := congrArg (fun M ↦ M.map (Int.castRingHom ℂ)) hsqZ
    calc
      _ = (G.adjMatrix ℤ * G.adjMatrix ℤ).map
          (Int.castRingHom ℂ) := by
        rw [Matrix.map_mul, adjMatrix_map_intCast]
      _ = ((7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) +
          FriendshipTheoremOQ01.onesMatrix (Fin 64) -
            D.adjMatrix ℤ).map (Int.castRingHom ℂ) := h
      _ = _ := by
        ext i j
        by_cases hij : i = j <;>
          simp [SimpleGraph.adjMatrix_apply, Matrix.ofNat_apply, hij]
  have hblock := toBlock_sq_add_cross_eq_of_sq_eq
    (G.adjMatrix ℂ) (D.adjMatrix ℂ)
    ((FriendshipTheoremOQ01.onesMatrix (Fin 64)).map
      (Int.castRingHom ℂ)) (7 : ℂ) hsqC p
  have hGblock : (G.adjMatrix ℂ).toBlock p p =
      (G.induce c.supp).adjMatrix ℂ := by
    ext i j
    simp [p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  have hDblock : (D.adjMatrix ℂ).toBlock p p =
      (D.induce c.supp).adjMatrix ℂ := by
    ext i j
    simp [p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  have hJblock :
      ((FriendshipTheoremOQ01.onesMatrix (Fin 64)).map
        (Int.castRingHom ℂ)).toBlock p p =
        (FriendshipTheoremOQ01.onesMatrix c.supp).map
          (Int.castRingHom ℂ) := by
    ext i j
    simp [p, Matrix.toBlock_apply, FriendshipTheoremOQ01.onesMatrix]
  have hreverse : (G.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) p =
      Matrix.conjTranspose B := by
    simpa [B] using adjMatrix_toBlock_compl_eq_conjTranspose G p
  rw [hGblock, hDblock, hJblock, hreverse] at hblock
  exact hblock

end

end Erdos85
