import Proofs.Erdos85PureEndpointExteriorBlockDesign

/-!
# A binary dependence among the exterior rows

At the pure endpoint there are more exterior rows than shore points.  Over
`ZMod 2`, the transpose incidence map therefore has a nonzero kernel.  This
produces a nonempty binary row dependency in which every shore point has
even weighted incidence.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- A matrix with more columns than rows has a nonzero vector in its kernel,
over any finite-dimensional field. -/
theorem exists_ne_zero_mulVec_eq_zero_of_card_lt
    {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix β α K) (hcard : Fintype.card β < Fintype.card α) :
    ∃ x : α → K, x ≠ 0 ∧ M.mulVec x = 0 := by
  classical
  have hnot : ¬ Function.Injective M.mulVecLin := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at hle
    omega
  obtain ⟨x, y, heq, hxy⟩ := Function.not_injective_iff.mp hnot
  refine ⟨x - y, sub_ne_zero.mpr hxy, ?_⟩
  change M.mulVecLin (x - y) = 0
  rw [map_sub, heq, sub_self]

/-- The pure endpoint exterior-row incidence matrix over `ZMod 2` has a
nontrivial kernel: some nonzero row weighting has zero incidence sum at
every shore point. -/
theorem c4Free_binarySquare_pureEndpoint_exterior_incidenceKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (_hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (_hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (_hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (_htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    ∃ x : W → ZMod 2, x ≠ 0 ∧
      ∀ y : P, ∑ w : W, (if G.Adj w.1 y.1 then x w else 0) = 0 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  have hFcard : F.card = q := by simpa [F] using hCcard
  have hWcard : Fintype.card W = q * q - q := by
    rw [show Fintype.card W = Fᶜ.card by exact Fintype.card_coe Fᶜ,
      Finset.card_compl, hFcard, hcard]
  have hPcard : Fintype.card P = S.card := by simp [P]
  have hPW : Fintype.card P < Fintype.card W := by
    rw [hPcard, hWcard]
    have hpoly : 3 * q < q * q := by nlinarith
    omega
  let M : Matrix P W (ZMod 2) := fun y w =>
    if G.Adj w.1 y.1 then 1 else 0
  obtain ⟨x, hx, hMx⟩ :=
    exists_ne_zero_mulVec_eq_zero_of_card_lt M hPW
  refine ⟨x, hx, ?_⟩
  intro y
  change (∑ w : W, (if G.Adj w.1 y.1 then x w else 0)) = 0
  have hy : M.mulVec x y = 0 := congrFun hMx y
  simpa only [M, Matrix.mulVec, dotProduct, ite_mul, one_mul, zero_mul] using hy

end

end Erdos85

#print axioms Erdos85.exists_ne_zero_mulVec_eq_zero_of_card_lt
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exterior_incidenceKernel
