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

/-- Combinatorial form of the binary kernel: there is a nonempty collection
of exterior rows in which every shore point has even incidence. -/
theorem c4Free_binarySquare_pureEndpoint_exists_even_exteriorRowConfiguration
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    ∃ T : Finset W, T.Nonempty ∧
      ∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  change ∃ T : Finset W, T.Nonempty ∧
    ∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)
  obtain ⟨x, hx, hzero⟩ :=
    c4Free_binarySquare_pureEndpoint_exterior_incidenceKernel
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  let T := (Finset.univ : Finset W).filter fun w => x w = 1
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hval : ∀ w : W, x w = if w ∈ T then 1 else 0 := by
    intro w
    rcases hbinary (x w) with hw0 | hw1
    · simp [T, hw0]
    · simp [T, hw1]
  have hT : T.Nonempty := by
    by_contra hTempty
    apply hx
    funext w
    have hwNot : w ∉ T := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hTempty]
    simp [hval w, hwNot]
  refine ⟨T, hT, ?_⟩
  intro y
  have hy := hzero y
  simp_rw [hval] at hy
  have hcast :
      (((T.filter fun w => G.Adj w.1 y.1).card : ℕ) : ZMod 2) = 0 := by
    have hy' : (∑ w : W,
        if w ∈ T then
          (if G.Adj w.1 y.1 then (1 : ZMod 2) else 0) else 0) = 0 := by
      calc
        (∑ w : W,
            if w ∈ T then
              (if G.Adj w.1 y.1 then (1 : ZMod 2) else 0) else 0) =
            ∑ w : W,
              if G.Adj w.1 y.1 then
                (if w ∈ T then (1 : ZMod 2) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro w _hw
          by_cases hwT : w ∈ T <;>
            by_cases hwy : G.Adj w.1 y.1 <;> simp [hwT, hwy]
        _ = 0 := hy
    calc
      (((T.filter fun w => G.Adj w.1 y.1).card : ℕ) : ZMod 2) =
          ∑ w ∈ (T.filter fun w => G.Adj w.1 y.1), (1 : ZMod 2) := by
        simp
      _ = ∑ w ∈ T,
          if G.Adj w.1 y.1 then (1 : ZMod 2) else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ w : W,
          if w ∈ T then
            (if G.Adj w.1 y.1 then (1 : ZMod 2) else 0) else 0 := by
        calc
          (∑ w ∈ T, if G.Adj w.1 y.1 then (1 : ZMod 2) else 0) =
              ∑ w ∈ T, if w ∈ T then
                (if G.Adj w.1 y.1 then (1 : ZMod 2) else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro w hwT
            simp [hwT]
          _ = ∑ w ∈ (Finset.univ : Finset W), if w ∈ T then
                (if G.Adj w.1 y.1 then (1 : ZMod 2) else 0) else 0 := by
            apply Finset.sum_subset (Finset.subset_univ T)
            intro w _hwUniv hwT
            simp [hwT]
          _ = _ := by rfl
      _ = 0 := hy'
  exact ZMod.natCast_eq_zero_iff_even.mp hcast

end

end Erdos85

#print axioms Erdos85.exists_ne_zero_mulVec_eq_zero_of_card_lt
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exterior_incidenceKernel
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_even_exteriorRowConfiguration
