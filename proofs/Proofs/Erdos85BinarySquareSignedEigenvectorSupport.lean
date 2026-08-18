import Proofs.Erdos85BinarySquareAdjacencySquareAction

/-! # Support forced by a signed defect eigenvector

For a signed vector supported on a normalized size-two defect component, the
global square identity determines the exact number of outside vertices on
which its adjacency image is nonzero.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Energy identity for a signed size-two defect eigenvector whose internal
adjacency action is `-2`.  The division-free conclusion is
`2 |support outside| = q(q-5-μ)`. -/
theorem binarySquare_regular_signedEigenvector_outsideSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (s : V → ℤ) (mu : ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = mu * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2) :
    2 * ((Finset.univ.filter fun x =>
      x ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s x ≠ 0).card : ℤ) =
      (q : ℤ) * ((q : ℤ) - 5 - mu) := by
  let A := G.adjMatrix ℤ
  let a : V → ℤ := A.mulVec s
  have hA2 : ∀ x, (A.mulVec a) x = ((q : ℤ) - 1 - mu) * s x := by
    intro x
    change (A.mulVec (A.mulVec s)) x = _
    rw [Matrix.mulVec_mulVec s A A]
    change (((G.adjMatrix ℤ) * (G.adjMatrix ℤ)).mulVec s) x = _
    rw [binarySquare_regular_adjMatrix_sq_mulVec_apply G hfree hreg s x,
      hsum, hDs x]
    ring
  have hsymm : A.transpose = A := G.isSymm_adjMatrix.eq
  have henergyDot : a ⬝ᵥ a = s ⬝ᵥ A.mulVec a := by
    calc
      a ⬝ᵥ a = (a ᵥ* A) ⬝ᵥ s := by
        change a ⬝ᵥ A.mulVec s = _
        rw [Matrix.dotProduct_mulVec]
      _ = A.mulVec a ⬝ᵥ s := by
        rw [← Matrix.vecMul_transpose, hsymm]
      _ = s ⬝ᵥ A.mulVec a := dotProduct_comm _ _
  have hcomponentCard :
      (Finset.univ.filter fun x => x ∈ c.supp).card = c.supp.ncard := by
    have heq : (Finset.univ.filter fun x => x ∈ c.supp) =
        c.supp.toFinite.toFinset := by
      ext x
      simp
    rw [heq, Set.ncard_eq_toFinset_card]
  have hs_sq : ∑ x, (s x) ^ 2 = 2 * (q : ℤ) := by
    calc
      ∑ x, (s x) ^ 2 =
          ∑ x ∈ Finset.univ.filter (fun x => x ∈ c.supp), (1 : ℤ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ c.supp
        · rcases hs_in x hx with hs | hs <;> simp [hx, hs]
        · simp [hx, hs_out x hx]
      _ = ((Finset.univ.filter fun x => x ∈ c.supp).card : ℤ) := by simp
      _ = (c.supp.ncard : ℤ) := by rw [hcomponentCard]
      _ = 2 * (q : ℤ) := by rw [hc]; push_cast; ring
  have henergy : ∑ x, (a x) ^ 2 =
      ((q : ℤ) - 1 - mu) * (2 * (q : ℤ)) := by
    calc
      ∑ x, (a x) ^ 2 = a ⬝ᵥ a := by simp [dotProduct, pow_two]
      _ = s ⬝ᵥ A.mulVec a := henergyDot
      _ = ∑ x, s x * (((q : ℤ) - 1 - mu) * s x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hA2 x]
      _ = ((q : ℤ) - 1 - mu) * ∑ x, (s x) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = ((q : ℤ) - 1 - mu) * (2 * (q : ℤ)) := by rw [hs_sq]
  have hsplit : ∑ x, (a x) ^ 2 =
      8 * (q : ℤ) +
      4 * ((Finset.univ.filter fun x => x ∉ c.supp ∧ a x ≠ 0).card : ℤ) := by
    calc
      ∑ x, (a x) ^ 2 =
          ∑ x, (if x ∈ c.supp then (4 : ℤ)
            else if a x ≠ 0 then 4 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ c.supp
        · have ha := hA_in x hx
          change a x = -2 * s x at ha
          rcases hs_in x hx with hs | hs <;> rw [ha, hs] <;> norm_num
        · have ha := hA_out x hx
          change a x = -2 ∨ a x = 0 ∨ a x = 2 at ha
          rcases ha with ha | ha | ha <;> simp [hx, ha]
      _ = 4 * ((Finset.univ.filter fun x => x ∈ c.supp).card : ℤ) +
          4 * ((Finset.univ.filter fun x => x ∉ c.supp ∧ a x ≠ 0).card : ℤ) := by
        simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
          nsmul_eq_mul, Finset.filter_filter]
        ring
      _ = 8 * (q : ℤ) +
          4 * ((Finset.univ.filter fun x => x ∉ c.supp ∧ a x ≠ 0).card : ℤ) := by
        have hcardc : ((Finset.univ.filter fun x => x ∈ c.supp).card : ℤ) =
            2 * (q : ℤ) := by
          calc
            ((Finset.univ.filter fun x => x ∈ c.supp).card : ℤ) =
                (c.supp.ncard : ℤ) := by rw [hcomponentCard]
            _ = 2 * (q : ℤ) := by rw [hc]; push_cast; ring
        rw [hcardc]
        ring
  change 2 * ((Finset.univ.filter fun x => x ∉ c.supp ∧ a x ≠ 0).card : ℤ) = _
  rw [hsplit] at henergy
  nlinarith

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_signedEigenvector_outsideSupport
