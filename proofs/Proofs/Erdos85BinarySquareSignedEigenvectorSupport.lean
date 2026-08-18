import Proofs.Erdos85BinarySquareAdjacencySquareAction
import Proofs.Erdos85ThreeLevelSupportBalance

/-! # Support forced by a signed defect eigenvector

For a signed vector supported on a normalized size-two defect component, the
global square identity determines the exact number of outside vertices on
which its adjacency image is nonzero.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Summing adjacency against a vector on a regular graph multiplies its
coordinate sum by the degree. -/
theorem sum_adjMatrix_mulVec_of_regular_int
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ)
    (hreg : ∀ x, G.degree x = q) (v : V → ℤ) :
    ∑ x, (G.adjMatrix ℤ).mulVec v x = (q : ℤ) * ∑ x, v x := by
  let one : V → ℤ := fun _ => 1
  have hOne : (G.adjMatrix ℤ).mulVec one = fun _ => (q : ℤ) := by
    funext x
    change (G.adjMatrix ℤ).mulVec (Function.const V 1) x = (q : ℤ)
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, hreg x]
    simp
  have hdot : one ⬝ᵥ ((G.adjMatrix ℤ).mulVec v) =
      ((G.adjMatrix ℤ).mulVec one) ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec]
    have hsymm : (G.adjMatrix ℤ).transpose = G.adjMatrix ℤ :=
      G.isSymm_adjMatrix.eq
    rw [← hsymm, Matrix.vecMul_transpose, hsymm]
  calc
    ∑ x, (G.adjMatrix ℤ).mulVec v x =
        one ⬝ᵥ ((G.adjMatrix ℤ).mulVec v) := by simp [dotProduct, one]
    _ = ((G.adjMatrix ℤ).mulVec one) ⬝ᵥ v := hdot
    _ = (q : ℤ) * ∑ x, v x := by
      rw [hOne]
      simp [dotProduct, Finset.mul_sum]

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

/-- The outside support is signed-balanced.  In particular its positive and
negative halves have equal size, and their common size satisfies the exact
division-free energy equation `4 |S₊| = q(q-5-μ)`. -/
theorem binarySquare_regular_signedEigenvector_outsideSupport_balance
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
    (Finset.univ.filter fun x => x ∉ c.supp ∧
        (G.adjMatrix ℤ).mulVec s x = 2).card =
      (Finset.univ.filter fun x => x ∉ c.supp ∧
        (G.adjMatrix ℤ).mulVec s x = -2).card ∧
    4 * ((Finset.univ.filter fun x => x ∉ c.supp ∧
        (G.adjMatrix ℤ).mulVec s x = 2).card : ℤ) =
      (q : ℤ) * ((q : ℤ) - 5 - mu) := by
  let a : V → ℤ := (G.adjMatrix ℤ).mulVec s
  let Sout := Finset.univ.filter fun x => x ∉ c.supp
  have htotalA : ∑ x, a x = 0 := by
    change ∑ x, (G.adjMatrix ℤ).mulVec s x = 0
    rw [sum_adjMatrix_mulVec_of_regular_int G q hreg s, hsum, mul_zero]
  have hinsideS : ∑ x ∈ Finset.univ.filter (fun x => x ∈ c.supp), s x = 0 := by
    have hout : ∑ x ∈ Finset.univ.filter (fun x => x ∉ c.supp), s x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hs_out x (Finset.mem_filter.mp hx).2
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => x ∈ c.supp) s
    rw [hout, add_zero, hsum] at hsplit
    exact hsplit
  have hinsideA : ∑ x ∈ Finset.univ.filter (fun x => x ∈ c.supp), a x = 0 := by
    calc
      ∑ x ∈ Finset.univ.filter (fun x => x ∈ c.supp), a x =
          ∑ x ∈ Finset.univ.filter (fun x => x ∈ c.supp), (-2 : ℤ) * s x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hA_in x (Finset.mem_filter.mp hx).2
      _ = (-2 : ℤ) * ∑ x ∈ Finset.univ.filter (fun x => x ∈ c.supp), s x := by
        rw [Finset.mul_sum]
      _ = 0 := by rw [hinsideS, mul_zero]
  have houtA : ∑ x ∈ Sout, a x = 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => x ∈ c.supp) a
    change (∑ x ∈ Finset.univ.filter (fun x => x ∈ c.supp), a x) +
      ∑ x ∈ Sout, a x = ∑ x, a x at hsplit
    rw [hinsideA, zero_add, htotalA] at hsplit
    exact hsplit
  have hlevels : ∀ x ∈ Sout, a x = -2 ∨ a x = 0 ∨ a x = 2 := by
    intro x hx
    exact hA_out x (Finset.mem_filter.mp hx).2
  obtain ⟨hbalance, hsupport⟩ :=
    threeLevel_zeroSum_support_balance Sout a hlevels houtA
  have hmass := binarySquare_regular_signedEigenvector_outsideSupport
    G hfree hreg c hc s mu hs_in hs_out hsum hDs hA_in hA_out
  have hP : (Sout.filter fun x => a x = 2) =
      Finset.univ.filter (fun x => x ∉ c.supp ∧ a x = 2) := by
    simp [Sout, Finset.filter_filter]
  have hN : (Sout.filter fun x => a x = -2) =
      Finset.univ.filter (fun x => x ∉ c.supp ∧ a x = -2) := by
    simp [Sout, Finset.filter_filter]
  have hSupp : (Sout.filter fun x => a x ≠ 0) =
      Finset.univ.filter (fun x => x ∉ c.supp ∧ a x ≠ 0) := by
    simp [Sout, Finset.filter_filter]
  change _ = _ ∧ 4 * (_ : ℤ) = _
  rw [← hP, ← hN]
  refine ⟨hbalance, ?_⟩
  change 2 * ((Finset.univ.filter fun x => x ∉ c.supp ∧ a x ≠ 0).card : ℤ) = _ at hmass
  rw [← hSupp] at hmass
  rw [hsupport] at hmass
  push_cast at hmass
  nlinarith

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_signedEigenvector_outsideSupport
#print axioms Erdos85.sum_adjMatrix_mulVec_of_regular_int
#print axioms Erdos85.binarySquare_regular_signedEigenvector_outsideSupport_balance
