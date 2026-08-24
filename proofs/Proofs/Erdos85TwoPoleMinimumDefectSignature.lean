import Proofs.Erdos85TwoPoleMinimumPoleLineSingleton
import Proofs.Erdos85TwoPoleExceptionalLineCorrection

/-!
# Defect signature of a minimum two-pole potential

This proves `(73rnz_bp)`.  The all-ones term in the mod-two defect equation
vanishes because the minimum support has even cardinality, leaving the exact
boundary identity `Dx = A(e₁+e₂)+x`.
-/

open SimpleGraph

namespace Erdos85

/-- The all-ones matrix reads the cardinality of the support of an F₂
vector. -/
theorem onesMatrix_mulVec_eq_f2PotentialSupport_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → ZMod 2) :
    (Matrix.of (fun _ _ => (1 : ZMod 2)) : Matrix V V (ZMod 2)).mulVec x =
      fun _ => ((f2PotentialSupport x).card : ZMod 2) := by
  classical
  funext center
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul]
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  calc
    (∑ j, x j) = ∑ j, if x j = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rcases hz (x j) with hj | hj <;> simp [hj]
    _ = ((f2PotentialSupport x).card : ZMod 2) := by
      simp [f2PotentialSupport]

/-- An even support is killed by the all-ones matrix over F₂. -/
theorem onesMatrix_mulVec_eq_zero_of_f2PotentialSupport_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → ZMod 2) (heven : Even (f2PotentialSupport x).card) :
    (Matrix.of (fun _ _ => (1 : ZMod 2)) : Matrix V V (ZMod 2)).mulVec x =
      0 := by
  rw [onesMatrix_mulVec_eq_f2PotentialSupport_card]
  funext center
  simp only [Pi.zero_apply]
  exact ZMod.natCast_eq_zero_iff_even.mpr heven

/-- **Minimum two-pole defect signature (`73rnz_bp`).** -/
theorem secondOrderDefect_mulVec_minimum_twoPolePotential
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (antipodalGraph A).Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A)
    {q : ℕ} (hq : Even q) (hreg : ∀ u, A.degree u = q)
    (x : V → ZMod 2) (pole₁ pole₂ : V)
    (hAx : (A.adjMatrix (ZMod 2)).mulVec x =
      Pi.single pole₁ 1 + Pi.single pole₂ 1)
    (hcard : (f2PotentialSupport x).card = q) :
    ((secondOrderDefectGraph A).adjMatrix (ZMod 2)).mulVec x =
      (A.adjMatrix (ZMod 2)).mulVec
          (Pi.single pole₁ 1 + Pi.single pole₂ 1) + x := by
  let M := A.adjMatrix (ZMod 2)
  let D := (secondOrderDefectGraph A).adjMatrix (ZMod 2)
  let J : Matrix V V (ZMod 2) := Matrix.of fun _ _ => 1
  let h : V → ZMod 2 := Pi.single pole₁ 1 + Pi.single pole₂ 1
  have hsupportEven : Even (f2PotentialSupport x).card := by
    rw [hcard]
    exact hq
  have hJx : J.mulVec x = 0 := by
    exact onesMatrix_mulVec_eq_zero_of_f2PotentialSupport_even x hsupportEven
  have hsq := adjMatrix_sq_eq_defect_mod_two_of_even_regular
    A hfree hq hreg
  have hA2x : (M * M).mulVec x = M.mulVec h := by
    rw [← Matrix.mulVec_mulVec, hAx]
  have heq : M.mulVec h = x + D.mulVec x := by
    rw [← hA2x]
    change M * M = 1 + J + D at hsq
    rw [hsq, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      hJx, add_zero]
  change D.mulVec x = M.mulVec h + x
  funext v
  have hv := congrFun heq v
  simp only [Pi.add_apply] at hv ⊢
  calc
    D.mulVec x v = D.mulVec x v + 0 := by rw [add_zero]
    _ = D.mulVec x v + (x v + x v) := by rw [zmodTwo_add_self]
    _ = (x v + D.mulVec x v) + x v := by ac_rfl
    _ = M.mulVec h v + x v := by rw [hv]

end Erdos85

#print axioms Erdos85.onesMatrix_mulVec_eq_f2PotentialSupport_card
#print axioms Erdos85.onesMatrix_mulVec_eq_zero_of_f2PotentialSupport_even
#print axioms Erdos85.secondOrderDefect_mulVec_minimum_twoPolePotential
