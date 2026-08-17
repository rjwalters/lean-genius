import Proofs.Erdos85BinarySquareOwnerBottomMultiplicity
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# The exact bottom factor in an order-64 owner characteristic polynomial

The exact shifted-owner nullity supplies 48 independent `-2` eigenvectors
for every normalized size-two owner.  Geometric multiplicity is bounded by
algebraic multiplicity, so `(X+2)^48` divides its real characteristic
polynomial.  Removing that monic factor leaves a monic residual polynomial
of degree exactly 16, the finite ledger consumed by the q=8 spectral route.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

/-- A `k`-dimensional kernel of `A+aI` supplies the corresponding `k`-fold
linear characteristic factor. -/
theorem pow_X_add_C_dvd_charpoly_of_finrank_shift_kernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (a : ℝ) (k : ℕ)
    (hker : Module.finrank ℝ
      (LinearMap.ker (A + a • (1 : Matrix V V ℝ)).mulVecLin) = k) :
    (X + C a) ^ k ∣ A.charpoly := by
  let T : Module.End ℝ (V → ℝ) := A.toLin'
  have heig : T.eigenspace (-a) =
      LinearMap.ker (A + a • (1 : Matrix V V ℝ)).mulVecLin := by
    rw [Module.End.eigenspace_def]
    congr 1
    ext v x
    simp [T]
  have hgeom : k ≤ T.charpoly.rootMultiplicity (-a) := by
    rw [← hker, ← heig]
    exact LinearMap.finrank_eigenspace_le T (-a)
  have hpow : (X - C (-a)) ^ k ∣
      (X - C (-a)) ^ T.charpoly.rootMultiplicity (-a) :=
    pow_dvd_pow _ hgeom
  have hroot : (X - C (-a)) ^ T.charpoly.rootMultiplicity (-a) ∣
      T.charpoly := T.charpoly.pow_rootMultiplicity_dvd (-a)
  have hdvd : (X - C (-a)) ^ k ∣ T.charpoly := hpow.trans hroot
  rw [Matrix.charpoly_toLin'] at hdvd
  simpa only [map_neg, sub_neg_eq_add] using hdvd

/-- Every order-64 normalized size-two owner has the 48-fold bottom factor
`(X+2)^48`. -/
theorem orderSixtyFour_sizeSixteen_componentOwnerGraph_bottom_charpoly_factor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    (X + C (2 : ℝ)) ^ 48 ∣
      ((componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℝ).charpoly := by
  apply pow_X_add_C_dvd_charpoly_of_finrank_shift_kernel
  exact orderSixtyFour_sizeSixteen_componentOwnerGraph_bottom_multiplicity
    G hfree hreg hcard c hc

/-- Removing the forced bottom factor leaves a monic degree-16 residual
polynomial. -/
theorem orderSixtyFour_sizeSixteen_componentOwnerGraph_exists_residual_charpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    ∃ r : ℝ[X], r.Monic ∧ r.natDegree = 16 ∧
      ((componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℝ).charpoly =
        (X + C (2 : ℝ)) ^ 48 * r := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  have hdvd :=
    orderSixtyFour_sizeSixteen_componentOwnerGraph_bottom_charpoly_factor
      G hfree hreg hcard c hc
  obtain ⟨r, hr⟩ := hdvd
  have hfactorMonic : ((X + C (2 : ℝ)) ^ 48).Monic :=
    (monic_X_add_C 2).pow 48
  have hcharMonic : (O.adjMatrix ℝ).charpoly.Monic :=
    Matrix.charpoly_monic _
  have hrMonic : r.Monic := by
    apply hfactorMonic.of_mul_monic_left
    rw [← hr]
    exact hcharMonic
  have hcharDegree : (O.adjMatrix ℝ).charpoly.natDegree = 64 := by
    rw [← Matrix.charpoly_toLin', LinearMap.charpoly_natDegree,
      Module.finrank_fintype_fun_eq_card ℝ, hcard]
  have hfactorDegree : ((X + C (2 : ℝ)) ^ 48).natDegree = 48 := by
    rw [natDegree_pow, natDegree_X_add_C]
  have hrDegree : r.natDegree = 16 := by
    have hdegree := congrArg Polynomial.natDegree hr
    rw [hcharDegree, natDegree_mul hfactorMonic.ne_zero hrMonic.ne_zero,
      hfactorDegree] at hdegree
    omega
  exact ⟨r, hrMonic, hrDegree, hr⟩

end

end Erdos85
