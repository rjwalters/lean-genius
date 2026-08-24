import Proofs.Erdos85ExcessDefectRegular

/-!
# Exact cut energy of an incidence-bottleneck row

For a square-order incidence matrix satisfying `A² = L_D + J`, the error
of a `q`-set `S`, namely `A 1_S - 1`, has squared norm equal to the defect
cut of `S`.  The closed defect neighborhood is the intended consumer.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

private def finsetIndicator
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) : V → ℤ :=
  fun v => if v ∈ S then 1 else 0

private def intOnesMatrix (V : Type*) : Matrix V V ℤ := fun _ _ => 1

/-- Ordered incidences of graph edges leaving a finite vertex set. -/
def finsetGraphCutIncidenceCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) : ℕ :=
  ∑ x ∈ S, (D.neighborFinset x \ S).card

private theorem sum_finsetIndicator
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    ∑ v, finsetIndicator S v = (S.card : ℤ) := by
  simp [finsetIndicator]

private theorem vecMul_eq_mulVec_of_transpose_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℤ) (hA : A.transpose = A) (v : V → ℤ) :
    Matrix.vecMul v A = A.mulVec v := by
  funext i
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _hj
  have hij := congrFun (congrFun hA i) j
  simp only [Matrix.transpose_apply] at hij
  rw [← hij]
  ring

/-- Algebraic energy identity: if a symmetric integral matrix is
`q`-regular and its square is the defect Laplacian plus the all-ones matrix,
then the incidence error of any `q`-set has Laplacian energy. -/
theorem incidenceError_sum_sq_eq_lapMatrix_quadratic
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (A : Matrix V V ℤ) (q : ℕ)
    (hcard : Fintype.card V = q * q)
    (hA : A.transpose = A)
    (hreg : A.mulVec (1 : V → ℤ) = (q : ℤ) • (1 : V → ℤ))
    (hsq : A * A = D.lapMatrix ℤ + intOnesMatrix V)
    (S : Finset V) (hScard : S.card = q) :
    ∑ y : V, (A.mulVec (finsetIndicator S) y - 1) ^ 2 =
      finsetIndicator S ⬝ᵥ (D.lapMatrix ℤ).mulVec (finsetIndicator S) := by
  let s := finsetIndicator S
  let v := A.mulVec s
  have hvv : v ⬝ᵥ v = s ⬝ᵥ (A * A).mulVec s := by
    calc
      v ⬝ᵥ v = Matrix.vecMul v A ⬝ᵥ s := by
        simpa [v] using (Matrix.dotProduct_mulVec v A s)
      _ = A.mulVec v ⬝ᵥ s := by rw [vecMul_eq_mulVec_of_transpose_eq A hA v]
      _ = s ⬝ᵥ A.mulVec v := dotProduct_comm _ _
      _ = s ⬝ᵥ (A * A).mulVec s := by
        rw [Matrix.mulVec_mulVec]
  have hsumv : ∑ y : V, v y = (q : ℤ) * q := by
    calc
      (∑ y : V, v y) = (1 : V → ℤ) ⬝ᵥ A.mulVec s := by
        simp [v, dotProduct]
      _ = Matrix.vecMul (1 : V → ℤ) A ⬝ᵥ s :=
        Matrix.dotProduct_mulVec (1 : V → ℤ) A s
      _ = A.mulVec (1 : V → ℤ) ⬝ᵥ s := by
        rw [vecMul_eq_mulVec_of_transpose_eq A hA]
      _ = ((q : ℤ) • (1 : V → ℤ)) ⬝ᵥ s := by rw [hreg]
      _ = (q : ℤ) * q := by
        simp only [dotProduct, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
          mul_one]
        rw [← Finset.mul_sum, show (∑ x : V, s x) = (S.card : ℤ) by
          simpa [s] using sum_finsetIndicator S, hScard]
  have hJs : (intOnesMatrix V).mulVec s =
      (q : ℤ) • (1 : V → ℤ) := by
    funext y
    simp only [intOnesMatrix, Matrix.mulVec, dotProduct, mul_one,
      Pi.smul_apply, Pi.one_apply, smul_eq_mul]
    simp only [one_mul]
    rw [show (∑ x : V, s x) = (S.card : ℤ) by
      simpa [s] using sum_finsetIndicator S, hScard]
  calc
    (∑ y : V, (A.mulVec s y - 1) ^ 2) =
        v ⬝ᵥ v - 2 * (∑ y : V, v y) + Fintype.card V := by
      change (∑ y : V, (v y - 1) ^ 2) = _
      calc
        (∑ y : V, (v y - 1) ^ 2) =
            (∑ y : V, (v y) ^ 2) - (∑ y : V, 2 * v y) +
              ∑ _y : V, (1 : ℤ) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro y _hy
          ring
        _ = v ⬝ᵥ v - 2 * (∑ y : V, v y) + Fintype.card V := by
          simp only [dotProduct, pow_two]
          rw [← Finset.mul_sum]
          simp
    _ = s ⬝ᵥ (A * A).mulVec s - 2 * ((q : ℤ) * q) +
        (q : ℤ) * q := by
      rw [hvv, hsumv, hcard]
      push_cast
      rfl
    _ = s ⬝ᵥ ((D.lapMatrix ℤ + intOnesMatrix V).mulVec s) -
        2 * ((q : ℤ) * q) + (q : ℤ) * q := by rw [hsq]
    _ = s ⬝ᵥ (D.lapMatrix ℤ).mulVec s := by
      rw [Matrix.add_mulVec, hJs]
      simp only [dotProduct, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
        smul_eq_mul, mul_one]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hsqsum : (∑ x : V, s x * (q : ℤ)) = (q : ℤ) * q := by
        rw [show (∑ x : V, s x * (q : ℤ)) =
            (q : ℤ) * ∑ x : V, s x by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring,
          show (∑ x : V, s x) = (S.card : ℤ) by
            simpa [s] using sum_finsetIndicator S,
          hScard]
      rw [hsqsum]
      ring

/-- The Laplacian quadratic form of a set indicator is its ordered cut
incidence count. -/
theorem finsetIndicator_dot_lapMatrix_eq_finsetCutIncidenceCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) :
    finsetIndicator S ⬝ᵥ (D.lapMatrix ℤ).mulVec (finsetIndicator S) =
      (finsetGraphCutIncidenceCount D S : ℤ) := by
  have hpoint : ∀ x : V,
      finsetIndicator S x * (D.lapMatrix ℤ).mulVec
          (finsetIndicator S) x =
        if x ∈ S then ((D.neighborFinset x \ S).card : ℤ) else 0 := by
    intro x
    by_cases hx : x ∈ S
    · have hpartition := Finset.card_inter_add_card_sdiff
          (D.neighborFinset x) S
      have hdegree := D.card_neighborFinset_eq_degree x
      have hpartition' : (D.degree x : ℤ) =
          ((D.neighborFinset x ∩ S).card : ℤ) +
            ((D.neighborFinset x \ S).card : ℤ) := by
        exact_mod_cast (hpartition.trans hdegree).symm
      have hinter : ((S.filter fun y => D.Adj x y).card : ℤ) =
          ((D.neighborFinset x ∩ S).card : ℤ) := by
        have hfin : S.filter (fun y => D.Adj x y) =
            D.neighborFinset x ∩ S := by
          ext y
          simp [SimpleGraph.mem_neighborFinset, and_comm]
        exact_mod_cast congrArg Finset.card hfin
      rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec]
      simp only [Pi.sub_apply]
      simp [finsetIndicator, hx, SimpleGraph.degMatrix, Matrix.mulVec,
        dotProduct, Matrix.diagonal_apply,
        SimpleGraph.adjMatrix_mulVec_apply]
      rw [hinter]
      omega
    · rw [if_neg hx]
      simp [finsetIndicator, hx]
  calc
    finsetIndicator S ⬝ᵥ (D.lapMatrix ℤ).mulVec (finsetIndicator S) =
        ∑ x : V, if x ∈ S then
          ((D.neighborFinset x \ S).card : ℤ) else 0 := by
      simp only [dotProduct]
      apply Finset.sum_congr rfl
      intro x _hx
      exact hpoint x
    _ = ∑ x ∈ S, ((D.neighborFinset x \ S).card : ℤ) := by simp
    _ = (finsetGraphCutIncidenceCount D S : ℤ) := by
      rw [finsetGraphCutIncidenceCount]
      push_cast
      rfl

/-- Exact graph-facing form: the squared incidence error of a `q`-set is
the size of its defect cut. -/
theorem incidenceError_sum_sq_eq_finsetCutIncidenceCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (A : Matrix V V ℤ) (q : ℕ)
    (hcard : Fintype.card V = q * q)
    (hA : A.transpose = A)
    (hreg : A.mulVec (1 : V → ℤ) = (q : ℤ) • (1 : V → ℤ))
    (hsq : A * A = D.lapMatrix ℤ + intOnesMatrix V)
    (S : Finset V) (hScard : S.card = q) :
    ∑ y : V, (A.mulVec (finsetIndicator S) y - 1) ^ 2 =
      (finsetGraphCutIncidenceCount D S : ℤ) := by
  rw [incidenceError_sum_sq_eq_lapMatrix_quadratic
    D A q hcard hA hreg hsq S hScard]
  exact finsetIndicator_dot_lapMatrix_eq_finsetCutIncidenceCount D S

/-- Square-order graph wrapper for an arbitrary `q`-set.  The explicit
defect-regularity hypothesis is the exact structural input used by the
connected branch. -/
theorem binarySquare_regular_incidenceError_sum_sq_eq_finsetCut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 1 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (S : Finset V) (hScard : S.card = q) :
    ∑ y : V,
        ((G.adjMatrix ℤ).mulVec (finsetIndicator S) y - 1) ^ 2 =
      (finsetGraphCutIncidenceCount (secondOrderDefectGraph G) S : ℤ) := by
  let A := G.adjMatrix ℤ
  let D := secondOrderDefectGraph G
  have hA : A.transpose = A := by
    ext i j
    simp [A, SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hregVec : A.mulVec (1 : V → ℤ) =
      (q : ℤ) • (1 : V → ℤ) := by
    funext i
    simp [A, SimpleGraph.adjMatrix_mulVec_apply, hreg i]
  have hsq0 :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hsq : A * A = D.lapMatrix ℤ + intOnesMatrix V := by
    rw [hsq0]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        intOnesMatrix, FriendshipTheoremOQ01.onesMatrix,
        hDreg, SimpleGraph.adjMatrix_apply, Matrix.smul_apply,
        Matrix.one_apply, Matrix.natCast_apply, Matrix.intCast_apply,
        smul_eq_mul]
      omega
    · simp [D, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        intOnesMatrix, FriendshipTheoremOQ01.onesMatrix,
        hij, SimpleGraph.adjMatrix_apply, Matrix.smul_apply,
        Matrix.one_apply, Matrix.natCast_apply, Matrix.intCast_apply,
        smul_eq_mul]
      ring
  exact incidenceError_sum_sq_eq_finsetCutIncidenceCount
    D A q hcard hA hregVec hsq S hScard

/-- Closed-neighborhood form used by the incidence bottleneck: its exact
row energy is the defect cut leaving that closed neighborhood. -/
theorem binarySquare_regular_closedDefectNeighborhood_incidenceError_energy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 1 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (x : V) :
    let S := insert x ((secondOrderDefectGraph G).neighborFinset x)
    ∑ y : V,
        ((G.adjMatrix ℤ).mulVec (finsetIndicator S) y - 1) ^ 2 =
      (finsetGraphCutIncidenceCount (secondOrderDefectGraph G) S : ℤ) := by
  dsimp only
  apply binarySquare_regular_incidenceError_sum_sq_eq_finsetCut
    G hfree hq hreg hcard hDreg
  simp [hDreg x]
  omega

end


end Erdos85

#print axioms Erdos85.incidenceError_sum_sq_eq_lapMatrix_quadratic
#print axioms Erdos85.finsetIndicator_dot_lapMatrix_eq_finsetCutIncidenceCount
#print axioms Erdos85.incidenceError_sum_sq_eq_finsetCutIncidenceCount
#print axioms Erdos85.binarySquare_regular_incidenceError_sum_sq_eq_finsetCut
#print axioms
  Erdos85.binarySquare_regular_closedDefectNeighborhood_incidenceError_energy
