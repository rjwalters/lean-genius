import Proofs.Erdos85RayleighEigenvalueLowerBound
import Proofs.Erdos85SquareEigenvalueLift
import Proofs.Erdos85SquareOrderAdjacencyMoments
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# The all-ones Rayleigh quotient of the squared adjacency matrix
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def euclideanOnes (V : Type*) [Fintype V] : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun _ : V => (1 : ℝ))

@[simp] theorem euclideanOnes_apply
    {V : Type*} [Fintype V] (x : V) :
    euclideanOnes V x = 1 := rfl

theorem norm_euclideanOnes_sq
    (V : Type*) [Fintype V] :
    ‖euclideanOnes V‖ ^ 2 = Fintype.card V := by
  calc
    ‖euclideanOnes V‖ ^ 2 =
        @inner ℝ (EuclideanSpace ℝ V) _ (euclideanOnes V) (euclideanOnes V) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∑ _x : V, (1 : ℝ) := by
      rw [PiLp.inner_apply]
      simp [euclideanOnes]
    _ = Fintype.card V := by simp

theorem adjMatrix_toEuclideanLin_euclideanOnes_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.adjMatrix ℝ).toEuclideanLin (euclideanOnes V) x =
      G.degree x := by
  change ((G.adjMatrix ℝ).mulVec (fun _ : V => 1)) x = _
  change ((G.adjMatrix ℝ).mulVec (Function.const V 1)) x = _
  rw [SimpleGraph.adjMatrix_mulVec_const_apply]
  simp

theorem inner_euclideanOnes_adjMatrix_sq_eq_sum_degree_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    @inner ℝ (EuclideanSpace ℝ V) _ (euclideanOnes V)
        (((G.adjMatrix ℝ) ^ 2).toEuclideanLin (euclideanOnes V)) =
      ∑ x : V, (G.degree x : ℝ) ^ 2 := by
  let A := G.adjMatrix ℝ
  let v := euclideanOnes V
  have hA : A.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [A, SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff (A := A)).mpr hA
  have hcomp : (A ^ 2).toEuclideanLin v =
      A.toEuclideanLin (A.toEuclideanLin v) := by
    ext i
    simp [A, v, pow_two, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_mulVec]
  change @inner ℝ (EuclideanSpace ℝ V) _ v
      ((A ^ 2).toEuclideanLin v) = _
  rw [hcomp, ← hsym v (A.toEuclideanLin v)]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [show A.toEuclideanLin v x = (G.degree x : ℝ) by
    exact adjMatrix_toEuclideanLin_euclideanOnes_apply G x]
  simp

/-- The squared adjacency operator has an eigenvalue at least the mean
squared degree. -/
theorem exists_adjMatrix_sq_eigenvalue_ge_mean_degree_sq
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ mu : ℝ,
      Module.End.HasEigenvalue
          ((G.adjMatrix ℝ) ^ 2).toEuclideanLin mu ∧
      (∑ x : V, (G.degree x : ℝ) ^ 2) / Fintype.card V ≤ mu := by
  have hA : (G.adjMatrix ℝ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hv : euclideanOnes V ≠ 0 := by
    obtain ⟨x⟩ := ‹Nonempty V›
    intro h
    have hx := congrArg (fun v : EuclideanSpace ℝ V => v x) h
    simpa using hx
  obtain ⟨mu, hmuEig, hmu⟩ :=
    exists_sq_eigenvalue_ge_rayleigh_matrix
      (G.adjMatrix ℝ) hA (euclideanOnes V) hv
  refine ⟨mu, hmuEig, ?_⟩
  rw [inner_euclideanOnes_adjMatrix_sq_eq_sum_degree_sq,
    norm_euclideanOnes_sq] at hmu
  exact hmu

/-- At order 49 and minimum degree 7, the Rayleigh eigenvalue lower bound is
exactly `(2401 + 15h) / 49`. -/
theorem exists_orderFortyNine_adjMatrix_sq_eigenvalue_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49) :
    ∃ mu : ℝ,
      Module.End.HasEigenvalue
          ((G.adjMatrix ℝ) ^ 2).toEuclideanLin mu ∧
      ((2401 : ℝ) + 15 * (squareOrderHighVertices G 7).card) / 49 ≤ mu := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨mu, hmuEig, hmu⟩ :=
    exists_adjMatrix_sq_eigenvalue_ge_mean_degree_sq G
  have hsZ := (squareOrder_sum_degree_and_sq
    G hfree (d := 7) (by norm_num) hmin hcover
      (by norm_num [hcard])).2
  have hsR : (∑ x : V, (G.degree x : ℝ) ^ 2) =
      2401 + 15 * (squareOrderHighVertices G 7).card := by
    exact_mod_cast hsZ
  refine ⟨mu, hmuEig, ?_⟩
  rw [hcard, hsR] at hmu
  norm_num at hmu ⊢
  exact hmu

/-- Lifting the squared eigenvalue gives an adjacency eigenvalue whose square
obeys the same exact lower bound. -/
theorem exists_orderFortyNine_adjMatrix_eigenvalue_sq_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49) :
    ∃ lambda : ℝ,
      Module.End.HasEigenvalue (G.adjMatrix ℝ).toEuclideanLin lambda ∧
      ((2401 : ℝ) + 15 * (squareOrderHighVertices G 7).card) / 49 ≤
        lambda ^ 2 := by
  obtain ⟨mu, hmuEig, hmuLower⟩ :=
    exists_orderFortyNine_adjMatrix_sq_eigenvalue_ge
      G hfree hmin hcover hcard
  have hmupos : 0 < mu := by
    have : (0 : ℝ) <
        ((2401 : ℝ) + 15 * (squareOrderHighVertices G 7).card) / 49 := by
      positivity
    exact this.trans_le hmuLower
  let T := (G.adjMatrix ℝ).toEuclideanLin
  have hpow : ((G.adjMatrix ℝ) ^ 2).toEuclideanLin = T ^ 2 := by
    ext v i
    simp [T, pow_two, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_mulVec]
  rw [hpow] at hmuEig
  rcases hasEigenvalue_sqrt_or_neg_sqrt_of_sq T hmuEig hmupos with hpos | hneg
  · refine ⟨Real.sqrt mu, hpos, ?_⟩
    rw [Real.sq_sqrt hmupos.le]
    exact hmuLower
  · refine ⟨-Real.sqrt mu, hneg, ?_⟩
    rw [show (-Real.sqrt mu) ^ 2 = (Real.sqrt mu) ^ 2 by ring,
      Real.sq_sqrt hmupos.le]
    exact hmuLower

end

end Erdos85
