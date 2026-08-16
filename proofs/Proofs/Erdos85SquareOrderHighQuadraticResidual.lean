import Proofs.Erdos85SquareOrderHighQuadraticCharpoly

/-!
# Residual characteristic polynomial after the high quadratic sector

The certified factor has degree twice the number of non-base high vertices.
Cancelling it from the monic adjacency characteristic polynomial leaves a
monic residual of exact degree d squared minus twice h minus one.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem exists_monic_squareOrder_residualCharpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    ∃ Q : Polynomial ℚ,
      Q.Monic ∧
      LinearMap.charpoly (G.adjMatrix ℚ).toLin' =
        (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)) ^
          ((squareOrderHighVertices G d).card - 1) * Q ∧
      Q.natDegree =
        d * d - 2 * ((squareOrderHighVertices G d).card - 1) := by
  obtain ⟨Q, hQ⟩ := exists_squareOrder_residualCharpoly
    G hfree hd hmin hcover hcard ha
  let k := (squareOrderHighVertices G d).card - 1
  let P : Polynomial ℚ :=
    (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)) ^ k
  have hbaseData :
      (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)).IsMonicOfDegree 2 :=
    (Polynomial.isMonicOfDegree_X_pow ℚ 2).sub (by simp)
  have hbase : (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)).Monic :=
    hbaseData.monic
  have hbaseDegree :
      (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)).natDegree = 2 :=
    hbaseData.natDegree_eq
  have hP : P.Monic := hbase.pow k
  have hPDegree : P.natDegree = 2 * k := by
    change ((Polynomial.X ^ 2 - Polynomial.C (d : ℚ)) ^ k).natDegree =
      2 * k
    rw [hbase.natDegree_pow, hbaseDegree]
    omega
  have hcharMonic :
      (LinearMap.charpoly (G.adjMatrix ℚ).toLin').Monic :=
    (G.adjMatrix ℚ).toLin'.charpoly_monic
  have hQmonic : Q.Monic := by
    apply hP.of_mul_monic_left
    rw [← hQ]
    exact hcharMonic
  have hdegree := hP.natDegree_mul hQmonic
  rw [← hQ, LinearMap.charpoly_natDegree, hPDegree,
    Module.finrank_pi ℚ, hcard] at hdegree
  refine ⟨Q, hQmonic, hQ, ?_⟩
  dsimp [k] at hdegree ⊢
  omega

/-- Order-forty-nine specialization of the residual degree formula. -/
theorem exists_monic_orderFortyNineSeven_residualCharpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49)
    {a : V} (ha : a ∈ squareOrderHighVertices G 7) :
    ∃ Q : Polynomial ℚ,
      Q.Monic ∧
      LinearMap.charpoly (G.adjMatrix ℚ).toLin' =
        (Polynomial.X ^ 2 - Polynomial.C 7) ^
          ((squareOrderHighVertices G 7).card - 1) * Q ∧
      Q.natDegree =
        49 - 2 * ((squareOrderHighVertices G 7).card - 1) := by
  simpa using exists_monic_squareOrder_residualCharpoly
    G hfree (d := 7) (by norm_num) hmin hcover (by norm_num [hcard]) ha

/-- The residual polynomial has vanishing next coefficient, equivalently its
roots have sum zero. -/
theorem exists_monic_squareOrder_residualCharpoly_nextCoeff_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    ∃ Q : Polynomial ℚ,
      Q.Monic ∧
      LinearMap.charpoly (G.adjMatrix ℚ).toLin' =
        (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)) ^
          ((squareOrderHighVertices G d).card - 1) * Q ∧
      Q.natDegree =
        d * d - 2 * ((squareOrderHighVertices G d).card - 1) ∧
      Q.nextCoeff = 0 := by
  obtain ⟨Q, hQmonic, hfactor, hdegree⟩ :=
    exists_monic_squareOrder_residualCharpoly
      G hfree hd hmin hcover hcard ha
  let k := (squareOrderHighVertices G d).card - 1
  let p : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (d : ℚ)
  have hpData : p.IsMonicOfDegree 2 := by
    dsimp [p]
    exact (Polynomial.isMonicOfDegree_X_pow ℚ 2).sub (by simp)
  have hppow : (p ^ k).Monic := hpData.monic.pow k
  have hpnext : p.nextCoeff = 0 := by
    rw [Polynomial.nextCoeff, hpData.natDegree_eq]
    dsimp [p]
    simp
  have hfactorNext := congrArg Polynomial.nextCoeff hfactor
  rw [hppow.nextCoeff_mul hQmonic,
    hpData.monic.nextCoeff_pow, hpnext, nsmul_zero, zero_add] at hfactorNext
  have htrace : Matrix.trace (G.adjMatrix ℚ) = 0 := by
    simp [Matrix.trace]
  have hcharNext :
      (LinearMap.charpoly (G.adjMatrix ℚ).toLin').nextCoeff = 0 := by
    simp only [Matrix.charpoly_toLin']
    rw [← neg_eq_zero, ← Matrix.trace_eq_neg_charpoly_nextCoeff]
    exact htrace
  refine ⟨Q, hQmonic, hfactor, hdegree, ?_⟩
  exact hfactorNext ▸ hcharNext

end

end Erdos85
