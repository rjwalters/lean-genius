import Proofs.Erdos85ExcessEigenspace

/-!
# Even dimension for nonsquare quadratic operators over a field

The field-valued quadratic trace theorem has a stronger parity companion:
if `T² = aI` and `a` is not a square in the ground field, then the underlying
space has even dimension.  Applied to a defect eigenspace, this is the exact
Case B multiplicity constraint; no assertion is made in the square branch.
-/

namespace Erdos85

open Matrix Polynomial

noncomputable section

/-- Full characteristic-polynomial form of nonsquare quadraticity. -/
theorem Matrix.exists_charpoly_eq_quadraticScalar_pow_of_sq_eq_nonsquare
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M : Matrix I I K) (a : K) (ha : ¬ IsSquare a)
    (hM : M * M = a • (1 : Matrix I I K)) :
    ∃ k : ℕ, M.charpoly = quadraticScalar a ^ k ∧
      Fintype.card I = 2 * k := by
  have hdvd := charpoly_dvd_quadraticScalar_pow M a hM
  obtain ⟨k, _hk, hassoc⟩ :=
    (dvd_prime_pow (quadraticScalar_irreducible ha).prime
      (Fintype.card I)).mp hdvd
  have hchar : M.charpoly = quadraticScalar a ^ k :=
    Polynomial.eq_of_monic_of_associated M.charpoly_monic
      ((quadraticScalar_monic a).pow k) hassoc
  have hdeg := congrArg Polynomial.natDegree hchar
  rw [Matrix.charpoly_natDegree_eq_dim,
    (quadraticScalar_monic a).natDegree_pow, quadraticScalar_natDegree] at hdeg
  exact ⟨k, hchar, by omega⟩

/-- A square root of a nonsquare field scalar can act only in even matrix
dimension. -/
theorem Matrix.even_card_of_sq_eq_nonsquare
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M : Matrix I I K) (a : K) (ha : ¬ IsSquare a)
    (hM : M * M = a • (1 : Matrix I I K)) :
    Even (Fintype.card I) := by
  obtain ⟨k, _hchar, hcard⟩ :=
    Matrix.exists_charpoly_eq_quadraticScalar_pow_of_sq_eq_nonsquare
      M a ha hM
  exact ⟨k, by omega⟩

/-- Endomorphism form of field-valued nonsquare dimension parity. -/
theorem LinearMap.even_finrank_of_sq_eq_nonsquare
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]
    (T : E →ₗ[K] E) (a : K) (ha : ¬ IsSquare a)
    (hT : T * T = a • LinearMap.id) :
    Even (Module.finrank K E) := by
  let b := Module.Free.chooseBasis K E
  let M := LinearMap.toMatrix b b T
  have hM : M * M =
      a • (1 : Matrix (Module.Free.ChooseBasisIndex K E)
        (Module.Free.ChooseBasisIndex K E) K) := by
    have hmapped := congrArg (LinearMap.toMatrix b b) hT
    simpa [M, LinearMap.toMatrix_mul, LinearMap.toMatrix_id] using hmapped
  rw [Module.finrank_eq_card_chooseBasisIndex K E]
  exact Matrix.even_card_of_sq_eq_nonsquare M a ha hM

/-- Endomorphism characteristic polynomial in the nonsquare branch. -/
theorem LinearMap.exists_charpoly_eq_quadraticScalar_pow_of_sq_eq_nonsquare
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]
    (T : E →ₗ[K] E) (a : K) (ha : ¬ IsSquare a)
    (hT : T * T = a • LinearMap.id) :
    ∃ k : ℕ, T.charpoly = quadraticScalar a ^ k ∧
      Module.finrank K E = 2 * k := by
  let b := Module.Free.chooseBasis K E
  let M := LinearMap.toMatrix b b T
  have hM : M * M =
      a • (1 : Matrix (Module.Free.ChooseBasisIndex K E)
        (Module.Free.ChooseBasisIndex K E) K) := by
    have hmapped := congrArg (LinearMap.toMatrix b b) hT
    simpa [M, LinearMap.toMatrix_mul, LinearMap.toMatrix_id] using hmapped
  obtain ⟨k, hchar, hcard⟩ :=
    Matrix.exists_charpoly_eq_quadraticScalar_pow_of_sq_eq_nonsquare
      M a ha hM
  refine ⟨k, ?_, ?_⟩
  · rw [← LinearMap.charpoly_toMatrix T b]
    exact hchar
  · rw [Module.finrank_eq_card_chooseBasisIndex K E]
    exact hcard

/-- **Nonsquare defect sectors have even multiplicity.**  For a regular
square-identity graph, every nonprincipal defect eigenspace whose ambient
square scalar is nonsquare has even dimension over the ground field. -/
theorem graph_even_finrank_defectEigenspace_of_regular_excess_field
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hregD : ∀ x, (secondOrderDefectGraph G).degree x = e + 2)
    {μ : K} (hμ : μ ≠ (e + 2 : ℕ))
    (hnonsquare : ¬ IsSquare ((d : K) - 1 - μ)) :
    Even (Module.finrank K
      (defectEigenspace ((secondOrderDefectGraph G).adjMatrix K) μ)) := by
  let A := G.adjMatrix K
  let D := (secondOrderDefectGraph G).adjMatrix K
  let hcomm : A * D = D * A :=
    adjMatrix_comm_secondOrderDefect_of_regular_field G hfree hreg
  have hsq := graph_defectEigenspaceRestrict_sq_of_regular_excess_field
    G hfree hreg hregD hμ
  exact LinearMap.even_finrank_of_sq_eq_nonsquare
    (defectEigenspaceRestrict A hcomm μ) ((d : K) - 1 - μ)
      hnonsquare hsq

/-- **Exact nonsquare frequency factor.**  The characteristic polynomial of
the ambient adjacency restriction to a nonsquare defect sector is a pure
power of `X² - (d - 1 - μ)`. -/
theorem graph_exists_restrict_charpoly_eq_quadraticScalar_pow_of_regular_excess_field
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hregD : ∀ x, (secondOrderDefectGraph G).degree x = e + 2)
    {μ : K} (hμ : μ ≠ (e + 2 : ℕ))
    (hnonsquare : ¬ IsSquare ((d : K) - 1 - μ)) :
    let A := G.adjMatrix K
    let D := (secondOrderDefectGraph G).adjMatrix K
    let hcomm : A * D = D * A :=
      adjMatrix_comm_secondOrderDefect_of_regular_field G hfree hreg
    ∃ k : ℕ,
      (defectEigenspaceRestrict A hcomm μ).charpoly =
        quadraticScalar ((d : K) - 1 - μ) ^ k ∧
      Module.finrank K (defectEigenspace D μ) = 2 * k := by
  dsimp only
  apply LinearMap.exists_charpoly_eq_quadraticScalar_pow_of_sq_eq_nonsquare
    _ _ hnonsquare
  exact graph_defectEigenspaceRestrict_sq_of_regular_excess_field
    G hfree hreg hregD hμ

end

end Erdos85
