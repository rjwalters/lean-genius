import Proofs.Erdos85QuadraticTrace

/-!
# Dimension parity for a rational nonsquare quadratic operator

The trace-zero theorem for `T² = cI` is accompanied by a stronger elementary
fact: when `c` is a nonsquare natural, the underlying rational vector space
has even dimension.  This file exposes that fact for later quotient arguments.
-/

namespace Erdos85

open Matrix Polynomial

/-- A rational square root of a nonsquare scalar can act only in even matrix
dimension. -/
theorem Matrix.even_card_of_sq_eq_nonsquare_nat
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℚ) (c : ℕ) (hc : ¬ IsSquare c)
    (hM : M * M = (c : ℚ) • (1 : Matrix I I ℚ)) :
    Even (Fintype.card I) := by
  have hdvd := charpoly_dvd_quadraticNat_pow M c hM
  obtain ⟨k, hk, hassoc⟩ :=
    (dvd_prime_pow (quadraticNat_irreducible hc).prime
      (Fintype.card I)).mp hdvd
  have hchar : M.charpoly = quadraticNat c ^ k :=
    Polynomial.eq_of_monic_of_associated M.charpoly_monic
      ((quadraticNat_monic c).pow k) hassoc
  have hdeg := congrArg Polynomial.natDegree hchar
  rw [Matrix.charpoly_natDegree_eq_dim,
    (quadraticNat_monic c).natDegree_pow, quadraticNat_natDegree] at hdeg
  exact ⟨k, by omega⟩

/-- Endomorphism form of the nonsquare quadratic dimension theorem. -/
theorem LinearMap.even_finrank_of_sq_eq_nonsquare_nat
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E) (c : ℕ) (hc : ¬ IsSquare c)
    (hT : T * T = (c : ℚ) • LinearMap.id) :
    Even (Module.finrank ℚ E) := by
  let b := Module.Free.chooseBasis ℚ E
  let M := LinearMap.toMatrix b b T
  have hM : M * M =
      (c : ℚ) • (1 : Matrix (Module.Free.ChooseBasisIndex ℚ E)
        (Module.Free.ChooseBasisIndex ℚ E) ℚ) := by
    have hmapped := congrArg (LinearMap.toMatrix b b) hT
    simpa [M, LinearMap.toMatrix_mul, LinearMap.toMatrix_id] using hmapped
  rw [Module.finrank_eq_card_chooseBasisIndex ℚ E]
  exact Matrix.even_card_of_sq_eq_nonsquare_nat M c hc hM

end Erdos85
