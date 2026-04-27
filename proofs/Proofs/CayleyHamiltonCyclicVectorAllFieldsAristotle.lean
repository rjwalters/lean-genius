/-
  Aristotle targets for CayleyHamiltonCyclicVectorAllFields

  Routine polynomial factorization bridge for automated proof search.
  See CayleyHamiltonCyclicVectorAllFields.lean for the main formalization.

  Target: monic_factored_form
  Every monic polynomial of positive degree over a field factors into a finite
  product of coprime monic irreducible prime powers.
  This follows from K[X] being a UniqueFactorizationMonoid via normalizedFactors.
-/
import Mathlib

namespace CayleyHamiltonCyclicVectorAllFieldsAristotle

open Polynomial UniqueFactorizationMonoid

/-- Every monic polynomial of positive degree over a field factors into a
    finite product of coprime monic irreducible prime powers.

    Proof sketch:
    1. normalizedFactors μ gives monic irreducible factors with multiplicity
    2. Group by distinct primes with exponents via toFinset + count
    3. Distinct monic irreducibles are coprime (prime → IsCoprime)
    4. Product equality from normalizedFactors_prod + monicity -/
theorem monic_factored_form {K : Type*} [Field K]
    (μ : K[X]) (hμ_monic : μ.Monic) (hμ_deg : 0 < μ.natDegree) :
    ∃ (k : ℕ) (_ : 0 < k) (p : Fin k → K[X]) (e : Fin k → ℕ),
      (∀ i, Irreducible (p i)) ∧
      (∀ i, (p i).Monic) ∧
      (∀ i, 0 < e i) ∧
      (∀ i j : Fin k, i ≠ j → IsCoprime (p i ^ e i) (p j ^ e j)) ∧
      μ = ∏ i : Fin k, p i ^ e i := by
  sorry

end CayleyHamiltonCyclicVectorAllFieldsAristotle
