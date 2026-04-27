/-
  Aristotle targets for CayleyHamiltonCyclicVectorAllFields

  Exposes routine supporting lemmas from the CayleyHamiltonCyclicVectorAllFields
  proof for automated proof search via Aristotle.

  The main sorry in the parent file is `monic_factored_form`: a standard
  consequence of K[X] being a UniqueFactorizationMonoid, requiring ~50 lines
  of Mathlib API navigation (normalizedFactors, coprime irreducibles, product
  reconstruction). This is routine algebra, not a mathematical assumption.

  See CayleyHamiltonCyclicVectorAllFields.lean for the main formalization.

  Targets:
  1. monic_factored_form: UFD factorization of monic polynomial into coprime
     monic irreducible prime powers.
-/
import Mathlib

noncomputable section

namespace CayleyHamiltonCyclicVectorAllFieldsAristotle

open Polynomial

/-- Every monic polynomial of positive degree over a field factors into a
    finite product of coprime monic irreducible prime powers.

    Proof strategy: use K[X] as a UniqueFactorizationMonoid.
    - `normalizedFactors μ` gives monic irreducible factors with multiplicity
    - Group by `toFinset` + `count` to get distinct primes with exponents
    - Distinct monic irreducibles are coprime (Irreducible → prime in UFD → coprime)
    - Product equality from `normalizedFactors_prod` + monicity -/
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

end
