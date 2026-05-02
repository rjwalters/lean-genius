/-
  Nonderogatory ⟹ Cyclic Vector: All Fields (Primary Decomposition)

  Every nonderogatory matrix over ANY field K (finite or infinite, any size)
  has a cyclic vector. This formalization uses the primary decomposition approach
  from WIP04, avoiding the Rational Canonical Form axiom entirely.

  ## Proof Structure (V2: Axiom-Free)

  V1 axiomatized the RCF similarity theorem (nonderogatory_similar_companion).
  V2 eliminates that axiom using direct algebraic arguments:

  1. **[Proved, WIP04]** Primary decomposition: Given the factored form of
     minpoly K M = ∏ p_i^{e_i}, construct primary vectors v_i in
     ker(p_i^{e_i}(M)) \ ker(p_i^{e_i-1}(M)) via minimality of minpoly.

  2. **[Proved, WIP04]** CRT combination: v = ∑ v_i is cyclic. For any r with
     r(M)v = 0, Bezout projections extract r(M)v_i = 0 for each i, giving
     p_i^{e_i} | r by pow_irred_dvd_of_annihilated. Then ∏ p_i^{e_i} | r by
     pairwise coprimality, so deg(r) ≥ n — contradiction with deg(r) < n.

  3. **[Proved, Aristotle]** Factorization bridge: Every monic polynomial of positive
     degree over a field factors into coprime monic irreducible prime powers.
     Proved via UniqueFactorizationMonoid.normalizedFactors in the companion file
     CayleyHamiltonCyclicVectorAllFieldsAristotle.lean.

  ## Status: 0 axioms, 0 sorries (fully verified)

  All mathematical content is machine-checked. The factorization bridge was proved
  by Aristotle proof search using Mathlib's UniqueFactorizationMonoid API.

  ## Why V2 is Stronger than V1

  V1's axiom (RCF similarity) required the structure theorem for finitely
  generated modules over a PID — ~800 lines to formalize, fundamentally deep.
  V2 delegates only to standard UFD API in Mathlib.

  ## Related Gallery Entries

  - `cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-04`: Full proof (WIP04)
  - `cayley-hamilton-minpoly-oq-05-oq-01-oq-04`: Module-theory approach
  - `cayley-hamilton-reduction-oq-02-oq-01`: Companion matrix properties
-/
import Mathlib
import Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04
import Proofs.CayleyHamiltonCyclicVectorAllFieldsAristotle

noncomputable section

namespace CayleyHamiltonCyclicVectorAllFields

open Matrix Polynomial

-- ============================================================
-- SECTION I: Definitions
-- ============================================================

/-- A vector v ∈ Kⁿ is **cyclic** for M if no nonzero polynomial of degree < n
    annihilates both M and v. Equivalently, {v, Mv, ..., M^{n-1}v} is a basis. -/
abbrev IsCyclicVector {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  GeneralCyclicVector.IsCyclicVector M v

/-- A matrix M is **nonderogatory** if its minimal polynomial equals its
    characteristic polynomial (both monic, both of degree n). -/
abbrev IsNonderogatory {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : Prop :=
  GeneralCyclicVector.IsNonderogatory M

-- ============================================================
-- SECTION II: Factorization Bridge
-- ============================================================

/-- Every monic polynomial of positive degree over a field factors into a
    finite product of coprime monic irreducible prime powers.

    This follows from K[X] being a UniqueFactorizationMonoid:
    1. `normalizedFactors μ` gives monic irreducible factors (with multiplicity)
    2. Group by `toFinset` + `count` to get distinct primes with exponents
    3. Distinct monic irreducibles are coprime (prime → coprime_iff_not_dvd)
    4. Product equality from `normalizedFactors_prod` + monicity

    Suitable for Aristotle submission (routine Mathlib API, ~50 lines). -/
private theorem monic_factored_form {K : Type*} [Field K]
    (μ : K[X]) (hμ_monic : μ.Monic) (hμ_deg : 0 < μ.natDegree) :
    ∃ (k : ℕ) (_ : 0 < k) (p : Fin k → K[X]) (e : Fin k → ℕ),
      (∀ i, Irreducible (p i)) ∧
      (∀ i, (p i).Monic) ∧
      (∀ i, 0 < e i) ∧
      (∀ i j : Fin k, i ≠ j → IsCoprime (p i ^ e i) (p j ^ e j)) ∧
      μ = ∏ i : Fin k, p i ^ e i :=
  CayleyHamiltonCyclicVectorAllFieldsAristotle.monic_factored_form μ hμ_monic hμ_deg

-- ============================================================
-- SECTION III: Main Theorem
-- ============================================================

/-- **Main Theorem**: Over ANY field K (including finite fields F_q with q ≤ n),
    every nonderogatory matrix has a cyclic vector.

    **Proof**:
    - Case n = 0: trivial (Fin 0 → K is empty, the empty function works).
    - Case n > 0:
      1. Factor minpoly K M = ∏ p_i^{e_i} via `monic_factored_form`.
      2. Apply WIP04's primary decomposition theorem
         (`GeneralCyclicVector.nonderogatory_general_has_cyclic_vector`).

    **Why this works over finite fields**: The proof never invokes |K| > n.
    The key insight is that primary decomposition + CRT provides a cyclic vector
    purely from the annihilator structure, bypassing union avoidance entirely. -/
theorem nonderogatory_has_cyclic_vector
    {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v := by
  -- Dispatch trivial n = 0 case
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun p hp _ => by omega⟩
  -- minpoly facts
  have hμ_monic : (minpoly K M).Monic := minpoly.monic (Matrix.isIntegral M)
  have hμ_deg : (minpoly K M).natDegree = n := by
    rw [h, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Factor minpoly into coprime prime powers
  obtain ⟨k, hk, p, e, hp_irr, hp_monic, he_pos, hcop, hprod⟩ :=
    monic_factored_form (minpoly K M) hμ_monic (by omega)
  -- Apply WIP04's axiom-free primary decomposition theorem
  exact GeneralCyclicVector.nonderogatory_general_has_cyclic_vector
    hk M h p e hp_irr hp_monic he_pos hcop hprod

-- ============================================================
-- SECTION IV: Corollaries
-- ============================================================

/-- **Corollary (Finite Fields)**: The cyclic vector theorem holds over any
    finite field, including F_q with q ≤ n (where union avoidance fails). -/
theorem nonderogatory_has_cyclic_vector_finite
    {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v :=
  nonderogatory_has_cyclic_vector M h

/-- **Corollary (Uniqueness condition)**: If M is nonderogatory, a vector v is
    cyclic iff it is not annihilated by any polynomial of degree < n. -/
theorem cyclic_iff_not_killed_below_degree
    {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) (v : Fin n → K) :
    IsCyclicVector M v ↔ ∀ p : K[X], p ≠ 0 → p.natDegree < n → ¬(aeval M p).mulVec v = 0 := by
  constructor
  · intro hcyc p hne hdeg hann
    exact hne (hcyc p hdeg hann)
  · intro h' p hdeg hann
    by_contra hne
    exact h' p hne hdeg hann

-- ============================================================
-- SECTION V: Summary
-- ============================================================

/-!
## Summary

This formalization proves the cyclic vector theorem for nonderogatory matrices
over arbitrary fields using primary decomposition (WIP04).

**V2 Upgrade**: Eliminated the RCF similarity axiom from V1. The proof no longer
depends on the Rational Canonical Form theorem or the structure theorem for
finitely generated modules over PIDs.

**What is fully proved (sorry-free, axiom-free)**:
- Primary decomposition construction (GeneralCyclicVector, WIP04)
- Bezout projections and CRT-based cyclic vector construction (WIP04)
- `monic_factored_form`: proved by Aristotle via UFD API (companion file)
- `nonderogatory_has_cyclic_vector`: main theorem
- `nonderogatory_has_cyclic_vector_finite`: finite field corollary
- `cyclic_iff_not_killed_below_degree`: characterization corollary

**V1 → V2 → V3 delta**:
- V1→V2: Removed `axiom nonderogatory_similar_companion` (RCF similarity), added `sorry` in `monic_factored_form`
- V2→V3: Proved `monic_factored_form` via Aristotle (companion file); file now 0 axioms, 0 sorries
-/

end CayleyHamiltonCyclicVectorAllFields

end
