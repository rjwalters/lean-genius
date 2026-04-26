/-
  Nonderogatory ⟹ Cyclic Vector: All Fields (Axiomatized via RCF Similarity)

  Every nonderogatory matrix over ANY field K (finite or infinite, any size)
  has a cyclic vector. This formalization uses one explicit axiom — the
  Rational Canonical Form (RCF) similarity theorem — and proves the main
  result from it using fully verified supporting lemmas.

  ## Proof Structure

  The key insight is that the union avoidance argument (which fails over
  small finite fields) is unnecessary. Instead, the algebraic structure of
  the companion matrix suffices:

  1. **[Axiom]** `nonderogatory_similar_companion`: Every nonderogatory M is
     similar to its companion matrix C(minpoly M). This is the single-block
     case of the rational canonical form (Frobenius normal form), which requires
     the structure theorem for f.g. modules over K[X] (a PID). Not yet in Mathlib.

  2. **[Proved]** `companionMatrix_cyclic_e0`: The standard basis vector e₀ is
     a cyclic vector for C(p). Proved via the orbit argument: C(p)^k · e₀ = eₖ.

  3. **[Proved]** `cyclic_vector_of_similar`: Cyclic vectors transfer under
     matrix similarity. Proved using the fact that conjugation by P is an
     algebra endomorphism.

  4. **Main theorem**: Combine 1+2+3. M ~ C(minpoly M) gives P, e₀ is cyclic
     for C(minpoly M), so P⁻¹ · e₀ is cyclic for M.

  ## Status: axiomatized (1 axiom, 0 sorries)

  The axiomCount = 1 reflects the explicit `axiom` declaration for the
  RCF similarity theorem. All other theorems are fully proved.

  ## Related Gallery Entries

  - `cayley-hamilton-minpoly-oq-05-oq-01-oq-04`: Module-theory approach (1 sorry)
  - `cayley-hamilton-reduction-oq-02-oq-01`: Companion matrix properties
  - `cayley-hamilton-minpoly-oq-05-oq-01`: Infinite-field case (union avoidance)
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic
import Proofs.CayleyHamiltonReductionOQ02OQ01
import Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04

noncomputable section

namespace CayleyHamiltonCyclicVectorAllFields

open Matrix Polynomial

-- ============================================================
-- SECTION I: Definitions (aliases to parent namespace)
-- ============================================================

/-- A vector v ∈ Kⁿ is **cyclic** for M if no nonzero polynomial of degree < n
    annihilates both M and v. Equivalently, {v, Mv, ..., M^{n-1}v} is a basis. -/
abbrev IsCyclicVector {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  CyclicVectorArbitrary.IsCyclicVector M v

/-- A matrix M is **nonderogatory** if its minimal polynomial equals its
    characteristic polynomial (both monic, both of degree n). -/
abbrev IsNonderogatory {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : Prop :=
  CyclicVectorArbitrary.IsNonderogatory M

-- ============================================================
-- SECTION II: The RCF Axiom
-- ============================================================

/-- **Axiom (RCF Similarity)**: Every nonderogatory matrix is similar to its companion matrix.

    Formally: if M ∈ Mₙ(K) is nonderogatory (minpoly K M = charpoly M), then
    there exists an invertible P ∈ GLₙ(K) such that
      M = P⁻¹ · C(minpoly M) · P
    where C(p) is the companion matrix of p.

    **Mathematical content**: This is the single-block rational canonical form.
    Over K[X] (a PID), nonderogatory forces Kⁿ ≅ K[X]/(minpoly M) as K[X]-modules
    (a single cyclic factor). The change-of-basis matrix P is the map taking the
    cyclic basis {e₀, C·e₀, C²·e₀, ...} to the standard basis.

    **Mathlib gap**: The structure theorem for finitely generated modules over a PID
    is not yet in Mathlib 4 (as of v4.26.0). Once available, this axiom can be
    removed and replaced by a constructive proof.

    **References**: Horn & Johnson, "Matrix Analysis" §3.3; Hoffman & Kunze §7.2. -/
axiom nonderogatory_similar_companion
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ P : (Matrix (Fin n) (Fin n) K)ˣ,
      M = P.inv * CayleyHamiltonReductionOQ02OQ01.companionMatrix (d := n) (minpoly K M) * P.val

-- ============================================================
-- SECTION III: Main Theorem
-- ============================================================

/-- **Main Theorem**: Over ANY field K (including finite fields F_q with q ≤ n),
    every nonderogatory matrix has a cyclic vector.

    **Proof**:
    - Case n = 0: trivial (Fin 0 → K is empty, the empty function works).
    - Case n > 0:
      1. Axiom gives invertible P with M = P⁻¹ · C(minpoly M) · P.
      2. minpoly M has degree n (since M is nonderogatory and charpoly has degree n).
      3. `companionMatrix_cyclic_e0` (proved): e₀ is cyclic for C(minpoly M).
         This uses the orbit property: C(p)^k · e₀ = eₖ for k < n.
      4. `cyclic_vector_of_similar` (proved): since M ~ C(minpoly M) via P,
         the vector v = P⁻¹ · e₀ is cyclic for M.

    **Why this works over finite fields**: Steps 1-4 are purely algebraic —
    they never invoke |K| > n. The union avoidance argument (used for infinite fields)
    is bypassed entirely. The key insight is structural: companion matrices have a
    distinguished cyclic vector by construction. -/
theorem nonderogatory_has_cyclic_vector
    {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v := by
  -- Dispatch trivial n = 0 case
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun p hp _ => by omega⟩
  -- Step 1: M ~ C(minpoly M) via the RCF axiom
  obtain ⟨P, hMC⟩ := nonderogatory_similar_companion hn M h
  -- Step 2: minpoly M has degree n (nonderogatory ↔ minpoly = charpoly, deg = n)
  have hμ_monic : (minpoly K M).Monic := minpoly.monic (Matrix.isIntegral M)
  have hμ_deg : (minpoly K M).natDegree = n := by
    -- h : minpoly K M = M.charpoly, and charpoly has degree = Fintype.card (Fin n) = n
    rw [h, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Step 3: e₀ is cyclic for C(minpoly M) — orbit argument
  have hcyc :=
    CyclicVectorArbitrary.companionMatrix_cyclic_e0 hn (minpoly K M) hμ_monic hμ_deg
  -- Step 4: Transfer cyclic vector along similarity M = P⁻¹ · C · P
  exact CyclicVectorArbitrary.cyclic_vector_of_similar M
    (CayleyHamiltonReductionOQ02OQ01.companionMatrix (d := n) (minpoly K M))
    P hMC _ hcyc

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
    cyclic iff it is not annihilated by any polynomial of degree < n.
    (This follows from the main theorem and annihilator characterization.) -/
theorem cyclic_iff_not_killed_below_degree
    {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) (v : Fin n → K) :
    IsCyclicVector M v ↔ ∀ p : K[X], p ≠ 0 → p.natDegree < n → ¬(aeval M p).mulVec v = 0 := by
  simp only [IsCyclicVector, CyclicVectorArbitrary.IsCyclicVector]
  constructor
  · intro hcyc p hne hdeg hann
    exact hne (hcyc p hdeg hann)
  · intro h p hdeg hann
    by_contra hne
    exact h p hne hdeg hann

-- ============================================================
-- SECTION V: Summary
-- ============================================================

/-!
## Summary

This formalization axiomatizes the Rational Canonical Form similarity theorem
and derives the cyclic vector theorem from it in three proved steps.

**What is fully proved (sorry-free)**:
- `companionMatrix_cyclic_e0`: e₀ cyclic for C(p) (from CayleyHamiltonMinpolyOQ05OQ01OQ04)
- `cyclic_vector_of_similar`: cyclic vectors transfer under similarity (from same file)
- `nonderogatory_has_cyclic_vector`: main theorem (this file)
- `nonderogatory_has_cyclic_vector_finite`: finite field corollary (this file)
- `cyclic_iff_not_killed_below_degree`: characterization corollary (this file)

**The one axiom**:
- `nonderogatory_similar_companion`: M ~ C(minpoly M) for nonderogatory M
  This is the single-block RCF / Frobenius normal form theorem.
  Requires: structure theorem for f.g. modules over K[X] (PID).
  Not yet available in Mathlib 4.

**For the full proof without axioms**:
Formalize the PID structure theorem (Smith normal form for F[X]-matrices),
then replace the axiom with its proof. Estimated: ~800 lines for Smith normal
form + ~200 lines for the RCF similarity reduction.
-/

end CayleyHamiltonCyclicVectorAllFields

end
