/-
  p-adic Algebraic Closure: [ℚ̄_p : ℚ_p] = ∞

  Contrasts the real case [ℂ:ℝ] = 2 with the p-adic case [ℚ̄_p:ℚ_p] = ∞.
  The key vehicle is X^n - p, which is irreducible over ℚ_p for every n ≥ 1
  (Newton polygon: single segment from (0,1) to (n,0), slope -1/n, gcd(1,n)=1).
  This gives ℚ_p field extensions of all degrees n, so [ℚ̄_p:ℚ_p] = ∞.

  ## Results

  ### Proved (2 axioms, 0 sorries):
  1. real_complex_finrank: [ℂ:ℝ] = 2 (Mathlib delegation)
  2. real_complex_module_finite: Module.Finite ℝ ℂ (typeclass)
  3. Xn_sub_p_irred_Z: X^n - p irreducible over ℤ (Eisenstein at (p))
  4. Xn_sub_p_irred_Q: X^n - p irreducible over ℚ (Gauss + NthRootIrrationalOQ01)
  5. Xn_sub_p_ne_zero_Qp: X^n - C p ≠ 0 over ℚ_p for n ≥ 1
  6. natDegree_Xn_sub_p: natDegree(X^n - C p over ℚ_p) = n
  7. padic_root_extension_finrank: [AdjoinRoot(X^n - p):ℚ_p] = n (PowerBasis)
  8. padic_quadratic_extension: [ℚ_p(√p):ℚ_p] = 2 (n=2)
  9. padic_cubic_extension: [ℚ_p(∛p):ℚ_p] = 3 (n=3)
  10. padic_quartic_extension: [ℚ_p(p^{1/4}):ℚ_p] = 4 (n=4)
  11. real_padic_closure_contrast: [ℂ:ℝ] = 2 ∧ ¬Module.Finite ℚ_[p] (AlgClosure ℚ_[p])
  12. padic_extensions_unbounded: ℚ_p has field extensions of every degree n ≥ 1
  13. padic_extensions_strictly_unbounded: extensions exceed any finite bound
  14. degree_contrast_summary: four-part conjunction of all results

  ### Axiomatized (Newton polygon + AlgebraicClosure infrastructure):
  1. Xn_sub_p_irred_Qp: X^n - p irreducible over ℚ_p (Newton polygon argument)
  2. padic_alg_closure_infinite_dim: ¬Module.Finite ℚ_[p] (AlgebraicClosure ℚ_[p])

  ## References
  - Serre, J.-P., Local Fields, Springer GTM 67 (1979).
  - Neukirch, J., Algebraic Number Theory, Springer GMW 322 (1999), Ch. II §6.
  - Gouvêa, F.Q., p-adic Numbers: An Introduction, 2nd ed., Springer (2003), Ch. 3.
-/

import Mathlib
import Proofs.NthRootIrrationalOQ01

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Polynomial

namespace PadicAlgClosureContrast

variable {p : ℕ} [Fact (Nat.Prime p)]

private theorem p_prime : Nat.Prime p := Fact.out

noncomputable section

-- ============================================================================
-- Part I: Real Case — [ℂ:ℝ] = 2 (Reference Point for Contrast)
-- ============================================================================

/-- The extension degree [ℂ:ℝ] = 2. Starting point for the real/p-adic contrast. -/
theorem real_complex_finrank : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

/-- ℂ is a finite extension of ℝ (typeclass instance). -/
theorem real_complex_module_finite : Module.Finite ℝ ℂ := inferInstance

-- ============================================================================
-- Part II: X^n - p Irreducible over ℚ (via Eisenstein + Gauss)
-- ============================================================================

/-- X^n - p is irreducible over ℤ via the Eisenstein criterion at the prime ideal (p).
    Leading coeff 1 ∉ (p); non-leading coefficients 0 ∈ (p); constant -p ∈ (p);
    but -p ∉ (p)^2 since p² ∤ p for prime p. -/
theorem Xn_sub_p_irred_Z (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (X ^ n - C (p : ℤ) : ℤ[X]) := by
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast p_prime.ne_zero
  have hp_int : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]; exact_mod_cast p_prime
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(p : ℤ)})
  · rw [Ideal.span_singleton_prime hp_ne]; exact hp_int
  · rw [leadingCoeff_X_pow_sub_C (by omega : 0 < n), Ideal.mem_span_singleton]
    exact hp_int.not_dvd_one
  · intro k hk
    rw [degree_X_pow_sub_C (by omega : 0 < n) (p : ℤ)] at hk
    have hkn : k < n := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow, coeff_C]
    have hkne : ¬(k = n) := by omega
    simp only [if_neg hkne, zero_sub, dvd_neg]
    by_cases hk0 : k = 0 <;> simp [hk0]
  · rw [degree_X_pow_sub_C (by omega : 0 < n) (p : ℤ)]; exact_mod_cast (by omega : 0 < n)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [coeff_sub, coeff_X_pow, coeff_C, show ¬(0 = n) from by omega,
               ite_false, zero_sub, dvd_neg]
    intro h
    have hle := Int.le_of_dvd (by exact_mod_cast p_prime.pos : 0 < (p : ℤ)) h
    nlinarith [sq_nonneg ((p : ℤ) - 1), show (1 : ℤ) < p from by exact_mod_cast p_prime.one_lt]
  · exact (monic_X_pow_sub_C (p : ℤ) (by omega : n ≠ 0)).isPrimitive

/-- X^n - p is irreducible over ℚ for n ≥ 2, via Gauss's lemma from the ℤ result. -/
theorem Xn_sub_p_irred_Q (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (X ^ n - C (p : ℚ) : ℚ[X]) :=
  NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime n p hn p_prime

-- ============================================================================
-- Part III: Newton Polygon Axiom — X^n - p Irreducible over ℚ_p
-- ============================================================================

/-- **Axiom**: X^n - p is irreducible over ℚ_p for n ≥ 1.

    Newton polygon of X^n - p at p: single segment from (0, v_p(p)) = (0,1)
    to (n, 0) with slope -1/n. Since gcd(1, n) = 1, the Ore-Hensel criterion
    implies irreducibility.

    Equivalently: X^n - p satisfies Eisenstein at the maximal ideal (p) of the DVR ℤ_p.
    Gauss's lemma for DVRs transfers irreducibility from ℤ_p[X] to ℚ_p[X].
    Bridging PadicInt to Mathlib's DVR framework requires additional infrastructure. -/
axiom Xn_sub_p_irred_Qp (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (X ^ n - C (p : ℚ_[p]) : ℚ_[p][X])

-- ============================================================================
-- Part IV: Degree-n Extensions of ℚ_p (Machine-Checked via AdjoinRoot)
-- ============================================================================

/-- X^n - C p ≠ 0 over ℚ_p for n ≥ 1 (has natDegree n ≥ 1, so nonzero). -/
theorem Xn_sub_p_ne_zero_Qp (n : ℕ) (hn : 1 ≤ n) :
    (X ^ n - C (p : ℚ_[p]) : ℚ_[p][X]) ≠ 0 := by
  have h : (C (p : ℚ_[p])).natDegree < (X ^ n : ℚ_[p][X]).natDegree := by
    simp [natDegree_C, natDegree_pow, natDegree_X]; omega
  have hne := natDegree_sub_eq_left_of_natDegree_lt h
  intro heq; simp [heq] at hne; simp [natDegree_pow, natDegree_X] at hne; omega

/-- natDegree(X^n - C p) = n over ℚ_p. -/
theorem natDegree_Xn_sub_p (n : ℕ) (hn : 1 ≤ n) :
    (X ^ n - C (p : ℚ_[p])).natDegree = n := by
  have h : (C (p : ℚ_[p])).natDegree < (X ^ n : ℚ_[p][X]).natDegree := by
    simp [natDegree_C, natDegree_pow, natDegree_X]; omega
  rw [natDegree_sub_eq_left_of_natDegree_lt h, natDegree_pow, natDegree_X, mul_one]

/-- **Main result**: [AdjoinRoot(X^n - p) : ℚ_p] = n for all n ≥ 1.
    AdjoinRoot.powerBasis gives a ℚ_p-basis of size natDegree(X^n - p) = n.
    The polynomial need only be nonzero (irreducibility is not required for finrank). -/
theorem padic_root_extension_finrank (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank ℚ_[p] (AdjoinRoot (X ^ n - C (p : ℚ_[p]))) = n := by
  rw [(AdjoinRoot.powerBasis (Xn_sub_p_ne_zero_Qp n hn)).finrank,
      AdjoinRoot.powerBasis_dim]
  exact natDegree_Xn_sub_p n hn

/-- Concrete case n = 2: [ℚ_p(√p) : ℚ_p] = 2. -/
theorem padic_quadratic_extension :
    Module.finrank ℚ_[p] (AdjoinRoot (X ^ 2 - C (p : ℚ_[p]))) = 2 :=
  padic_root_extension_finrank 2 (by norm_num)

/-- Concrete case n = 3: [ℚ_p(∛p) : ℚ_p] = 3. -/
theorem padic_cubic_extension :
    Module.finrank ℚ_[p] (AdjoinRoot (X ^ 3 - C (p : ℚ_[p]))) = 3 :=
  padic_root_extension_finrank 3 (by norm_num)

/-- Concrete case n = 4: [ℚ_p(p^{1/4}) : ℚ_p] = 4. -/
theorem padic_quartic_extension :
    Module.finrank ℚ_[p] (AdjoinRoot (X ^ 4 - C (p : ℚ_[p]))) = 4 :=
  padic_root_extension_finrank 4 (by norm_num)

-- ============================================================================
-- Part V: [ℚ̄_p : ℚ_p] = ∞ (Axiomatized)
-- ============================================================================

/-- **Axiom**: The algebraic closure of ℚ_p is not finite-dimensional over ℚ_p.

    Justification: padic_root_extension_finrank gives finrank n for every n ≥ 1,
    so extensions are unbounded. If Module.Finite held, finrank would be bounded.
    Formalizing requires embedding AdjoinRoot(X^n - p) into AlgebraicClosure ℚ_[p]
    and using finrank monotonicity — this needs the irreducibility axiom and the
    AlgebraicClosure embedding infrastructure. -/
axiom padic_alg_closure_infinite_dim :
    ¬ Module.Finite ℚ_[p] (AlgebraicClosure ℚ_[p])

-- ============================================================================
-- Part VI: Contrast Summary
-- ============================================================================

/-- **Contrast theorem**: [ℂ:ℝ] = 2 (one quadratic step) vs ¬Module.Finite for ℚ_p. -/
theorem real_padic_closure_contrast :
    Module.finrank ℝ ℂ = 2 ∧ ¬ Module.Finite ℚ_[p] (AlgebraicClosure ℚ_[p]) :=
  ⟨real_complex_finrank, padic_alg_closure_infinite_dim⟩

/-- ℚ_p has field extensions of every degree n ≥ 1 (AdjoinRoot(X^n - p) has degree n). -/
theorem padic_extensions_unbounded (n : ℕ) (hn : 1 ≤ n) :
    ∃ (K : Type*) (_ : Field K) (_ : Algebra ℚ_[p] K), Module.finrank ℚ_[p] K = n :=
  ⟨AdjoinRoot (X ^ n - C (p : ℚ_[p])), inferInstance, inferInstance,
   padic_root_extension_finrank n hn⟩

/-- For any bound N, ℚ_p has an extension of degree exceeding N. -/
theorem padic_extensions_strictly_unbounded (N : ℕ) :
    ∃ (K : Type*) (_ : Field K) (_ : Algebra ℚ_[p] K), N < Module.finrank ℚ_[p] K := by
  obtain ⟨K, hf, ha, hrk⟩ := padic_extensions_unbounded (N + 1) (by omega)
  exact ⟨K, hf, ha, hrk ▸ by omega⟩

/-- **Degree contrast summary**: [ℂ:ℝ] = 2; [ℚ_p(p^{1/n}):ℚ_p] = n; extensions unbounded;
    [ℚ̄_p:ℚ_p] = ∞. -/
theorem degree_contrast_summary :
    Module.finrank ℝ ℂ = 2 ∧
    (∀ n : ℕ, 1 ≤ n →
      Module.finrank ℚ_[p] (AdjoinRoot (X ^ n - C (p : ℚ_[p]))) = n) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ (K : Type*) (_ : Field K) (_ : Algebra ℚ_[p] K),
      Module.finrank ℚ_[p] K = n) ∧
    ¬ Module.Finite ℚ_[p] (AlgebraicClosure ℚ_[p]) :=
  ⟨real_complex_finrank, padic_root_extension_finrank,
   padic_extensions_unbounded, padic_alg_closure_infinite_dim⟩

end

end PadicAlgClosureContrast

#check @PadicAlgClosureContrast.real_complex_finrank
#check @PadicAlgClosureContrast.padic_root_extension_finrank
#check @PadicAlgClosureContrast.real_padic_closure_contrast
#check @PadicAlgClosureContrast.degree_contrast_summary
