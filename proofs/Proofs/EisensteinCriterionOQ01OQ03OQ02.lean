/-
  Irreducibility of the p-th cyclotomic polynomial Φ_p, via Eisenstein at Φ_p(X + 1).

  This file answers the second open question of `eisenstein-criterion-oq-01-oq-03`:

    > Establish irreducibility of the p-th cyclotomic polynomial Φ_p by applying
    > irreducible_rat_of_eisenstein to Φ_p(X + 1).

  **The classical Gauss argument.**  The cyclotomic polynomial
  `Φ_p(X) = 1 + X + ⋯ + X^{p-1}` is not visibly Eisenstein at `p`.  Its translate

      Φ_p(X + 1) = ((X + 1)^p − 1) / X = ∑_{k=1}^{p} C(p, k) · X^{k−1}

  *is*: it is monic of degree `p − 1`, every lower coefficient `C(p, k)` with
  `1 ≤ k ≤ p − 1` is divisible by `p`, and its constant coefficient `C(p, 1) = p` is
  divisible by `p` but not by `p²`.  Eisenstein's criterion therefore makes
  `Φ_p(X + 1)` irreducible over `ℚ`; and since the translation `X ↦ X + 1` is a ring
  automorphism of `ℚ[X]`, `Φ_p` itself is irreducible over `ℚ`.

  **What is reused.**  We feed the Eisenstein data into the *parent's* reproved
  criterion `EisensteinCriterionOQ01OQ03.irreducible_rat_of_eisenstein` (a concrete
  divisibility form of Eisenstein + Gauss's lemma over `ℤ ⊂ ℚ`), demonstrating its
  reach beyond the `Xⁿ + p·g` family.  The Eisenstein-at-`p` data for `Φ_p(X + 1)` is
  Mathlib's `Polynomial.cyclotomic_comp_X_add_one_isEisensteinAt`; the final descent
  from `Φ_p(X + 1)` to `Φ_p` uses the polynomial automorphism
  `Polynomial.algEquivAevalXAddC` together with `MulEquiv.irreducible_iff`.

  This re-derives `Polynomial.cyclotomic.irreducible_rat` (for prime indices) through
  the elementary Eisenstein route rather than invoking it.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib
import Proofs.EisensteinCriterionOQ01OQ03

open Polynomial

namespace EisensteinCriterionOQ01OQ03OQ02

variable (p : ℕ) [hp : Fact p.Prime]

/-- The translate `Φ_p(X + 1)`, viewed over `ℤ`. -/
noncomputable def shiftedCyclotomicInt : ℤ[X] := (cyclotomic p ℤ).comp (X + 1)

omit hp in
/-- `Φ_p(X + 1)` is monic. -/
theorem shiftedCyclotomicInt_monic : (shiftedCyclotomicInt p).Monic := by
  have hmX : (X + 1 : ℤ[X]).Monic := by
    rw [show (X + 1 : ℤ[X]) = X + C 1 by simp]; exact monic_X_add_C 1
  refine (cyclotomic.monic p ℤ).comp hmX ?_
  rw [show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C]
  exact one_ne_zero

/-- `Φ_p(X + 1)` has degree `p − 1`. -/
theorem shiftedCyclotomicInt_natDegree : (shiftedCyclotomicInt p).natDegree = p - 1 := by
  rw [shiftedCyclotomicInt, natDegree_comp, natDegree_cyclotomic,
    show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one,
    Nat.totient_prime hp.out]

/-- **Irreducibility of `Φ_p` over `ℚ`, via Eisenstein at `Φ_p(X + 1)`.**

The Eisenstein data for `Φ_p(X + 1)` is fed into the parent entry's reproved criterion
`irreducible_rat_of_eisenstein`, and the resulting irreducibility of `Φ_p(X + 1)` is
transported back to `Φ_p` along the translation automorphism `X ↦ X + 1`. -/
theorem cyclotomic_prime_irreducible_rat :
    Irreducible (cyclotomic p ℚ) := by
  -- The Eisenstein-at-`p` data for `Φ_p(X + 1) : ℤ[X]`.
  have hEis : (shiftedCyclotomicInt p).IsEisensteinAt (Submodule.span ℤ {(p : ℤ)}) :=
    cyclotomic_comp_X_add_one_isEisensteinAt p
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
  -- Repackage `IsEisensteinAt` into the divisibility hypotheses the parent expects.
  have hmonic : (shiftedCyclotomicInt p).Monic := shiftedCyclotomicInt_monic p
  have hdeg : 0 < (shiftedCyclotomicInt p).natDegree := by
    rw [shiftedCyclotomicInt_natDegree]; exact Nat.sub_pos_of_lt hp.out.one_lt
  have hlow : ∀ k < (shiftedCyclotomicInt p).natDegree, (p : ℤ) ∣ (shiftedCyclotomicInt p).coeff k := by
    intro k hk
    have hmem := hEis.mem hk
    rwa [Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hmem
  have hconst : ¬ ((p : ℤ) ^ 2 ∣ (shiftedCyclotomicInt p).coeff 0) := by
    intro hdvd
    refine hEis.notMem ?_
    rw [Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hdvd
  -- Apply the parent's reproved Eisenstein criterion over ℚ.
  have hirr_rat : Irreducible ((shiftedCyclotomicInt p).map (algebraMap ℤ ℚ)) :=
    EisensteinCriterionOQ01OQ03.irreducible_rat_of_eisenstein hpZ hmonic hdeg hlow hconst
  -- `Φ_p(X + 1)` over ℤ maps to `Φ_p(X + 1)` over ℚ.
  have hmap : (shiftedCyclotomicInt p).map (algebraMap ℤ ℚ) = (cyclotomic p ℚ).comp (X + 1) := by
    rw [shiftedCyclotomicInt, Polynomial.map_comp, map_cyclotomic, Polynomial.map_add,
      map_X, Polynomial.map_one]
  rw [hmap] at hirr_rat
  -- Descend from `Φ_p(X + 1)` to `Φ_p` along the translation automorphism `X ↦ X + 1`.
  have key : algEquivAevalXAddC (1 : ℚ) (cyclotomic p ℚ) = (cyclotomic p ℚ).comp (X + 1) := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval, C_1]
  exact (MulEquiv.irreducible_iff (f := algEquivAevalXAddC (1 : ℚ))).mp (key ▸ hirr_rat)

end EisensteinCriterionOQ01OQ03OQ02
