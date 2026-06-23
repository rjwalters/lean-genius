/-
  Irreducibility of the prime-power cyclotomic polynomial Φ_{pᵏ}, via Eisenstein
  at Φ_{pᵏ}(X + 1).

  This file answers the first open question of `eisenstein-criterion-oq-01-oq-03-oq-02`:

    > Extend to prime powers: Mathlib's `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt`
    > supplies the analogous Eisenstein data for Φ_{pᵏ}(X + 1); feed it through the
    > same criterion to obtain irreducibility of Φ_{pᵏ} over ℚ.

  **The argument, verbatim from the prime case.**  For a prime `p` and `k = n + 1 ≥ 1`,
  the cyclotomic polynomial `Φ_{pᵏ}(X)` is monic of degree `φ(pᵏ) = p^{k-1}(p − 1)` but
  is *not* visibly Eisenstein at `p`.  Its translate `Φ_{pᵏ}(X + 1)` *is*: Mathlib's
  `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n` proves
  `((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).IsEisensteinAt (span ℤ {p})`, i.e. it is
  monic, every lower coefficient is divisible by `p`, and its constant coefficient is
  divisible by `p` but not by `p²`.  Eisenstein's criterion therefore makes
  `Φ_{pᵏ}(X + 1)` irreducible over `ℚ`; and since the translation `X ↦ X + 1` is a ring
  automorphism of `ℚ[X]`, `Φ_{pᵏ}` itself is irreducible over `ℚ`.

  **What is reused.**  Exactly as the parent `eisenstein-criterion-oq-01-oq-03-oq-02`
  did for the *prime* index, we feed the Eisenstein data into the grandparent's reproved
  criterion `EisensteinCriterionOQ01OQ03.irreducible_rat_of_eisenstein` (a concrete
  divisibility form of Eisenstein + Gauss's lemma over `ℤ ⊂ ℚ`).  The only change from
  the prime case is the index: `cyclotomic p` becomes `cyclotomic (p ^ (n + 1))`, and the
  Eisenstein input is the prime-*power* lemma rather than the prime one.  The final
  descent from `Φ_{pᵏ}(X + 1)` to `Φ_{pᵏ}` again uses the polynomial automorphism
  `Polynomial.algEquivAevalXAddC` together with `MulEquiv.irreducible_iff`.

  This re-derives `Polynomial.cyclotomic.irreducible_rat` (for prime-power indices)
  through the elementary Eisenstein route rather than invoking it.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib
import Proofs.EisensteinCriterionOQ01OQ03

open Polynomial

namespace EisensteinCriterionOQ01OQ03OQ02OQ01

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

/-- The translate `Φ_{p^{n+1}}(X + 1)`, viewed over `ℤ`. -/
noncomputable def shiftedCyclotomicPrimePowInt : ℤ[X] :=
  (cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)

omit hp in
/-- `Φ_{p^{n+1}}(X + 1)` is monic. -/
theorem shiftedCyclotomicPrimePowInt_monic :
    (shiftedCyclotomicPrimePowInt p n).Monic := by
  have hmX : (X + 1 : ℤ[X]).Monic := by
    rw [show (X + 1 : ℤ[X]) = X + C 1 by simp]; exact monic_X_add_C 1
  refine (cyclotomic.monic (p ^ (n + 1)) ℤ).comp hmX ?_
  rw [show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C]
  exact one_ne_zero

/-- `Φ_{p^{n+1}}(X + 1)` has degree `φ(p^{n+1}) = pⁿ·(p − 1)`. -/
theorem shiftedCyclotomicPrimePowInt_natDegree :
    (shiftedCyclotomicPrimePowInt p n).natDegree = p ^ n * (p - 1) := by
  rw [shiftedCyclotomicPrimePowInt, natDegree_comp, natDegree_cyclotomic,
    show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one,
    Nat.totient_prime_pow_succ hp.out]

/-- **Irreducibility of `Φ_{p^{n+1}}` over `ℚ`, via Eisenstein at `Φ_{p^{n+1}}(X + 1)`.**

The Eisenstein data for `Φ_{p^{n+1}}(X + 1)` (Mathlib's
`cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt`) is fed into the grandparent
entry's reproved criterion `irreducible_rat_of_eisenstein`, and the resulting
irreducibility of `Φ_{p^{n+1}}(X + 1)` is transported back to `Φ_{p^{n+1}}` along the
translation automorphism `X ↦ X + 1`.  This generalises the parent's prime-index result
`cyclotomic_prime_irreducible_rat` to every prime power. -/
theorem cyclotomic_prime_pow_irreducible_rat :
    Irreducible (cyclotomic (p ^ (n + 1)) ℚ) := by
  -- The Eisenstein-at-`p` data for `Φ_{p^{n+1}}(X + 1) : ℤ[X]`.
  have hEis :
      (shiftedCyclotomicPrimePowInt p n).IsEisensteinAt (Submodule.span ℤ {(p : ℤ)}) :=
    cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
  -- Repackage `IsEisensteinAt` into the divisibility hypotheses the criterion expects.
  have hmonic : (shiftedCyclotomicPrimePowInt p n).Monic :=
    shiftedCyclotomicPrimePowInt_monic p n
  have hdeg : 0 < (shiftedCyclotomicPrimePowInt p n).natDegree := by
    rw [shiftedCyclotomicPrimePowInt_natDegree]
    have h1 : 0 < p ^ n := Nat.pos_pow_of_pos n hp.out.pos
    have h2 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
    positivity
  have hlow : ∀ k < (shiftedCyclotomicPrimePowInt p n).natDegree,
      (p : ℤ) ∣ (shiftedCyclotomicPrimePowInt p n).coeff k := by
    intro k hk
    have hmem := hEis.mem hk
    rwa [Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hmem
  have hconst : ¬ ((p : ℤ) ^ 2 ∣ (shiftedCyclotomicPrimePowInt p n).coeff 0) := by
    intro hdvd
    refine hEis.notMem ?_
    rw [Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hdvd
  -- Apply the grandparent's reproved Eisenstein criterion over ℚ.
  have hirr_rat :
      Irreducible ((shiftedCyclotomicPrimePowInt p n).map (algebraMap ℤ ℚ)) :=
    EisensteinCriterionOQ01OQ03.irreducible_rat_of_eisenstein hpZ hmonic hdeg hlow hconst
  -- `Φ_{p^{n+1}}(X + 1)` over ℤ maps to `Φ_{p^{n+1}}(X + 1)` over ℚ.
  have hmap : (shiftedCyclotomicPrimePowInt p n).map (algebraMap ℤ ℚ)
      = (cyclotomic (p ^ (n + 1)) ℚ).comp (X + 1) := by
    rw [shiftedCyclotomicPrimePowInt, Polynomial.map_comp, map_cyclotomic,
      Polynomial.map_add, map_X, Polynomial.map_one]
  rw [hmap] at hirr_rat
  -- Descend from `Φ_{p^{n+1}}(X + 1)` to `Φ_{p^{n+1}}` along the translation `X ↦ X + 1`.
  have key : algEquivAevalXAddC (1 : ℚ) (cyclotomic (p ^ (n + 1)) ℚ)
      = (cyclotomic (p ^ (n + 1)) ℚ).comp (X + 1) := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval, C_1]
  exact (MulEquiv.irreducible_iff (f := algEquivAevalXAddC (1 : ℚ))).mp (key ▸ hirr_rat)

end EisensteinCriterionOQ01OQ03OQ02OQ01
