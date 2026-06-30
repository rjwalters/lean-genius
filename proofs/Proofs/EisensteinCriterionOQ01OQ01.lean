/-
  Irreducibility of the p-th cyclotomic polynomial Φ_p via Eisenstein at X + 1.

  This is a child of `EisensteinCriterionOQ01`, which packages Eisenstein's
  irreducibility criterion (`irreducible_of_eisenstein`) and the `Xⁿ − p`
  family.  Here we carry out the *classical* derivation of the irreducibility
  of the p-th cyclotomic polynomial

      Φ_p(X) = 1 + X + X² + … + X^{p−1}        (p prime)

  by applying that criterion to the SHIFTED polynomial Φ_p(X + 1).

  **The mechanism.**  From the geometric-sum identity `Φ_p · (X − 1) = X^p − 1`
  one gets, after substituting `X ↦ X + 1`,

      Φ_p(X + 1) · X = (X + 1)^p − 1.

  Reading off coefficients (`coeff_mul_X`, `coeff_X_add_one_pow`) gives the
  exact shape

      Φ_p(X + 1) = ∑_{j=0}^{p−1} C(p, j+1) · X^j,        i.e.  coeff j = C(p, j+1).

  The Eisenstein hypotheses at the prime `p` then read off the binomial
  coefficients:

    * leading coefficient `C(p, p) = 1 ∉ (p)`             (Φ_p(X+1) is monic),
    * every lower coefficient `C(p, k)` with `1 ≤ k ≤ p−1` lies in `(p)`
      (`Nat.Prime.dvd_choose_self`),
    * the constant term `C(p, 1) = p ∉ (p²)`              (else `p ∣ 1`).

  Eisenstein gives irreducibility of `Φ_p(X + 1)`, and since `X ↦ X + 1` is a
  ring automorphism of `ℤ[X]` (`Polynomial.algEquivAevalXAddC`), irreducibility
  transfers back to `Φ_p` itself.

  Note: Mathlib already proves `Polynomial.cyclotomic.irreducible` for *all* `n`,
  but by an entirely different route (the minimal polynomial of a primitive root
  / Galois theory).  The elementary Eisenstein argument formalized here for the
  prime case is the textbook proof and is independent of that machinery.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib
import Proofs.EisensteinCriterionOQ01

open Polynomial

namespace EisensteinCriterionOQ01OQ01

variable {p : ℕ}

/-! ### The shifted cyclotomic polynomial `Φ_p(X + 1)` -/

/-- **Substitution identity.** `Φ_p(X + 1) · X = (X + 1)^p − 1`.

This is the geometric-sum identity `Φ_p · (X − 1) = X^p − 1` pushed through the
ring homomorphism `f ↦ f.comp (X + 1)`, noting `(X − 1)(X + 1) ↦ X`. -/
theorem cyclotomic_comp_X_add_one_mul_X (hp : p.Prime) :
    (cyclotomic p ℤ).comp (X + C 1) * X = (X + C 1) ^ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := cyclotomic_prime_mul_X_sub_one ℤ p
  have hc := congrArg (fun q : ℤ[X] => q.comp (X + C 1)) h
  simp only [mul_comp, sub_comp, pow_comp, X_comp, one_comp] at hc
  -- `(X - 1).comp (X + C 1) = X`, `(X^p - 1).comp (X + C 1) = (X + C 1)^p - 1`
  simpa [C_1, add_sub_cancel_right] using hc

/-- **Coefficient formula.** The `j`-th coefficient of `Φ_p(X + 1)` is the
binomial coefficient `C(p, j + 1)`. -/
theorem coeff_cyclotomic_comp_X_add_one (hp : p.Prime) (j : ℕ) :
    ((cyclotomic p ℤ).comp (X + C 1)).coeff j = (p.choose (j + 1) : ℤ) := by
  have hX := cyclotomic_comp_X_add_one_mul_X hp
  have h2 := congrArg (fun q : ℤ[X] => q.coeff (j + 1)) hX
  simp only [coeff_mul_X] at h2
  rw [h2, coeff_sub, C_1, coeff_X_add_one_pow]
  simp [coeff_one]

/-! ### Irreducibility of `Φ_p` over `ℤ` -/

/-- **Irreducibility of the p-th cyclotomic polynomial over `ℤ`**, proved by
applying Eisenstein's criterion (from the parent file) to `Φ_p(X + 1)`. -/
theorem irreducible_cyclotomic_prime (hp : p.Prime) :
    Irreducible (cyclotomic p ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set g : ℤ[X] := (cyclotomic p ℤ).comp (X + C 1) with hg
  -- `g` is monic of degree `p − 1`.
  have hmonic : g.Monic := (cyclotomic.monic p ℤ).comp_X_add_C 1
  have hndeg : g.natDegree = p - 1 := by
    rw [hg, natDegree_comp, natDegree_X_add_C, mul_one, natDegree_cyclotomic,
      Nat.totient_prime hp]
  have hdeg_val : g.degree = (p - 1 : ℕ) := by
    rw [degree_eq_natDegree hmonic.ne_zero, hndeg]
  -- The Eisenstein ideal `P = (p)`.
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP_def
  have hPprime : P.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  -- Leading coefficient `1 ∉ (p)`.
  have hlead : g.leadingCoeff ∉ P := by
    rw [hmonic.leadingCoeff, hP_def, Ideal.mem_span_singleton]
    intro hdvd
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdvd)
  -- All lower coefficients lie in `(p)`.
  have hlow : ∀ k : ℕ, (k : WithBot ℕ) < g.degree → g.coeff k ∈ P := by
    intro k hk
    rw [hdeg_val] at hk
    have hk' : k < p - 1 := by exact_mod_cast hk
    rw [coeff_cyclotomic_comp_X_add_one hp, hP_def, Ideal.mem_span_singleton]
    have hkp : k + 1 < p := by omega
    have hdvd : (p : ℕ) ∣ p.choose (k + 1) := hp.dvd_choose_self (Nat.succ_ne_zero k) hkp
    exact_mod_cast hdvd
  -- Degree is positive.
  have hdeg : 0 < g.degree := by
    rw [← natDegree_pos_iff_degree_pos, hndeg]
    have := hp.two_le; omega
  -- Constant term `C(p,1) = p ∉ (p²)`.
  have hconst : g.coeff 0 ∉ P ^ 2 := by
    have hc0 : g.coeff 0 = (p : ℤ) := by
      rw [coeff_cyclotomic_comp_X_add_one hp]; simp [Nat.choose_one_right]
    rw [hc0, hP_def, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    -- `p² ∣ p` would force `p² ≤ p`, impossible for `p > 1`.
    have hp2 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hle := Int.le_of_dvd hp2 hdvd
    nlinarith [hle, (by exact_mod_cast hp.one_lt : (1 : ℤ) < p)]
  -- Eisenstein gives irreducibility of `g = Φ_p(X + 1)`.
  have hg_irred : Irreducible g :=
    EisensteinCriterionOQ01.irreducible_of_eisenstein hPprime hlead hlow hdeg hconst
      hmonic.isPrimitive
  -- Transfer back along the automorphism `X ↦ X + 1`.
  have hgeq : (algEquivAevalXAddC (1 : ℤ)) (cyclotomic p ℤ) = g := by
    rw [hg, algEquivAevalXAddC_apply, ← comp_eq_aeval]
  rw [← hgeq] at hg_irred
  exact (MulEquiv.irreducible_iff
    (f := (algEquivAevalXAddC (1 : ℤ)).toMulEquiv)).mp hg_irred

/-! ### Corollaries -/

/-- The degree of `Φ_p` is `p − 1`. -/
theorem natDegree_cyclotomic_prime (hp : p.Prime) :
    (cyclotomic p ℤ).natDegree = p - 1 := by
  rw [natDegree_cyclotomic, Nat.totient_prime hp]

/-- **Irreducibility over `ℚ`.** Since `Φ_p` is monic (hence primitive) over `ℤ`,
Gauss's lemma upgrades irreducibility over `ℤ` to irreducibility over `ℚ`. -/
theorem irreducible_cyclotomic_prime_rat (hp : p.Prime) :
    Irreducible (cyclotomic p ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmap : (cyclotomic p ℤ).map (Int.castRingHom ℚ) = cyclotomic p ℚ :=
    map_cyclotomic_int p ℚ
  rw [← hmap]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (cyclotomic.isPrimitive p ℤ)).mp (irreducible_cyclotomic_prime hp)

end EisensteinCriterionOQ01OQ01
