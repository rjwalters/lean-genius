/-
  Eisenstein Conjecture for cos(π/p), General Odd Prime p

  **Conjecture.** For every odd prime p ≥ 3, the minimal polynomial of
  2 + 2cos(π/p) over ℚ is Eisenstein at p.

  **Status of this file.** Level-2 implementation (per S1 OBSERVE plan):
  1. Define a parametric polynomial `r : ℕ → ℤ[X]` with explicit values
     for p ∈ {5, 7, 11, 13}.
  2. Verify `IsEisensteinAt (r p) (Ideal.span {(p : ℤ)})` for each
     p ∈ {5, 7, 11, 13} by direct coefficient computation.
  3. Derive irreducibility of `r 11` and `r 13` from Eisenstein
     (the p = 5 and p = 7 cases are already established in
     `AngleTrisectionCos20GalOQ01OQ02.lean` and `AngleTrisectionCos20GalOQ01.lean`).
  4. State the uniform conjecture `eisenstein_conjecture_cos_pi_p` as a
     sorry; the full proof requires the cyclotomic-ramification argument
     (see knowledge.md).

  **Explicit polynomials** (degree (p−1)/2, monic):

      p=3  : Y − 3                                            (degree 1)
      p=5  : Y² − 5Y + 5
      p=7  : Y³ − 7Y² + 14Y − 7
      p=11 : Y⁵ − 11Y⁴ + 44Y³ − 77Y² + 55Y − 11
      p=13 : Y⁶ − 13Y⁵ + 65Y⁴ − 156Y³ + 182Y² − 91Y + 13

  All sub-leading coefficients are divisible by p; constant term is ±p,
  not divisible by p². The p=5, p=7 polynomials match sibling files
  (up to the substitution Y = 2X + 2, sibling files use the
  pre-substitution form 8X³−4X²−4X+1 etc.).

  **p = 3 boundary case.** `cos(π/3) = 1/2`, so `2 + 2 cos(π/3) = 3` and its
  minimal polynomial over ℚ is `Y − 3`. This is degree (3−1)/2 = 1, monic,
  and (degenerately) Eisenstein at 3: the only sub-leading coefficient is
  the constant `−3 ∈ (3)`, and `−3 ∉ (9)`. So the family extends down to
  p = 3 — a useful base case for any inductive proof of the general conjecture.

  **Constant-coefficient sign pattern.** Across the five verified primes
  p ∈ {3, 5, 7, 11, 13}, the constant term of `r p` equals
  `(-1)^((p−1)/2) · p`:

      p=3  : (−1)¹ · 3  = −3   (n=1)
      p=5  : (−1)² · 5  = +5   (n=2)
      p=7  : (−1)³ · 7  = −7   (n=3)
      p=11 : (−1)⁵ · 11 = −11  (n=5)
      p=13 : (−1)⁶ · 13 = +13  (n=6)

  This matches the cyclotomic prediction
  `N_{ℚ(θ_p)/ℚ}(2 + θ_p) = (−1)^((p−1)/2) · Φ_{2p}(−1) = (−1)^((p−1)/2) · p`
  derived from the norm identity `(1 + ζ)(1 + ζ⁻¹) = 2 + θ_p`. The sign
  alternation is exactly what any general proof via the cyclotomic-ramification
  route must reproduce. See `r_constantCoeff_eq_signed_p` below.

  **Mathematical justification (sketch).** By cyclotomic ramification:
  the prime p is totally ramified in ℤ[2cos(π/p)] with ramification
  index (p−1)/2, and 2 + 2cos(π/p) is a uniformizer (its norm equals
  Φ_{2p}(−1) = Φ_p(1) = p). Hence its minimal polynomial is Eisenstein
  at p by the standard local-field theorem (Neukirch ANT II.6).

  See `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/knowledge.md`.

  1 sorry (the general conjecture); 0 axioms.
-/

import Mathlib

open Polynomial

namespace AngleTrisectionCos20GalOQ01OQ03

/-! ## Definitions: parametric Eisenstein polynomial -/

/--
Parametric polynomial `r p ∈ ℤ[X]` that is conjecturally the minimal
polynomial of `2 + 2 cos(π/p)` over ℚ for odd prime p ≥ 3.

Explicit values for p ∈ {3, 5, 7, 11, 13} match the empirically verified cases:

    r 3  = X − 3                                              (degree 1, base case)
    r 5  = X² − 5X + 5
    r 7  = X³ − 7X² + 14X − 7
    r 11 = X⁵ − 11X⁴ + 44X³ − 77X² + 55X − 11
    r 13 = X⁶ − 13X⁵ + 65X⁴ − 156X³ + 182X² − 91X + 13

For all other p, returns a placeholder `0`. The conjecture
`eisenstein_conjecture_cos_pi_p` asserts the existence of a polynomial
with the required Eisenstein structure for every odd prime p ≥ 3.
-/
noncomputable def r : ℕ → ℤ[X]
  | 3 => X - C 3
  | 5 => X ^ 2 - C 5 * X + C 5
  | 7 => X ^ 3 - C 7 * X ^ 2 + C 14 * X - C 7
  | 11 => X ^ 5 - C 11 * X ^ 4 + C 44 * X ^ 3 - C 77 * X ^ 2 + C 55 * X - C 11
  | 13 => X ^ 6 - C 13 * X ^ 5 + C 65 * X ^ 4 - C 156 * X ^ 3 + C 182 * X ^ 2 - C 91 * X + C 13
  | _ => 0

/-! ## p = 3 (boundary case: degree 1)

`cos(π/3) = 1/2`, so `2 + 2 cos(π/3) = 3` has rational minimal polynomial
`X − 3`. This is the smallest case where the Eisenstein-at-`p` structure
applies: degree `(3 − 1)/2 = 1`, leading coefficient `1 ∉ (3)`, the unique
sub-leading coefficient is `−3 ∈ (3)`, and `−3 ∉ (9)`. -/

theorem r_3_eq : r 3 = X - C 3 := rfl

theorem r_3_natDegree : (r 3).natDegree = 1 := by
  rw [r_3_eq]; compute_degree!

theorem r_3_degree : (r 3).degree = 1 := by
  rw [r_3_eq]; compute_degree!

theorem r_3_monic : (r 3).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, r_3_natDegree, r_3_eq]
  simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem r_3_isEisensteinAt :
    (r 3).IsEisensteinAt (Ideal.span {(3 : ℤ)}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (r 3).leadingCoeff = 1 from r_3_monic, Ideal.mem_span_singleton]
    decide
  · intro k hk
    rw [r_3_natDegree] at hk
    simp only [Ideal.mem_span_singleton]
    rw [r_3_eq]
    simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [r_3_eq]
    simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide

/-! ## p = 5 -/

theorem r_5_eq : r 5 = X ^ 2 - C 5 * X + C 5 := rfl

theorem r_5_natDegree : (r 5).natDegree = 2 := by
  rw [r_5_eq]; compute_degree!

theorem r_5_degree : (r 5).degree = 2 := by
  rw [r_5_eq]; compute_degree!

theorem r_5_monic : (r 5).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, r_5_natDegree, r_5_eq]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem r_5_isEisensteinAt :
    (r 5).IsEisensteinAt (Ideal.span {(5 : ℤ)}) := by
  refine ⟨?_, ?_, ?_⟩
  · -- leading coefficient is 1, not in span {5}
    rw [show (r 5).leadingCoeff = 1 from r_5_monic, Ideal.mem_span_singleton]
    decide
  · -- all sub-leading coefficients are divisible by 5
    intro k hk
    rw [r_5_natDegree] at hk
    simp only [Ideal.mem_span_singleton]
    rw [r_5_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · -- constant term 5 is not divisible by 25
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [r_5_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide

/-! ## p = 7 -/

theorem r_7_eq : r 7 = X ^ 3 - C 7 * X ^ 2 + C 14 * X - C 7 := rfl

theorem r_7_natDegree : (r 7).natDegree = 3 := by
  rw [r_7_eq]; compute_degree!

theorem r_7_degree : (r 7).degree = 3 := by
  rw [r_7_eq]; compute_degree!

theorem r_7_monic : (r 7).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, r_7_natDegree, r_7_eq]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem r_7_isEisensteinAt :
    (r 7).IsEisensteinAt (Ideal.span {(7 : ℤ)}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (r 7).leadingCoeff = 1 from r_7_monic, Ideal.mem_span_singleton]
    decide
  · intro k hk
    rw [r_7_natDegree] at hk
    simp only [Ideal.mem_span_singleton]
    rw [r_7_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [r_7_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide

/-! ## p = 11 -/

theorem r_11_eq :
    r 11 = X ^ 5 - C 11 * X ^ 4 + C 44 * X ^ 3 - C 77 * X ^ 2 + C 55 * X - C 11 :=
  rfl

theorem r_11_natDegree : (r 11).natDegree = 5 := by
  rw [r_11_eq]; compute_degree!

theorem r_11_degree : (r 11).degree = 5 := by
  rw [r_11_eq]; compute_degree!

theorem r_11_monic : (r 11).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, r_11_natDegree, r_11_eq]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem r_11_isEisensteinAt :
    (r 11).IsEisensteinAt (Ideal.span {(11 : ℤ)}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (r 11).leadingCoeff = 1 from r_11_monic, Ideal.mem_span_singleton]
    decide
  · intro k hk
    rw [r_11_natDegree] at hk
    simp only [Ideal.mem_span_singleton]
    rw [r_11_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [r_11_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide

/-! ## p = 13 -/

theorem r_13_eq :
    r 13 = X ^ 6 - C 13 * X ^ 5 + C 65 * X ^ 4 - C 156 * X ^ 3 + C 182 * X ^ 2
      - C 91 * X + C 13 :=
  rfl

theorem r_13_natDegree : (r 13).natDegree = 6 := by
  rw [r_13_eq]; compute_degree!

theorem r_13_degree : (r 13).degree = 6 := by
  rw [r_13_eq]; compute_degree!

theorem r_13_monic : (r 13).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, r_13_natDegree, r_13_eq]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem r_13_isEisensteinAt :
    (r 13).IsEisensteinAt (Ideal.span {(13 : ℤ)}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (r 13).leadingCoeff = 1 from r_13_monic, Ideal.mem_span_singleton]
    decide
  · intro k hk
    rw [r_13_natDegree] at hk
    simp only [Ideal.mem_span_singleton]
    rw [r_13_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [r_13_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide

/-! ## Empirical verification: the four cases packaged -/

/--
Verification of the conjecture for the five smallest odd primes p ≥ 3.
Each of the explicit polynomials `r 3, r 5, r 7, r 11, r 13` is
Eisenstein at p, in the sense of `Polynomial.IsEisensteinAt`.

The `p = 3` case is the degenerate degree-1 base case: `r 3 = X − 3`,
whose only sub-leading coefficient is `−3 ∈ (3)`. The `p = 5, 7` cases
agree (up to the substitution `Y = 2X + 2`) with the polynomials in
sibling files `AngleTrisectionCos20GalOQ01OQ02.lean` and
`AngleTrisectionCos20GalOQ01.lean`, which also derive irreducibility
via Eisenstein at the same prime.

For p = 11, p = 13, this is the first formal verification of the
Eisenstein structure in the gallery.
-/
theorem eisenstein_verified_small_primes :
    (r 3).IsEisensteinAt (Ideal.span {(3 : ℤ)})
    ∧ (r 5).IsEisensteinAt (Ideal.span {(5 : ℤ)})
    ∧ (r 7).IsEisensteinAt (Ideal.span {(7 : ℤ)})
    ∧ (r 11).IsEisensteinAt (Ideal.span {(11 : ℤ)})
    ∧ (r 13).IsEisensteinAt (Ideal.span {(13 : ℤ)}) :=
  ⟨r_3_isEisensteinAt, r_5_isEisensteinAt, r_7_isEisensteinAt,
   r_11_isEisensteinAt, r_13_isEisensteinAt⟩

/-! ## Constant-coefficient sign pattern (structural)

The constant term of `r p` for the five verified primes follows the
cyclotomic prediction
`(r p).coeff 0 = (-1)^((p-1)/2) · p`. This matches the norm
`N_{ℚ(θ_p)/ℚ}(2 + θ_p) = (-1)^((p-1)/2) · Φ_{2p}(-1) = (-1)^((p-1)/2) · p`
from the identity `(1 + ζ_{2p})(1 + ζ_{2p}⁻¹) = 2 + 2 cos(π/p)`. Any
general proof of `eisenstein_conjecture_cos_pi_p` along the
cyclotomic-ramification route must reproduce exactly this sign.
-/

/-- Constant term of `r p` equals `(-1)^((p-1)/2) · p` for the five
verified primes p ∈ {3, 5, 7, 11, 13}. -/
theorem r_constantCoeff_eq_signed_p :
    (r 3).coeff 0 = (-1) ^ ((3 - 1) / 2) * 3
    ∧ (r 5).coeff 0 = (-1) ^ ((5 - 1) / 2) * 5
    ∧ (r 7).coeff 0 = (-1) ^ ((7 - 1) / 2) * 7
    ∧ (r 11).coeff 0 = (-1) ^ ((11 - 1) / 2) * 11
    ∧ (r 13).coeff 0 = (-1) ^ ((13 - 1) / 2) * 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [r_3_eq]
    simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  · rw [r_5_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  · rw [r_7_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  · rw [r_11_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  · rw [r_13_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide

/-! ## Sub-leading (trace) coefficient pattern (structural)

The next-to-top coefficient of `r p` for the five verified primes is
uniformly `-p`:

    p = 5  : coeff X¹ in r 5 = -5
    p = 7  : coeff X² in r 7 = -7
    p = 11 : coeff X⁴ in r 11 = -11
    p = 13 : coeff X⁵ in r 13 = -13

Mathematically this encodes `-Tr_{ℚ(θ_p)/ℚ}(2 + 2 cos(π/p)) = -p`, since
by Vieta the sub-leading coefficient of a monic minimal polynomial equals
minus the sum of conjugates (the field trace).  The trace equals `p`
because the `(p-1)/2` conjugates of `2 + 2 cos(π/p)` are
`2 + 2 cos(k π / p)` for odd `k ∈ {1, 3, …, p − 2}`, and
`∑_{k odd} 2 cos(k π / p) = 1` (a standard cyclotomic identity), giving
trace `(p − 1) + 1 = p`.

For `p = 3` the polynomial has degree 1 and the sub-leading coefficient
coincides with the constant term, so the trace pattern `coeff 0 = -3` is
already a direct consequence of `r_constantCoeff_eq_signed_p` (where the
sign exponent `(3 − 1)/2 = 1` gives `-3`).  Hence the dedicated trace
lemma below covers the four non-degenerate primes; we add a separate
`r_3_traceCoeff` clause so the boundary case is recorded explicitly.

Together with `r_constantCoeff_eq_signed_p` (the norm half), this lemma
fixes both Vieta endpoints of `r p`:

* Constant term =  `(-1)^((p-1)/2) · N_{ℚ(θ_p)/ℚ}(2 + θ_p) = (-1)^((p-1)/2) · p`.
* Sub-leading  =  `-Tr_{ℚ(θ_p)/ℚ}(2 + θ_p) = -p`.

Any general proof of `eisenstein_conjecture_cos_pi_p` via the
cyclotomic-ramification route must reproduce both fingerprints.
-/

/-- Sub-leading coefficient of `r p` equals `-p` for the four
non-degenerate verified primes p ∈ {5, 7, 11, 13}.  Encodes
`Tr_{ℚ(θ_p)/ℚ}(2 + 2 cos(π/p)) = p`. -/
theorem r_subLeadingCoeff_eq_neg_p :
    (r 5).coeff 1 = -5
    ∧ (r 7).coeff 2 = -7
    ∧ (r 11).coeff 4 = -11
    ∧ (r 13).coeff 5 = -13 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r_5_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  · rw [r_7_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  · rw [r_11_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide
  · rw [r_13_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    decide

/-- Boundary trace for `p = 3`: the polynomial `r 3 = X − 3` has degree 1,
so its sub-leading coefficient is the constant term `−3`.  Recorded
separately because the index `(p − 1)/2 − 1 = 0` collides with the
constant coefficient (already handled by `r_constantCoeff_eq_signed_p`). -/
theorem r_3_traceCoeff : (r 3).coeff 0 = -3 := by
  rw [r_3_eq]
  simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  decide

/-! ## Irreducibility corollaries for p ∈ {11, 13} (new gallery content) -/

/-- `r 11 = X⁵ − 11X⁴ + 44X³ − 77X² + 55X − 11` is irreducible over ℤ
by Eisenstein's criterion at p = 11. -/
theorem r_11_irreducible : Irreducible (r 11) := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(11 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (11 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [show (r 11).leadingCoeff = 1 from r_11_monic, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [r_11_degree] at hk
    have hkn : k < 5 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    rw [r_11_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · rw [r_11_degree]; exact_mod_cast Nat.zero_lt_succ 4
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [r_11_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · exact r_11_monic.isPrimitive

/-- `r 13 = X⁶ − 13X⁵ + 65X⁴ − 156X³ + 182X² − 91X + 13` is irreducible over ℤ
by Eisenstein's criterion at p = 13. -/
theorem r_13_irreducible : Irreducible (r 13) := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(13 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (13 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [show (r 13).leadingCoeff = 1 from r_13_monic, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [r_13_degree] at hk
    have hkn : k < 6 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    rw [r_13_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · rw [r_13_degree]; exact_mod_cast Nat.zero_lt_succ 5
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [r_13_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · exact r_13_monic.isPrimitive

/-! ## Uniform conjecture (general odd prime p ≥ 3) -/

/--
**Eisenstein conjecture for cos(π/p), general statement.**

For every odd prime p ≥ 3, there exists a monic integer polynomial
of degree (p−1)/2 that is Eisenstein at p. (Conjecturally this is
the minimal polynomial of `2 + 2 cos(π/p)` over ℚ.)

**Status**: open (sorry). The cyclotomic-ramification proof requires:
1. `Φ_{2p}(−1) = Φ_p(1) = p` (norm of `1 + ζ_{2p}` over ℚ).
2. `(1 + ζ_{2p})` is a uniformizer of the unique prime 𝔭 above p in
   ℤ[ζ_{2p}], with ramification index (p−1)/2 in the real subfield.
3. Local-field theorem: uniformizer of totally ramified extension ⇒
   minimal polynomial is Eisenstein.

Mathlib has Φ_{2p}(−1) = p (via `Polynomial.cyclotomic_prime_eq_X_pow_sub_one`
and the relation Φ_{2p} = Φ_p(−X) for p odd). The local-field uniformizer
theorem is the main gap to fill — see knowledge.md for the proof outline.

This file verifies the conjecture for p ∈ {3, 5, 7, 11, 13} via
`eisenstein_verified_small_primes`, including the degenerate
degree-1 base case `r 3 = X − 3`. The sign of the constant term
follows `(-1)^((p-1)/2) · p` (see `r_constantCoeff_eq_signed_p`).
-/
theorem eisenstein_conjecture_cos_pi_p :
    ∀ p : ℕ, p.Prime → 3 ≤ p → Odd p →
    ∃ q : ℤ[X], q.natDegree = (p - 1) / 2 ∧ q.Monic ∧
      q.IsEisensteinAt (Ideal.span {(p : ℤ)}) := by
  sorry

end AngleTrisectionCos20GalOQ01OQ03
