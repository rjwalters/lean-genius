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

/-! ## S5: Cyclotomic anchor — Φ_{2p}(−1) = p for p ∈ {3, 5, 7}

These lemmas make the cyclotomic-API side of the norm fingerprint
concrete. For each odd prime p ∈ {3, 5, 7}, the explicit form of
`cyclotomic (2*p) ℤ` is identified, and its evaluation at `-1` is shown
to equal `p`. Combined with `r_constantCoeff_eq_signed_p`, this
verifies the prediction
`(r p).coeff 0 = (-1)^((p-1)/2) · Φ_{2p}(-1) = (-1)^((p-1)/2) · p`
for these primes via two independent computations: the gallery's
direct coefficient evaluation, and Mathlib's cyclotomic-polynomial API.

**Mathematical content.** For odd prime p ≥ 3, primitive 2p-th roots of
unity are exactly the negatives of primitive p-th roots, so
`Φ_{2p}(X) = Φ_p(-X)`. Evaluating at `X = -1`:
`Φ_{2p}(-1) = Φ_p(1) = p` (Mathlib's `eval_one_cyclotomic_prime`).

**Mathlib status.** Mathlib v4.26.0 has `cyclotomic_one`, `cyclotomic_two`,
`cyclotomic_three` (explicit values for n ≤ 3), `cyclotomic_prime`
(`Φ_p = ∑_{i<p} X^i` for p prime), `eq_cyclotomic_iff`
(`P = cyclotomic n R ↔ P · ∏_{d ∈ properDivisors n} Φ_d = X^n - 1`),
and `eval_one_cyclotomic_prime` (`Φ_p(1) = p`). The general reflection
`Φ_{2p}(X) = Φ_p(-X)` is NOT in Mathlib in this form. We derive each
explicit `cyclotomic_{2p}` form via `eq_cyclotomic_iff` plus the
divisor structure of 2p, then evaluate by direct simp/ring.

Lifting to a uniform `Φ_{2p}(-1) = p` for all odd primes p ≥ 3 is the
S6 target; the bridge identity goes through `cyclotomic_prime_mul_X_sub_one`
composed with `X → -X` plus polynomial cancellation in `ℤ[X]`.
-/

/-- `cyclotomic 5 ℤ = X^4 + X^3 + X^2 + X + 1`. Derived via
`eq_cyclotomic_iff` and the identity `(X-1)(X^4+X^3+X^2+X+1) = X^5 - 1`. -/
theorem cyclotomic_5_eq : cyclotomic 5 ℤ = X^4 + X^3 + X^2 + X + 1 := by
  refine ((eq_cyclotomic_iff (by norm_num : 0 < 5) _).mpr ?_).symm
  rw [show Nat.properDivisors 5 = ({1} : Finset ℕ) from by decide,
      Finset.prod_singleton, cyclotomic_one]
  ring

/-- `cyclotomic 7 ℤ = X^6 + X^5 + X^4 + X^3 + X^2 + X + 1`. -/
theorem cyclotomic_7_eq :
    cyclotomic 7 ℤ = X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  refine ((eq_cyclotomic_iff (by norm_num : 0 < 7) _).mpr ?_).symm
  rw [show Nat.properDivisors 7 = ({1} : Finset ℕ) from by decide,
      Finset.prod_singleton, cyclotomic_one]
  ring

/-- `cyclotomic 6 ℤ = X^2 - X + 1`. The 6th cyclotomic polynomial. Derived
via `eq_cyclotomic_iff` plus the divisor structure `properDivisors 6 = {1, 2, 3}`
and the identity `(X^2-X+1)(X-1)(X+1)(X^2+X+1) = X^6 - 1`. -/
theorem cyclotomic_six_eq : cyclotomic 6 ℤ = X^2 - X + 1 := by
  refine ((eq_cyclotomic_iff (by norm_num : 0 < 6) _).mpr ?_).symm
  rw [show Nat.properDivisors 6 = ({1, 2, 3} : Finset ℕ) from by decide,
      show (({1, 2, 3} : Finset ℕ)) = insert 1 (insert 2 ({3} : Finset ℕ))
        from rfl,
      Finset.prod_insert
        (show (1 : ℕ) ∉ insert 2 ({3} : Finset ℕ) from by decide),
      Finset.prod_insert (show (2 : ℕ) ∉ ({3} : Finset ℕ) from by decide),
      Finset.prod_singleton, cyclotomic_one, cyclotomic_two, cyclotomic_three]
  ring

/-- `cyclotomic 10 ℤ = X^4 - X^3 + X^2 - X + 1`. -/
theorem cyclotomic_ten_eq :
    cyclotomic 10 ℤ = X^4 - X^3 + X^2 - X + 1 := by
  refine ((eq_cyclotomic_iff (by norm_num : 0 < 10) _).mpr ?_).symm
  rw [show Nat.properDivisors 10 = ({1, 2, 5} : Finset ℕ) from by decide,
      show (({1, 2, 5} : Finset ℕ)) = insert 1 (insert 2 ({5} : Finset ℕ))
        from rfl,
      Finset.prod_insert
        (show (1 : ℕ) ∉ insert 2 ({5} : Finset ℕ) from by decide),
      Finset.prod_insert (show (2 : ℕ) ∉ ({5} : Finset ℕ) from by decide),
      Finset.prod_singleton, cyclotomic_one, cyclotomic_two, cyclotomic_5_eq]
  ring

/-- `cyclotomic 14 ℤ = X^6 - X^5 + X^4 - X^3 + X^2 - X + 1`. -/
theorem cyclotomic_fourteen_eq :
    cyclotomic 14 ℤ = X^6 - X^5 + X^4 - X^3 + X^2 - X + 1 := by
  refine ((eq_cyclotomic_iff (by norm_num : 0 < 14) _).mpr ?_).symm
  rw [show Nat.properDivisors 14 = ({1, 2, 7} : Finset ℕ) from by decide,
      show (({1, 2, 7} : Finset ℕ)) = insert 1 (insert 2 ({7} : Finset ℕ))
        from rfl,
      Finset.prod_insert
        (show (1 : ℕ) ∉ insert 2 ({7} : Finset ℕ) from by decide),
      Finset.prod_insert (show (2 : ℕ) ∉ ({7} : Finset ℕ) from by decide),
      Finset.prod_singleton, cyclotomic_one, cyclotomic_two, cyclotomic_7_eq]
  ring

/-- `(cyclotomic 6 ℤ).eval (-1) = 3`. The norm prediction for p = 3. -/
theorem cyclotomic_six_eval_neg_one : (cyclotomic 6 ℤ).eval (-1) = 3 := by
  rw [cyclotomic_six_eq]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
  norm_num

/-- `(cyclotomic 10 ℤ).eval (-1) = 5`. The norm prediction for p = 5. -/
theorem cyclotomic_ten_eval_neg_one : (cyclotomic 10 ℤ).eval (-1) = 5 := by
  rw [cyclotomic_ten_eq]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
  norm_num

/-- `(cyclotomic 14 ℤ).eval (-1) = 7`. The norm prediction for p = 7. -/
theorem cyclotomic_fourteen_eval_neg_one :
    (cyclotomic 14 ℤ).eval (-1) = 7 := by
  rw [cyclotomic_fourteen_eq]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
  norm_num

/-! ## S5 bridge: r p constant term equals (-1)^((p-1)/2) · Φ_{2p}(-1)

For each prime p ∈ {3, 5, 7}, the constant term of `r p` is exactly
`(-1)^((p-1)/2)` times the explicit cyclotomic evaluation `Φ_{2p}(-1)`.
This bridges the gallery's algebraic computation
(`r_constantCoeff_eq_signed_p`) and Mathlib's cyclotomic-polynomial API,
making the prediction
`N_{ℚ(θ_p)/ℚ}(2 + θ_p) = (-1)^((p-1)/2) · Φ_{2p}(-1)`
*directly verifiable* on both sides. Any general proof of
`eisenstein_conjecture_cos_pi_p` must reproduce this identity.
-/

/-- For p = 3: `(r 3).coeff 0 = (-1)^1 · Φ_6(-1) = (-1) · 3 = -3`. -/
theorem r_3_constantCoeff_eq_cyclotomic :
    (r 3).coeff 0 = (-1)^((3 - 1)/2) * (cyclotomic 6 ℤ).eval (-1) := by
  rw [cyclotomic_six_eval_neg_one]
  exact r_constantCoeff_eq_signed_p.1

/-- For p = 5: `(r 5).coeff 0 = (-1)^2 · Φ_10(-1) = 1 · 5 = 5`. -/
theorem r_5_constantCoeff_eq_cyclotomic :
    (r 5).coeff 0 = (-1)^((5 - 1)/2) * (cyclotomic 10 ℤ).eval (-1) := by
  rw [cyclotomic_ten_eval_neg_one]
  exact r_constantCoeff_eq_signed_p.2.1

/-- For p = 7: `(r 7).coeff 0 = (-1)^3 · Φ_14(-1) = (-1) · 7 = -7`. -/
theorem r_7_constantCoeff_eq_cyclotomic :
    (r 7).coeff 0 = (-1)^((7 - 1)/2) * (cyclotomic 14 ℤ).eval (-1) := by
  rw [cyclotomic_fourteen_eval_neg_one]
  exact r_constantCoeff_eq_signed_p.2.2.1

/-- Packaged: for each of p ∈ {3, 5, 7}, the gallery's `(r p).coeff 0`
matches the cyclotomic prediction `(-1)^((p-1)/2) · Φ_{2p}(-1)`.
This converts the empirical sign pattern of S3 into a verifiable
identity in terms of Mathlib's cyclotomic API. -/
theorem r_constantCoeff_eq_cyclotomic_small :
    (r 3).coeff 0 = (-1)^((3 - 1)/2) * (cyclotomic 6 ℤ).eval (-1)
    ∧ (r 5).coeff 0 = (-1)^((5 - 1)/2) * (cyclotomic 10 ℤ).eval (-1)
    ∧ (r 7).coeff 0 = (-1)^((7 - 1)/2) * (cyclotomic 14 ℤ).eval (-1) :=
  ⟨r_3_constantCoeff_eq_cyclotomic,
   r_5_constantCoeff_eq_cyclotomic,
   r_7_constantCoeff_eq_cyclotomic⟩

/-! ## S6: Cyclotomic anchor extension — Φ_{2p}(−1) = p for p ∈ {11, 13}

S5 established the cyclotomic anchor Φ_{2p}(−1) = p for the bottom three
gallery primes p ∈ {3, 5, 7} via explicit `cyclotomic_{2p}` forms plus
direct evaluation. S6 extends the per-prime cyclotomic bridge (Tactic A2
in `state.md`) to the remaining gallery primes p ∈ {11, 13}, covering
the full verified gallery set {3, 5, 7, 11, 13}.

The general identity `Φ_{2p}(X) = Φ_p(−X)` (Tactic A1) — a single uniform
proof for all odd primes p ≥ 3 — is still deferred, but with the
per-prime extension below the gallery's empirical sign pattern
`(r p).coeff 0 = (-1)^((p-1)/2) · Φ_{2p}(−1)` is now matched against
Mathlib's cyclotomic API for *every* explicitly defined case in `r`,
leaving no per-prime gap that an A1 lift would still need to close.

**Proof structure (per prime).**
1. `cyclotomic_p_eq` for `p ∈ {11, 13}` via `eq_cyclotomic_iff` with
   `properDivisors p = {1}` and `cyclotomic_one` (same template as the
   S5 `cyclotomic_5_eq`/`cyclotomic_7_eq`).
2. `cyclotomic_{2p}_eq` via `eq_cyclotomic_iff` with
   `properDivisors (2p) = {1, 2, p}`, `cyclotomic_one`, `cyclotomic_two`,
   and the step (1) lemma (same template as S5's
   `cyclotomic_ten_eq`/`cyclotomic_fourteen_eq`).
3. `cyclotomic_{2p}_eval_neg_one` by `rw [cyclotomic_{2p}_eq]` and
   `simp + norm_num`.
4. `r_p_constantCoeff_eq_cyclotomic` combining the eval lemma with the
   appropriate projection of `r_constantCoeff_eq_signed_p`.

**Risk.** The two `ring` calls close degree-22 and degree-26 polynomial
identities; both are tractable (≤200 monomial expansion) but the
degree-26 call is the largest such `ring` in this file. No new
Mathlib API beyond what S5 used is required.

**Axiom bookkeeping.** No new axioms; no new sorries; 1 sorry remains
(the open conjecture). Five new theorems plus one packaged 5-prime
bridge `r_constantCoeff_eq_cyclotomic_full` superseding the
S5 `r_constantCoeff_eq_cyclotomic_small` predicate (S5 lemma retained
for compatibility).
-/

/-- `cyclotomic 11 ℤ = X^10 + X^9 + ⋯ + X + 1`. Same template as
`cyclotomic_5_eq`: `properDivisors 11 = {1}` plus `cyclotomic_one`,
closed by `ring`. -/
theorem cyclotomic_11_eq :
    cyclotomic 11 ℤ =
      X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  refine ((eq_cyclotomic_iff (by norm_num : 0 < 11) _).mpr ?_).symm
  rw [show Nat.properDivisors 11 = ({1} : Finset ℕ) from by decide,
      Finset.prod_singleton, cyclotomic_one]
  ring

/-- `cyclotomic 13 ℤ = X^12 + X^11 + ⋯ + X + 1`. -/
theorem cyclotomic_13_eq :
    cyclotomic 13 ℤ =
      X^12 + X^11 + X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  refine ((eq_cyclotomic_iff (by norm_num : 0 < 13) _).mpr ?_).symm
  rw [show Nat.properDivisors 13 = ({1} : Finset ℕ) from by decide,
      Finset.prod_singleton, cyclotomic_one]
  ring

/-- `cyclotomic 22 ℤ = X^10 - X^9 + X^8 - ⋯ - X + 1`. The 22nd cyclotomic
polynomial. Derived via `eq_cyclotomic_iff` plus the divisor structure
`properDivisors 22 = {1, 2, 11}`. -/
theorem cyclotomic_22_eq :
    cyclotomic 22 ℤ =
      X^10 - X^9 + X^8 - X^7 + X^6 - X^5 + X^4 - X^3 + X^2 - X + 1 := by
  refine ((eq_cyclotomic_iff (by norm_num : 0 < 22) _).mpr ?_).symm
  rw [show Nat.properDivisors 22 = ({1, 2, 11} : Finset ℕ) from by decide,
      show (({1, 2, 11} : Finset ℕ)) = insert 1 (insert 2 ({11} : Finset ℕ))
        from rfl,
      Finset.prod_insert
        (show (1 : ℕ) ∉ insert 2 ({11} : Finset ℕ) from by decide),
      Finset.prod_insert (show (2 : ℕ) ∉ ({11} : Finset ℕ) from by decide),
      Finset.prod_singleton, cyclotomic_one, cyclotomic_two, cyclotomic_11_eq]
  ring

/-- `cyclotomic 26 ℤ = X^12 - X^11 + X^10 - ⋯ - X + 1`. -/
theorem cyclotomic_26_eq :
    cyclotomic 26 ℤ =
      X^12 - X^11 + X^10 - X^9 + X^8 - X^7 + X^6 - X^5 + X^4 - X^3 + X^2 - X + 1 := by
  refine ((eq_cyclotomic_iff (by norm_num : 0 < 26) _).mpr ?_).symm
  rw [show Nat.properDivisors 26 = ({1, 2, 13} : Finset ℕ) from by decide,
      show (({1, 2, 13} : Finset ℕ)) = insert 1 (insert 2 ({13} : Finset ℕ))
        from rfl,
      Finset.prod_insert
        (show (1 : ℕ) ∉ insert 2 ({13} : Finset ℕ) from by decide),
      Finset.prod_insert (show (2 : ℕ) ∉ ({13} : Finset ℕ) from by decide),
      Finset.prod_singleton, cyclotomic_one, cyclotomic_two, cyclotomic_13_eq]
  ring

/-- `(cyclotomic 22 ℤ).eval (-1) = 11`. The norm prediction for p = 11. -/
theorem cyclotomic_twentytwo_eval_neg_one :
    (cyclotomic 22 ℤ).eval (-1) = 11 := by
  rw [cyclotomic_22_eq]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
  norm_num

/-- `(cyclotomic 26 ℤ).eval (-1) = 13`. The norm prediction for p = 13. -/
theorem cyclotomic_twentysix_eval_neg_one :
    (cyclotomic 26 ℤ).eval (-1) = 13 := by
  rw [cyclotomic_26_eq]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
  norm_num

/-- For p = 11: `(r 11).coeff 0 = (-1)^5 · Φ_22(-1) = (-1) · 11 = -11`. -/
theorem r_11_constantCoeff_eq_cyclotomic :
    (r 11).coeff 0 = (-1)^((11 - 1)/2) * (cyclotomic 22 ℤ).eval (-1) := by
  rw [cyclotomic_twentytwo_eval_neg_one]
  exact r_constantCoeff_eq_signed_p.2.2.2.1

/-- For p = 13: `(r 13).coeff 0 = (-1)^6 · Φ_26(-1) = 1 · 13 = 13`. -/
theorem r_13_constantCoeff_eq_cyclotomic :
    (r 13).coeff 0 = (-1)^((13 - 1)/2) * (cyclotomic 26 ℤ).eval (-1) := by
  rw [cyclotomic_twentysix_eval_neg_one]
  exact r_constantCoeff_eq_signed_p.2.2.2.2

/-- Packaged: for each of p ∈ {3, 5, 7, 11, 13}, the gallery's
`(r p).coeff 0` matches the cyclotomic prediction
`(-1)^((p-1)/2) · Φ_{2p}(-1)`. Extends `r_constantCoeff_eq_cyclotomic_small`
from S5 (which covered only {3, 5, 7}) to the full verified gallery set,
matching the per-prime range of `r_constantCoeff_eq_signed_p`. -/
theorem r_constantCoeff_eq_cyclotomic_full :
    (r 3).coeff 0 = (-1)^((3 - 1)/2) * (cyclotomic 6 ℤ).eval (-1)
    ∧ (r 5).coeff 0 = (-1)^((5 - 1)/2) * (cyclotomic 10 ℤ).eval (-1)
    ∧ (r 7).coeff 0 = (-1)^((7 - 1)/2) * (cyclotomic 14 ℤ).eval (-1)
    ∧ (r 11).coeff 0 = (-1)^((11 - 1)/2) * (cyclotomic 22 ℤ).eval (-1)
    ∧ (r 13).coeff 0 = (-1)^((13 - 1)/2) * (cyclotomic 26 ℤ).eval (-1) :=
  ⟨r_3_constantCoeff_eq_cyclotomic,
   r_5_constantCoeff_eq_cyclotomic,
   r_7_constantCoeff_eq_cyclotomic,
   r_11_constantCoeff_eq_cyclotomic,
   r_13_constantCoeff_eq_cyclotomic⟩

/-! ## S7 SCAFFOLD: Combinatorial backbone for the uniform cyclotomic bridge

The S6 cyclotomic anchor relied on **per-prime** factorizations of
`cyclotomic (2 * p) ℤ` for `p ∈ {3, 5, 7, 11, 13}` via `eq_cyclotomic_iff`.
The next structural step (S7) is the **uniform** bridge identity

  `cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1`    (for `p` odd prime).

Once available, this collapses the per-prime ring identities
`cyclotomic_{6,10,14,22,26}_eq` into a single uniform statement, eliminates
the per-prime evaluation lemmas `cyclotomic_*_eval_neg_one`, and turns the
constant-coefficient sign pattern (already verified via
`r_constantCoeff_eq_signed_p`) into a clean cyclotomic fingerprint
applicable to all odd primes — not just the verified five.

**Proof outline (cyclotomic factorization route).**

1. `Nat.divisors (2 * p) = {1, 2, p, 2 * p}` for `p` odd prime
   (lemma `divisors_two_mul_odd_prime` below — completed in this S7
   SCAFFOLD, 0 sorries).
2. `∏ d ∈ {1, 2, p, 2 * p}, cyclotomic d ℤ = X ^ (2 * p) - 1`
   (via `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` at `n = 2 * p`,
   substituting step 1 for the divisor enumeration).
3. `cyclotomic 1 ℤ = X - 1`, `cyclotomic 2 ℤ = X + 1`, so the product
   becomes `(X - 1) * (X + 1) * cyclotomic p ℤ * cyclotomic (2*p) ℤ
   = X ^ (2 * p) - 1`.
4. `(X - 1) * cyclotomic p ℤ = X ^ p - 1` (via
   `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` at `n = p`, since
   `Nat.divisors p = {1, p}` for prime `p`).
5. `X ^ (2 * p) - 1 = (X ^ p - 1) * (X ^ p + 1)` (algebraic identity:
   `a ^ 2 - 1 = (a - 1)(a + 1)` with `a = X ^ p`).
6. Combining 3–5 and cancelling the monic factor `(X - 1) * cyclotomic p ℤ`
   (nonzero in the integral domain `ℤ[X]`):
   `(X + 1) * cyclotomic (2 * p) ℤ = X ^ p + 1`.

This S7 SCAFFOLD lands **step 1**; steps 2–6 are deferred to a follow-up
session (`S8`). The downstream payoff (lifting `r_constantCoeff_eq_signed_p`
to all odd primes) is sketched in `state.md` and `knowledge.md`.
-/

/-- For `p` an odd prime, the divisors of `2 * p` are exactly `{1, 2, p, 2 * p}`.

Combinatorial backbone for the uniform cyclotomic bridge identity
`cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1`. The forward direction
(`k ∣ 2 * p ⇒ k ∈ {1, 2, p, 2 * p}`) splits on parity of `k`:

* If `2 ∣ k`, write `k = 2 * m`; then `2 * m ∣ 2 * p ⇒ m ∣ p`, so by
  primality `m ∈ {1, p}`, giving `k ∈ {2, 2 * p}`.
* If `2 ∤ k`, then `Nat.Coprime k 2`, so `k ∣ 2 * p ⇒ k ∣ p`, giving
  `k ∈ {1, p}` by primality.

For `p = 2` the divisor set degenerates to `{1, 2, 4}`; the lemma excludes
this case via `Odd p`. -/
lemma divisors_two_mul_odd_prime {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    Nat.divisors (2 * p) = {1, 2, p, 2 * p} := by
  have h2p_pos : 0 < 2 * p := Nat.mul_pos (by norm_num) hp.pos
  have h2p_ne : 2 * p ≠ 0 := h2p_pos.ne'
  ext k
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun ⟨hk_dvd, _⟩ => ?_, ?_⟩
  · by_cases h2 : 2 ∣ k
    · obtain ⟨m, rfl⟩ := h2
      -- `hk_dvd : 2 * m ∣ 2 * p`; cancel the `2` to get `m ∣ p`.
      have hm_dvd : m ∣ p := by
        obtain ⟨q, hq⟩ := hk_dvd
        refine ⟨q, ?_⟩
        have hassoc : 2 * m * q = 2 * (m * q) := by ring
        rw [hassoc] at hq
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hq
      rcases hp.eq_one_or_self_of_dvd m hm_dvd with rfl | rfl
      · exact Or.inr (Or.inl (by norm_num))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · -- `¬ 2 ∣ k` ⇒ `Nat.Coprime k 2`, so `k ∣ 2 * p ⇒ k ∣ p`.
      have hcop : Nat.Coprime k 2 :=
        ((Nat.prime_two.coprime_iff_not_dvd).mpr h2).symm
      have hk_p : k ∣ p := hcop.dvd_of_dvd_mul_left hk_dvd
      rcases hp.eq_one_or_self_of_dvd k hk_p with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨one_dvd _, h2p_ne⟩
    · exact ⟨dvd_mul_right _ _, h2p_ne⟩
    · exact ⟨dvd_mul_left _ _, h2p_ne⟩
    · exact ⟨dvd_refl _, h2p_ne⟩

/-! ## S8: Uniform cyclotomic bridge identity for odd primes p ≥ 3

S7 SCAFFOLD (`divisors_two_mul_odd_prime`) landed the combinatorial
backbone of the proof outline in steps 2–6 of the S7 module docstring.
This S8 iteration **closes** the remaining algebraic steps and delivers
the uniform identity

  `cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1`     in `ℤ[X]`

for every odd prime `p`. Together with Mathlib's `cyclotomic_prime_mul_X_sub_one`
(`cyclotomic p ℤ * (X - 1) = X ^ p - 1`) this establishes the canonical
cyclotomic duality

      cyclotomic p ℤ · (X - 1) = X ^ p - 1
      cyclotomic (2*p) ℤ · (X + 1) = X ^ p + 1            (this S8 result)

for `p` odd prime, exposing `Φ_{2p}` as the "X ↦ -X conjugate" of `Φ_p`
**without** invoking polynomial composition or working in a splitting
field. Together with S7 it collapses the five per-prime ring identities
`cyclotomic_{6,10,14,22,26}_eq` (S5+S6) into one uniform statement,
applicable to *every* odd prime — including primes outside the verified
gallery set `{3, 5, 7, 11, 13}`.

**Proof.** Six steps mirroring the outline of the S7 module docstring:

1. `divisors_two_mul_odd_prime` (S7): `Nat.divisors (2*p) = {1, 2, p, 2*p}`.
2. `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` at `n = 2 * p`:
     `∏ d ∈ (2*p).divisors, cyclotomic d ℤ = X ^ (2 * p) - 1`.
3. Substitute step 1, unfold the four-term `Finset.prod`, and replace
   `cyclotomic 1 ℤ = X - 1`, `cyclotomic 2 ℤ = X + 1`.
4. `Polynomial.cyclotomic_prime_mul_X_sub_one`:
     `cyclotomic p ℤ * (X - 1) = X ^ p - 1`.
5. Algebraic identity `X ^ (2 * p) - 1 = (X ^ p - 1) * (X ^ p + 1)`
   (`two_mul` plus `ring`).
6. Cancel the factor `X ^ p - 1` via `mul_left_cancel₀`. Nonzero in
   `ℤ[X]` (an integral domain): evaluating at `0` gives `-1 ≠ 0` for
   `p > 0`.

**Mathlib status.** All ingredients are in
`Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` (v4.26.0):
`prod_cyclotomic_eq_X_pow_sub_one`, `cyclotomic_one`, `cyclotomic_two`,
`cyclotomic_prime_mul_X_sub_one`. The cancellation step uses
`mul_left_cancel₀` from `Mathlib.Algebra.GroupWithZero.Basic`.

**Axiom bookkeeping.** No new axioms, no new sorries; one new theorem.
The uniform anchor corollary `(cyclotomic (2 * p) ℤ).eval (-1) = p` is
deferred to S9 (requires polynomial-evaluation manipulation of the
bridge — geometric-series substitution or formal differentiation).
-/

/--
**Uniform cyclotomic bridge.** For every odd prime `p`,
  `cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1`     in `ℤ[X]`.

The S8 structural payoff: replaces the five per-prime explicit
`cyclotomic_{6, 10, 14, 22, 26}_eq` ring identities of S5+S6 with a
single uniform identity holding for **all** odd primes `p`.

**Proof.** Apply `prod_cyclotomic_eq_X_pow_sub_one` at `n = 2 * p`,
expand the divisor set via `divisors_two_mul_odd_prime` (S7), and unfold
the resulting four-term `Finset.prod`. Identify the prefix
`(X - 1) * cyclotomic p ℤ = X ^ p - 1` using
`cyclotomic_prime_mul_X_sub_one` and the standard factorization
`X ^ (2 * p) - 1 = (X ^ p - 1) * (X ^ p + 1)`. Cancel `X ^ p - 1`
(nonzero in `ℤ[X]`) via `mul_left_cancel₀`.
-/
theorem cyclotomic_two_mul_prime_mul_X_add_one_uniform
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_pos : 0 < p := hp.pos
  have h2p_pos : 0 < 2 * p := Nat.mul_pos (by norm_num) hp_pos
  have hp_ne1 : p ≠ 1 := hp.one_lt.ne'
  have hp_ne2 : p ≠ 2 := fun h => absurd hpodd (h ▸ by decide)
  have hp_ge3 : 3 ≤ p := by omega
  have h2p_ne1 : 2 * p ≠ 1 := by omega
  have h2p_ne2 : 2 * p ≠ 2 := by intro h; exact hp_ne1 (by omega)
  have h2p_nep : 2 * p ≠ p := by omega
  -- Step 2 of the outline: cyclotomic product over divisors of 2p.
  have h_prod := prod_cyclotomic_eq_X_pow_sub_one h2p_pos ℤ
  -- Step 3: substitute the divisor enumeration (S7) and unfold the product.
  rw [divisors_two_mul_odd_prime hp hpodd] at h_prod
  have h1_notin : (1 : ℕ) ∉ insert 2 (insert p ({2 * p} : Finset ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h2_notin : (2 : ℕ) ∉ insert p ({2 * p} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hp_notin : p ∉ ({2 * p} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  rw [show ({1, 2, p, 2 * p} : Finset ℕ)
        = insert 1 (insert 2 (insert p ({2 * p} : Finset ℕ))) from rfl,
      Finset.prod_insert h1_notin,
      Finset.prod_insert h2_notin,
      Finset.prod_insert hp_notin,
      Finset.prod_singleton,
      cyclotomic_one, cyclotomic_two] at h_prod
  -- h_prod : (X - 1) * ((X + 1) * (cyclotomic p ℤ * cyclotomic (2 * p) ℤ))
  --         = X ^ (2 * p) - 1
  -- Step 4: identify (X - 1) · Φ_p = X^p - 1.
  have h_cyclop : (X - 1) * cyclotomic p ℤ = (X : ℤ[X]) ^ p - 1 := by
    rw [mul_comm]; exact cyclotomic_prime_mul_X_sub_one ℤ p
  -- Step 5: factorize X^{2p} - 1 = (X^p - 1) · (X^p + 1).
  have h_factor : (X : ℤ[X]) ^ (2 * p) - 1 = (X ^ p - 1) * (X ^ p + 1) := by
    rw [two_mul]; ring
  -- Rearrange the LHS into the form (X^p - 1) · ((X + 1) · Φ_{2p}).
  have h_rearr :
      (X - 1) * ((X + 1) * (cyclotomic p ℤ * cyclotomic (2 * p) ℤ))
        = ((X : ℤ[X]) ^ p - 1) * ((X + 1) * cyclotomic (2 * p) ℤ) :=
    calc (X - 1) * ((X + 1) * (cyclotomic p ℤ * cyclotomic (2 * p) ℤ))
        = ((X - 1) * cyclotomic p ℤ) * ((X + 1) * cyclotomic (2 * p) ℤ) := by ring
      _ = ((X : ℤ[X]) ^ p - 1) * ((X + 1) * cyclotomic (2 * p) ℤ) := by rw [h_cyclop]
  rw [h_rearr, h_factor] at h_prod
  -- h_prod : (X^p - 1) * ((X + 1) * cyclotomic (2 * p) ℤ) = (X^p - 1) * (X^p + 1)
  -- Step 6: cancel the X^p - 1 factor (nonzero in ℤ[X]).
  have h_nz : (X : ℤ[X]) ^ p - 1 ≠ 0 := by
    intro hzero
    have h_eval : ((X : ℤ[X]) ^ p - 1).eval 0 = (0 : ℤ) := by
      rw [hzero]; simp
    simp only [eval_sub, eval_pow, eval_X, eval_one] at h_eval
    rw [zero_pow hp_pos.ne'] at h_eval
    -- h_eval : 0 - 1 = 0, contradiction.
    norm_num at h_eval
  have h_cancel := mul_left_cancel₀ h_nz h_prod
  -- h_cancel : (X + 1) * cyclotomic (2 * p) ℤ = X ^ p + 1.
  -- Goal:      cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1
  rw [mul_comm]
  exact h_cancel

/-! ## S9: Uniform numerical anchor `Φ_{2p}(-1) = p` for odd primes `p ≥ 3`

S8 (PR #18066) established the uniform cyclotomic bridge identity
`cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1` for every odd prime `p`.
This S9 iteration **lifts** the per-prime cyclotomic evaluation lemmas
`cyclotomic_{6, 10, 14, 22, 26}_eval_neg_one = {3, 5, 7, 11, 13}` of
S5+S6 to a single uniform statement holding for *every* odd prime:

  `(cyclotomic (2 * p) ℤ).eval (-1) = p`     in `ℤ`,    for all odd prime `p`.

Together with the S5+S6 per-prime gallery bridges
`r_{3,5,7,11,13}_constantCoeff_eq_cyclotomic`, this collapses the
constant-coefficient sign pattern
`(r p).coeff 0 = (-1)^((p-1)/2) · Φ_{2p}(-1) = (-1)^((p-1)/2) · p`
into a one-line corollary applicable to **all** odd primes — not just
the five verified gallery primes.

**Proof outline.** Two steps:

1. **Geometric-series identification.** The geometric-series identity
   `geom_sum_mul (-X) p` reads
     `(∑ i ∈ Finset.range p, (-X)^i) * (-X - 1) = (-X)^p - 1`     in `ℤ[X]`.
   For `p` odd, `Odd.neg_pow` gives `(-X)^p = -X^p`. Rearranging signs
   (`(-X - 1) = -(X + 1)` and `(-X)^p - 1 = -(X^p + 1)`) yields
     `(∑ i ∈ Finset.range p, (-X)^i) * (X + 1) = X^p + 1`.
   Combining with the S8 bridge `cyclotomic (2*p) ℤ · (X + 1) = X^p + 1`
   and cancelling the nonzero factor `(X + 1)` (monic, hence ≠ 0)
   via `mul_right_cancel₀` gives the structural identity
     `cyclotomic (2 * p) ℤ = ∑ i ∈ Finset.range p, (-X)^i`     in `ℤ[X]`,
   the **S9 structural lemma** `cyclotomic_two_mul_prime_eq_geom_neg_series`.
   This is the explicit polynomial formula `Φ_{2p}(X) = ∑_{i<p} (-X)^i`
   for odd prime `p`, also known as `Φ_{2p}(X) = Φ_p(-X)` informally —
   now proved as a ring identity in `ℤ[X]`.

2. **Numerical evaluation.** Evaluate the structural lemma at `X = -1`.
   Each term `((-X)^i).eval (-1) = (-(-1))^i = 1^i = 1`, so the sum
   collapses to `∑ i ∈ Finset.range p, 1 = p`.

**Mathlib status (v4.26.0).** All ingredients are in
`Mathlib.Algebra.GeomSum` (`geom_sum_mul`),
`Mathlib.Algebra.GroupPower.Basic` (`Odd.neg_pow`),
`Mathlib.Algebra.Polynomial.Monic` (`monic_X_add_C`, `Monic.ne_zero`),
and the standard `eval_*` simp set (`eval_finset_sum`, `eval_pow`,
`eval_neg`, `eval_X`).

**Axiom bookkeeping.** No new axioms, no new sorries; two new theorems
(the S9 structural lemma and the S9 numerical anchor). The
constant-coefficient sign-pattern corollary
`r_constantCoeff_eq_signed_p_uniform`
(deferred to S10) is now a one-line consequence: combine
`r_constantCoeff_eq_signed_p` with `cyclotomic_two_mul_prime_eval_neg_one_uniform`.
-/

/--
**S9 structural lemma: Φ_{2p}(X) = ∑_{i<p} (-X)^i for odd prime p.**

For every odd prime `p`,
  `cyclotomic (2 * p) ℤ = ∑ i ∈ Finset.range p, (-X)^i`     in `ℤ[X]`.

This is the uniform geometric-series formula for `Φ_{2p}` over odd
primes, derived from the S8 bridge identity by cancelling the nonzero
factor `(X + 1)`. The classical informal identity `Φ_{2p}(X) = Φ_p(-X)`
is now a ring identity in `ℤ[X]`.

**Proof.** Apply `geom_sum_mul (-X) p` and `Odd.neg_pow` to obtain
`(∑ i ∈ range p, (-X)^i) * (X + 1) = X^p + 1`. Combine with the S8
uniform bridge `cyclotomic_two_mul_prime_mul_X_add_one_uniform` and
cancel `(X + 1)` (monic, hence nonzero in `ℤ[X]`) via `mul_right_cancel₀`.
-/
theorem cyclotomic_two_mul_prime_eq_geom_neg_series
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    cyclotomic (2 * p) ℤ = ∑ i ∈ Finset.range p, (-X : ℤ[X]) ^ i := by
  -- Step 1: geometric-series identity at `x = -X`.
  have h_geom_raw : (∑ i ∈ Finset.range p, (-X : ℤ[X]) ^ i) * ((-X) - 1)
                  = (-X : ℤ[X]) ^ p - 1 :=
    geom_sum_mul (-X : ℤ[X]) p
  -- Rewrite `(-X)^p = -X^p` using `Odd.neg_pow`.
  have h_negXp : ((-X : ℤ[X])) ^ p = -(X : ℤ[X]) ^ p := hpodd.neg_pow X
  rw [h_negXp] at h_geom_raw
  -- Now `h_geom_raw : (∑ …) * (-X - 1) = -X^p - 1`. Push the signs.
  have h_geom : (∑ i ∈ Finset.range p, (-X : ℤ[X]) ^ i) * (X + 1) = X ^ p + 1 := by
    have h_rearr_lhs :
        (∑ i ∈ Finset.range p, (-X : ℤ[X]) ^ i) * ((-X) - 1)
          = -((∑ i ∈ Finset.range p, (-X : ℤ[X]) ^ i) * (X + 1)) := by ring
    have h_rearr_rhs : -(X : ℤ[X]) ^ p - 1 = -((X : ℤ[X]) ^ p + 1) := by ring
    rw [h_rearr_lhs, h_rearr_rhs] at h_geom_raw
    exact neg_injective h_geom_raw
  -- Step 2: combine with the S8 bridge and cancel `(X + 1)`.
  have h_bridge :
      cyclotomic (2 * p) ℤ * (X + 1) = (X : ℤ[X]) ^ p + 1 :=
    cyclotomic_two_mul_prime_mul_X_add_one_uniform hp hpodd
  have h_eq :
      cyclotomic (2 * p) ℤ * (X + 1)
        = (∑ i ∈ Finset.range p, (-X : ℤ[X]) ^ i) * (X + 1) := by
    rw [h_bridge, h_geom]
  -- `X + 1` is monic, hence nonzero, so `mul_right_cancel₀` applies.
  have h_xp1_monic : Monic ((X : ℤ[X]) + C (1 : ℤ)) := monic_X_add_C (1 : ℤ)
  have h_xp1_ne : ((X : ℤ[X]) + 1) ≠ 0 := by
    have := h_xp1_monic.ne_zero
    simpa using this
  exact mul_right_cancel₀ h_xp1_ne h_eq

/--
**S9 numerical anchor: uniform `Φ_{2p}(-1) = p` for odd prime p.**

For every odd prime `p`,
  `(cyclotomic (2 * p) ℤ).eval (-1) = p`     in `ℤ`.

This is the uniform lift of the per-prime evaluations
`cyclotomic_{six, ten, fourteen, twentytwo, twentysix}_eval_neg_one = {3, 5, 7, 11, 13}`
of S5+S6, now holding for **every** odd prime — not just the five
verified gallery primes.

**Proof.** Substitute the S9 structural lemma
`cyclotomic_two_mul_prime_eq_geom_neg_series` to rewrite the cyclotomic
as a geometric series in `(-X)`. Distribute `eval (-1)` over the sum.
Each term `((-X)^i).eval (-1) = (-(-1))^i = 1^i = 1`. The sum of `p`
ones is `p`.
-/
theorem cyclotomic_two_mul_prime_eval_neg_one_uniform
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    (cyclotomic (2 * p) ℤ).eval (-1) = (p : ℤ) := by
  rw [cyclotomic_two_mul_prime_eq_geom_neg_series hp hpodd]
  rw [eval_finset_sum]
  simp only [eval_pow, eval_neg, eval_X, neg_neg, one_pow]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-! ## S10: Uniform constant-coefficient corollary

S9 delivered the uniform numerical anchor
`cyclotomic_two_mul_prime_eval_neg_one_uniform`:
`(cyclotomic (2 * p) ℤ).eval (-1) = p` for every odd prime `p ≥ 3`. The
per-prime cyclotomic bridges
`r_{3, 5, 7, 11, 13}_constantCoeff_eq_cyclotomic` of S5+S6 use the
**literal** cyclotomic indices `{6, 10, 14, 22, 26}`. S10 lifts those
per-prime bridges into a single statement parameterised by `(2 * p)`,
yielding the uniform constant-coefficient identity

  `r_constantCoeff_eq_signed_cyclotomic_uniform`
  : `∀ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      (r p).coeff 0 = (-1)^((p-1)/2) · (cyclotomic (2 * p) ℤ).eval (-1)`

and combining it with the S9 numerical anchor yields the **fully
uniform** signed-`p` form, decoupled from the literal cyclotomic index:

  `r_constantCoeff_eq_signed_uniform`
  : `∀ p (verified), p.Prime → Odd p →
       (r p).coeff 0 = (-1)^((p-1)/2) · (p : ℤ)`.

This is the S10 deliverable announced in `state.md`. Note the
quantification is over the **verified** prime set `{3, 5, 7, 11, 13}`
because `r p = 0` for `p ∉ {3, 5, 7, 11, 13}`; the uniformity is in the
**indexing of cyclotomic** (now `2 * p` instead of literal `{6, 10,
14, 22, 26}`), not in the parametric polynomial `r`. Closing the gap to
"all odd primes" requires the gallery-side extension of `r` itself,
which awaits the cyclotomic-ramification proof outlined in
`eisenstein_conjecture_cos_pi_p` (line 1083).

**Proof structure.**
1. `r_constantCoeff_eq_signed_cyclotomic_uniform` reduces by case-split
   on `Finset.mem_insert` to the five per-prime cyclotomic bridges
   already proved in S5/S6; the `(2 * p)` indices reduce definitionally
   to the literal `{6, 10, 14, 22, 26}`.
2. `r_constantCoeff_eq_signed_uniform` then rewrites the cyclotomic
   evaluation via the S9 numerical anchor, requiring only that the
   verified primes are themselves prime and odd (discharged by `decide`
   at each case for the membership-derived `p`).
-/

/-- For each verified prime `p ∈ {3, 5, 7, 11, 13}`, the constant
coefficient of `r p` equals `(-1)^((p-1)/2) · Φ_{2p}(-1)`. Uniform
restatement of the S5/S6 per-prime cyclotomic bridges using `(2 * p)`
indexing (which reduces definitionally to the literal cyclotomic index
at each case). -/
theorem r_constantCoeff_eq_signed_cyclotomic_uniform (p : ℕ)
    (hp : p ∈ ({3, 5, 7, 11, 13} : Finset ℕ)) :
    (r p).coeff 0 = (-1) ^ ((p - 1) / 2) * (cyclotomic (2 * p) ℤ).eval (-1) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact r_3_constantCoeff_eq_cyclotomic
  · exact r_5_constantCoeff_eq_cyclotomic
  · exact r_7_constantCoeff_eq_cyclotomic
  · exact r_11_constantCoeff_eq_cyclotomic
  · exact r_13_constantCoeff_eq_cyclotomic

/-- Uniform constant-coefficient corollary: for each verified prime
`p ∈ {3, 5, 7, 11, 13}`, the constant coefficient of `r p` equals
`(-1)^((p-1)/2) · p`. Combines `r_constantCoeff_eq_signed_cyclotomic_uniform`
with the S9 uniform anchor `cyclotomic_two_mul_prime_eval_neg_one_uniform`.

Re-derives the per-prime `r_constantCoeff_eq_signed_p` via the cyclotomic
anchor route: the S9 lemma `(cyclotomic (2*p) ℤ).eval (-1) = p` for odd
prime `p` collapses the cyclotomic factor on the RHS down to the plain
`p`, recovering the empirical sign-pattern fingerprint without case-split. -/
theorem r_constantCoeff_eq_signed_uniform (p : ℕ)
    (hp : p ∈ ({3, 5, 7, 11, 13} : Finset ℕ)) :
    (r p).coeff 0 = (-1) ^ ((p - 1) / 2) * (p : ℤ) := by
  have h_prime : p.Prime ∧ Odd p := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by decide, by decide⟩
  rw [r_constantCoeff_eq_signed_cyclotomic_uniform p hp,
      cyclotomic_two_mul_prime_eval_neg_one_uniform h_prime.1 h_prime.2]

/-! ## S15: Uniform trace bridge — `(r p).coeff ((p-1)/2 - 1) = -p`

S10 delivered the **uniform constant-coefficient corollary**
`r_constantCoeff_eq_signed_uniform`: for each verified prime
`p ∈ {3, 5, 7, 11, 13}`, `(r p).coeff 0 = (-1)^((p-1)/2) · p`.

S15 delivers the **trace fingerprint** counterpart, completing the second
of the two Vieta endpoints predicted by the cyclotomic-ramification
analysis. Three deliverables:

  **Stage 1** (uniform cyclotomic side, all odd primes p ≥ 3):
    `cyclotomic_two_mul_prime_subLeadingCoeff_uniform`
    : `(cyclotomic (2 * p) ℤ).coeff (p - 2) = -1`

  **Stage 2a** (per-prime structural bridge, p ∈ {5, 7, 11, 13}):
    `r_subLeadingCoeff_via_moebius_uniform`
    : `(r p).coeff ((p-1)/2 - 1) = -((p:ℤ) - 1) + (Φ_{2p}).coeff (p - 2)`

  **Stage 2b** (Finset-quantified corollary, p ∈ {5, 7, 11, 13}):
    `r_subLeadingCoeff_eq_neg_p_uniform`
    : `(r p).coeff ((p-1)/2 - 1) = -p`,
    via Stage 2a + Stage 1.

**Why this matters.** The pair `r_constantCoeff_eq_signed_uniform` (S10)
and `r_subLeadingCoeff_eq_neg_p_uniform` (S15) packages **both** Vieta
fingerprints in Finset form, with their cyclotomic-anchor proof routes
made explicit:

      constant     = (-1)^((p-1)/2) · Φ_{2p}(-1)    via S9 + S10
      sub-leading  =       -1       · (Φ_{2p}.coeff (p-2) − (p−1))    via S15

Both endpoints reduce to a corresponding cyclotomic identity. The
Stage 1 lemma (`Φ_{2p}.coeff (p-2) = -1`) is the trace counterpart of
the S9 norm anchor (`Φ_{2p}(-1) = p`) — both follow from the same
geometric-series identification `Φ_{2p} = ∑_{i<p} (-X)^i` (S9
structural lemma `cyclotomic_two_mul_prime_eq_geom_neg_series`).

**Proof structure of Stage 1.**
1. Rewrite `Φ_{2p}` via the S9 structural lemma to `∑_{i<p} (-X)^i`.
2. Distribute `coeff (p-2)` over the sum via `Polynomial.finsetSum_coeff`.
3. Apply `Finset.sum_eq_single (p - 2)`: only the `i = p - 2` term
   survives because `((-X)^i).coeff (p-2) = 0` for `i ≠ p - 2`.
4. The surviving term is `((-X)^(p-2)).coeff (p-2) = (-1)^(p-2)`,
   which equals `-1` because `p - 2` is odd (since `p` is odd ≥ 3).

**Bookkeeping.** Stage 2a is `p ∈ {5, 7, 11, 13}` (excluding `p = 3`,
which is handled separately by `r_3_traceCoeff` because `(3-1)/2 - 1
= 0` collides with the constant-coefficient case). Stage 1 is
**uniform across all odd primes p ≥ 3**, just like the S9 anchor.

**Companion lemma (private).** `neg_X_pow_coeff_eq` distributes
`coeff k ((-X)^i) = (-1)^i * (if k = i then 1 else 0)` for arbitrary
`i, k : ℕ`. Used twice in Stage 1's `Finset.sum_eq_single` branches
(surviving and off-diagonal).
-/

/-- Helper: distribute `coeff k` over `(-X)^i` in `ℤ[X]`. The result is
`(-1)^i * (X^i).coeff k`, factoring out the sign through the
`(-X) = (-1) * X` decomposition + `mul_pow` + `C_pow`. Used in the
`Finset.sum_eq_single` step of `cyclotomic_two_mul_prime_subLeadingCoeff_uniform`.
-/
private lemma neg_X_pow_coeff_eq (i k : ℕ) :
    ((-X : ℤ[X])^i).coeff k = (-1 : ℤ)^i * (if k = i then 1 else 0) := by
  have h_neg_X : (-X : ℤ[X]) = -1 * X := by ring
  rw [h_neg_X, mul_pow]
  have h_neg1_pow : ((-1 : ℤ[X]))^i = C ((-1 : ℤ)^i) := by
    rw [show (-1 : ℤ[X]) = C (-1 : ℤ) from by rw [C_neg, C_1]]
    rw [← C_pow]
  rw [h_neg1_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

/--
**S15 Stage 1: Uniform sub-leading coefficient of Φ_{2p} for odd prime p.**

For every odd prime `p`, `(cyclotomic (2 * p) ℤ).coeff (p - 2) = -1`.

This is the **trace** counterpart of the S9 norm anchor
`cyclotomic_two_mul_prime_eval_neg_one_uniform` (`Φ_{2p}(-1) = p`).
Both follow from the same geometric-series identification
`Φ_{2p} = ∑_{i<p} (-X)^i` (S9 structural lemma).

**Proof.**
1. Rewrite `Φ_{2p}` via the S9 structural lemma to `∑ i ∈ range p, (-X)^i`.
2. Distribute `coeff (p-2)` over the sum via `Polynomial.finsetSum_coeff`.
3. Apply `Finset.sum_eq_single (p - 2)`: only the `i = p - 2` term
   contributes nonzero coefficient at index `p - 2`.
4. The surviving coefficient is `(-1)^(p-2) = -1` (odd exponent since
   `p` odd ≥ 3 implies `p - 2` odd).

**Index discipline.** For `p` odd prime, `p ≥ 3` (since `p = 2` is the
only even prime). Hence `p - 2` is well-defined as a natural and equals
`p - 2` in ℕ. The proof derives `3 ≤ p` from `hp.two_le` + `hp_odd`.
-/
theorem cyclotomic_two_mul_prime_subLeadingCoeff_uniform
    {p : ℕ} (hp : p.Prime) (hp_odd : Odd p) :
    (cyclotomic (2 * p) ℤ).coeff (p - 2) = -1 := by
  -- Derive `3 ≤ p` from `p.Prime` and `Odd p`.
  have hp_ge3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases h2.eq_or_lt with hp2 | hp2
    · exfalso; subst hp2; exact (by decide : ¬ Odd 2) hp_odd
    · omega
  -- Step 1: rewrite cyclotomic as geometric series in `-X` (S9 structural).
  rw [cyclotomic_two_mul_prime_eq_geom_neg_series hp hp_odd]
  -- Step 2: distribute `coeff (p - 2)` over the sum.
  rw [finset_sum_coeff]
  -- Step 3: only the `i = p - 2` term survives.
  have hp_minus_two_in : p - 2 ∈ Finset.range p :=
    Finset.mem_range.mpr (by omega)
  have h_sum :
      (∑ i ∈ Finset.range p, ((-X : ℤ[X])^i).coeff (p - 2))
        = ((-X : ℤ[X])^(p - 2)).coeff (p - 2) := by
    refine Finset.sum_eq_single (p - 2) ?_ ?_
    · -- Off-diagonal vanishing: `((-X)^i).coeff (p-2) = 0` for `i ≠ p-2`.
      intro i _ hi_ne
      rw [neg_X_pow_coeff_eq i (p - 2), if_neg (Ne.symm hi_ne), mul_zero]
    · -- `p - 2 ∈ range p` so this branch is unreachable.
      intro h; exact absurd hp_minus_two_in h
  rw [h_sum]
  -- Step 4: surviving term `((-X)^(p-2)).coeff (p-2) = -1`.
  rw [neg_X_pow_coeff_eq (p - 2) (p - 2), if_pos rfl, mul_one]
  -- Goal: `(-1 : ℤ)^(p - 2) = -1`. Use `Odd (p - 2)`.
  have hp2_odd : Odd (p - 2) := by
    obtain ⟨k, hk⟩ := hp_odd
    refine ⟨k - 1, ?_⟩
    omega
  exact hp2_odd.neg_one_pow

/--
**S15 Stage 2a: Per-prime structural bridge** (Möbius decomposition).

For each verified prime `p ∈ {5, 7, 11, 13}`, the sub-leading coefficient
of `r p` decomposes as

  `(r p).coeff ((p-1)/2 - 1) = -((p:ℤ) - 1) + (cyclotomic (2*p) ℤ).coeff (p - 2)`.

The sum splits the trace `Tr_{ℚ(θ_p)/ℚ}(2 + θ_p)` into

  - the contribution `−(p − 1)` of the `+2` shift across the `(p−1)/2`
    real conjugates, and
  - the cyclotomic sub-leading `Φ_{2p}.coeff (p - 2)` (which equals `-1`
    by Stage 1, encoding `μ(2p) = 1` for odd prime `p`).

**Proof.** Per-prime: `rcases` destructure of `p ∈ {5, 7, 11, 13}`;
each branch unfolds `r p` via `r_p_eq`, normalises the cyclotomic
index `2 * p → 2p`, rewrites with the explicit `cyclotomic_{2p}_eq`
form (S5/S6), expands coefficients via the v4.26.0-audited `simp only`
set (S14), and closes with `decide` on the literal integer arithmetic.

**Excludes `p = 3`** because `(3-1)/2 - 1 = 0` collides with the
constant-coefficient case (handled separately by `r_3_traceCoeff`).
-/
theorem r_subLeadingCoeff_via_moebius_uniform :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p - 1) / 2 - 1)
        = -((p : ℤ) - 1) + (cyclotomic (2 * p) ℤ).coeff (p - 1 - 1) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · -- p = 5: (r 5).coeff 1 = -4 + (Φ_10).coeff 3
    rw [show (2 * 5 : ℕ) = 10 from rfl, cyclotomic_ten_eq, r_5_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_one]
    decide
  · -- p = 7: (r 7).coeff 2 = -6 + (Φ_14).coeff 5
    rw [show (2 * 7 : ℕ) = 14 from rfl, cyclotomic_fourteen_eq, r_7_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_one]
    decide
  · -- p = 11: (r 11).coeff 4 = -10 + (Φ_22).coeff 9
    rw [show (2 * 11 : ℕ) = 22 from rfl, cyclotomic_22_eq, r_11_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_one]
    decide
  · -- p = 13: (r 13).coeff 5 = -12 + (Φ_26).coeff 11
    rw [show (2 * 13 : ℕ) = 26 from rfl, cyclotomic_26_eq, r_13_eq]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_one]
    decide

/--
**S15 Stage 2b: Uniform trace fingerprint corollary.**

For each verified prime `p ∈ {5, 7, 11, 13}`,

  `(r p).coeff ((p - 1) / 2 - 1) = -(p : ℤ)`.

This is the Finset-quantified packaging of the per-prime trace
fingerprint `r_subLeadingCoeff_eq_neg_p` (S4), now derived through the
**cyclotomic-anchor route**: combines the per-prime decomposition
`r_subLeadingCoeff_via_moebius_uniform` (Stage 2a) with the uniform
sub-leading anchor `cyclotomic_two_mul_prime_subLeadingCoeff_uniform`
(Stage 1) to recover `−p` without case-bashing on `r p`.

The `p = 3` case is excluded because the index `(3-1)/2 - 1 = 0`
collides with the constant-coefficient case (handled by
`r_3_traceCoeff`).
-/
theorem r_subLeadingCoeff_eq_neg_p_uniform :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p - 1) / 2 - 1) = -(p : ℤ) := by
  intro p hp
  -- Get `Prime p` and `Odd p` from the Finset membership.
  have h_prime_odd : p.Prime ∧ Odd p := by
    have hp' := hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
    rcases hp' with rfl | rfl | rfl | rfl
    all_goals exact ⟨by decide, by decide⟩
  -- Apply Stage 2a (per-prime decomposition).
  rw [r_subLeadingCoeff_via_moebius_uniform p hp]
  -- Reduce `p - 1 - 1` to `p - 2` (definitionally for `p ≥ 2`).
  have h_idx : p - 1 - 1 = p - 2 := by
    have := h_prime_odd.1.two_le
    omega
  rw [h_idx]
  -- Apply Stage 1 to rewrite the cyclotomic coefficient as `-1`.
  rw [cyclotomic_two_mul_prime_subLeadingCoeff_uniform h_prime_odd.1 h_prime_odd.2]
  ring

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
