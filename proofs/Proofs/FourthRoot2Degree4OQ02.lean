/-
  Fourth Root of 2, Degree 4 — OQ-02:
  The Eisenstein-then-Gauss route, packaged as a reusable lemma for `Xⁿ − p`.

  Open question (generalization) from the gallery proof `fourth-root-2-irrational`
  / `FourthRoot2Degree4`:

      Can the Eisenstein-then-Gauss route here be packaged as a reusable lemma
      for `X^{2^k} − 2` (or `X^{p^k} − p`), filling the even-exponent gap that
      Mathlib's Kummer lemmas mark with TODO comments?

  Mathlib's Kummer-extension API (`Mathlib/FieldTheory/KummerExtension.lean`)
  proves `Xⁿ − a` irreducible only away from the obstructed cases:

    * `X_pow_sub_C_irreducible_of_odd`        — requires `n` **odd**;
    * `X_pow_sub_C_irreducible_of_prime_pow`  — requires the prime `p ≠ 2`.

  Both carry explicit `TODO`s asking to cover `p = 2` / even exponents.  The
  parent file handled exactly one such case (`X⁴ − 2`, `4 = 2²`) by hand.

  This file shows the parent's hand-rolled argument was never special to `2` or
  to `4`: **Eisenstein's criterion at the prime `p` applies verbatim to
  `Xⁿ − p` for every prime `p` and every exponent `n ≥ 1`**, with no parity or
  `p ≠ 2` restriction, because the only facts used are

      `leadingCoeff = 1 ∉ (p)`,  all lower coefficients `∈ (p)`  (they are `0`
      except the constant `−p`),  and  `−p ∉ (p)² = (p²)`  (a prime is not
      divisible by its square).

  Gauss's lemma then descends irreducibility from `ℤ[X]` to `ℚ[X]`.  From the
  single packaged lemma we recover, with no further work:

    * irreducibility of `Xⁿ − p` over `ℤ` and over `ℚ`, all primes, all `n ≥ 1`;
    * the minimal polynomial and field degree of any root: `[ℚ(α):ℚ] = n`
      whenever `αⁿ = p`;
    * the previously TODO-blocked even cases `X² − 2`, `X⁴ − 2`, `X⁸ − 2`,
      `X¹⁶ − 2`, … and `p = 2` cases generally, as one-line corollaries;
    * `[ℚ(√2):ℚ] = 2` and `[ℚ(⁴√2):ℚ] = 4` re-derived from the general degree
      corollary (the parent's bespoke `finrank` proofs collapse to one line).

  Results: 0 axioms, 0 sorries.
-/

import Mathlib

open Polynomial

namespace FourthRoot2Degree4OQ02

/-! ## Part 1: The reusable irreducibility lemma over ℤ

Eisenstein at the prime `p`, packaged uniformly in `p` and `n`. -/

/-- Coefficient description of `Xⁿ − C a` over `ℤ`: index `n` carries the
leading `1`, index `0` carries `−a`, every other index is `0`. -/
private theorem coeff_X_pow_sub_C {n : ℕ} {a : ℤ} (k : ℕ) :
    (X ^ n - C a : ℤ[X]).coeff k
      = (if k = n then (1 : ℤ) else 0) - (if k = 0 then a else 0) := by
  simp only [coeff_sub, coeff_X_pow, coeff_C]

/-- **Reusable Eisenstein lemma.**  For any prime `p : ℤ` and any exponent
`n ≥ 1`, the polynomial `Xⁿ − p` is irreducible over `ℤ`.

This is the parent file's `irreducible_X4_sub_2_int` with the prime `2` replaced
by an arbitrary prime and the exponent `4` replaced by an arbitrary `n ≥ 1`.
No oddness / `p ≠ 2` hypothesis is needed: Eisenstein at `p` only ever uses that
`p` is prime and `p² ∤ p`. -/
theorem irreducible_X_pow_sub_C_int {p : ℤ} (hp : Prime p) {n : ℕ} (hn : 0 < n) :
    Irreducible (X ^ n - C p : ℤ[X]) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hmonic : (X ^ n - C p : ℤ[X]).Monic := monic_X_pow_sub_C _ hn.ne'
  have hlc : (X ^ n - C p : ℤ[X]).leadingCoeff = 1 := hmonic
  have hdeg : (X ^ n - C p : ℤ[X]).degree = n := degree_X_pow_sub_C hn p
  apply irreducible_of_eisenstein_criterion (P := Ideal.span {p})
  · -- (p) is prime
    rw [Ideal.span_singleton_prime hp0]; exact hp
  · -- leadingCoeff 1 ∉ (p)
    rw [hlc, Ideal.mem_span_singleton]
    exact fun h => hp.not_unit (isUnit_of_dvd_one h)
  · -- all coefficients below the top lie in (p)
    intro k hk
    rw [hdeg] at hk
    have hkn : k ≠ n := by
      rintro rfl; exact absurd hk (lt_irrefl _)
    rw [coeff_X_pow_sub_C, if_neg hkn, Ideal.mem_span_singleton]
    apply dvd_sub (dvd_zero p)
    split_ifs
    · exact dvd_refl p
    · exact dvd_zero p
  · -- 0 < degree
    rw [hdeg]; exact_mod_cast hn
  · -- constant term −p ∉ (p)² = (p²)
    rw [coeff_X_pow_sub_C, if_neg (by omega : ¬ (0 = n)), if_pos rfl,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, zero_sub, dvd_neg]
    intro hdvd
    -- p² ∣ p is impossible: pass to natAbs and compare sizes
    have hm : p.natAbs ^ 2 ∣ p.natAbs := by
      have h := Int.natAbs_dvd_natAbs.mpr hdvd
      rwa [Int.natAbs_pow] at h
    have hmp : p.natAbs.Prime := Int.prime_iff_natAbs_prime.mp hp
    have hle := Nat.le_of_dvd hmp.pos hm
    nlinarith [hle, hmp.two_le]
  · -- monic ⇒ primitive
    exact hmonic.isPrimitive

/-! ## Part 2: Descent to ℚ via Gauss's lemma -/

/-- **Reusable lemma over ℚ.**  `Xⁿ − p` is irreducible over `ℚ` for every prime
`p : ℤ` and every `n ≥ 1`.  Gauss's lemma descends the integer result. -/
theorem irreducible_X_pow_sub_C_rat {p : ℤ} (hp : Prime p) {n : ℕ} (hn : 0 < n) :
    Irreducible (X ^ n - C (p : ℚ) : ℚ[X]) := by
  have hprim : (X ^ n - C p : ℤ[X]).IsPrimitive :=
    (monic_X_pow_sub_C _ hn.ne').isPrimitive
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    (irreducible_X_pow_sub_C_int hp hn)
  have hmap : (X ^ n - C p : ℤ[X]).map (Int.castRingHom ℚ) = X ^ n - C (p : ℚ) := by
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, map_X]
  rwa [hmap] at h

/-! ## Part 3: Minimal polynomial and field degree of an arbitrary root

For any `ℚ`-algebra field `L` and any `α : L` with `αⁿ = p`, the minimal
polynomial is `Xⁿ − p` and `[ℚ(α):ℚ] = n`.  This packages the parent's
`minpoly_fr2` / `finrank_adjoin_fr2` so they no longer reprove irreducibility by
hand. -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The root condition `αⁿ = p` makes `Xⁿ − p` vanish at `α`. -/
private theorem aeval_root {a : L} {p : ℤ} {n : ℕ}
    (ha : a ^ n = algebraMap ℚ L (p : ℚ)) :
    (Polynomial.aeval a) (X ^ n - C (p : ℚ)) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, ha, sub_self]

/-- **Minimal polynomial of a root of a prime.**  If `αⁿ = p` (`p` prime,
`n ≥ 1`) then `minpoly ℚ α = Xⁿ − p`. -/
theorem minpoly_eq_X_pow_sub_C {a : L} {p : ℤ} {n : ℕ} (hp : Prime p) (hn : 0 < n)
    (ha : a ^ n = algebraMap ℚ L (p : ℚ)) :
    minpoly ℚ a = X ^ n - C (p : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic
    (irreducible_X_pow_sub_C_rat hp hn) (aeval_root ha)
    (monic_X_pow_sub_C _ hn.ne')).symm

/-- `α` is integral over `ℚ`, witnessed by the monic `Xⁿ − p`. -/
theorem isIntegral_root {a : L} {p : ℤ} {n : ℕ} (hn : 0 < n)
    (ha : a ^ n = algebraMap ℚ L (p : ℚ)) : IsIntegral ℚ a :=
  ⟨X ^ n - C (p : ℚ), monic_X_pow_sub_C _ hn.ne', aeval_root ha⟩

/-- **Field degree of a root of a prime.**  If `αⁿ = p` (`p` prime, `n ≥ 1`)
then `[ℚ(α):ℚ] = n`.  Recovers `finrank_adjoin_fr2 = 4` and
`finrank_adjoin_sqrt2 = 2` from a single statement. -/
theorem finrank_adjoin_eq {a : L} {p : ℤ} {n : ℕ} (hp : Prime p) (hn : 0 < n)
    (ha : a ^ n = algebraMap ℚ L (p : ℚ)) :
    Module.finrank ℚ ℚ⟮a⟯ = n := by
  rw [IntermediateField.adjoin.finrank (isIntegral_root hn ha),
    minpoly_eq_X_pow_sub_C hp hn ha, natDegree_X_pow_sub_C]

/-! ## Part 4: The even-exponent / `p = 2` cases that Mathlib's Kummer API
cannot reach — now one-liners.

`X_pow_sub_C_irreducible_of_odd` needs odd `n`; `X_pow_sub_C_irreducible_of_prime_pow`
needs `p ≠ 2`.  None of the following satisfy those hypotheses, yet each is
immediate from `irreducible_X_pow_sub_C_rat`. -/

/-- `X² − 2` irreducible over ℚ — even exponent, `p = 2`. -/
theorem irreducible_X2_sub_2 : Irreducible (X ^ 2 - C 2 : ℚ[X]) := by
  have := irreducible_X_pow_sub_C_rat (p := 2) Int.prime_two (n := 2) (by norm_num)
  simpa using this

/-- `X⁴ − 2` irreducible over ℚ — recovers the parent's `irreducible_X4_sub_2_rat`.
`4 = 2²`, the exact case both Kummer lemmas miss. -/
theorem irreducible_X4_sub_2 : Irreducible (X ^ 4 - C 2 : ℚ[X]) := by
  have := irreducible_X_pow_sub_C_rat (p := 2) Int.prime_two (n := 4) (by norm_num)
  simpa using this

/-- `X⁸ − 2` irreducible over ℚ — the `X^{2³} − 2` case, `8` even. -/
theorem irreducible_X8_sub_2 : Irreducible (X ^ 8 - C 2 : ℚ[X]) := by
  have := irreducible_X_pow_sub_C_rat (p := 2) Int.prime_two (n := 8) (by norm_num)
  simpa using this

/-- `X¹⁶ − 2` irreducible over ℚ — the `X^{2⁴} − 2` case. -/
theorem irreducible_X16_sub_2 : Irreducible (X ^ 16 - C 2 : ℚ[X]) := by
  have := irreducible_X_pow_sub_C_rat (p := 2) Int.prime_two (n := 16) (by norm_num)
  simpa using this

/-- `X⁴ − 3` irreducible over ℚ — even exponent, odd prime. -/
theorem irreducible_X4_sub_3 : Irreducible (X ^ 4 - C 3 : ℚ[X]) := by
  have := irreducible_X_pow_sub_C_rat (p := 3) (by norm_num) (n := 4) (by norm_num)
  simpa using this

/-- `X⁶ − 7` irreducible over ℚ — even exponent, odd prime. -/
theorem irreducible_X6_sub_7 : Irreducible (X ^ 6 - C 7 : ℚ[X]) := by
  have := irreducible_X_pow_sub_C_rat (p := 7) (by norm_num) (n := 6) (by norm_num)
  simpa using this

/-! ## Part 5: Field-degree corollaries via the real roots, re-deriving the
parent's bespoke results from the general degree lemma. -/

/-- `√2 = algebraMap ℚ ℝ 2` raised appropriately: `(√2)² = 2`. -/
theorem sqrt2_sq : (Real.sqrt 2) ^ 2 = algebraMap ℚ ℝ ((2 : ℤ) : ℚ) := by
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

/-- **`[ℚ(√2):ℚ] = 2`** from the general degree lemma (parent:
`finrank_adjoin_sqrt2`). -/
theorem finrank_adjoin_sqrt2 : Module.finrank ℚ ℚ⟮Real.sqrt 2⟯ = 2 :=
  finrank_adjoin_eq (p := 2) Int.prime_two (n := 2) sqrt2_sq

/-- The real fourth root of `2`, as `√√2`. -/
noncomputable def fr2 : ℝ := Real.sqrt (Real.sqrt 2)

/-- `(⁴√2)⁴ = algebraMap ℚ ℝ 2`. -/
theorem fr2_pow : fr2 ^ 4 = algebraMap ℚ ℝ ((2 : ℤ) : ℚ) := by
  have h : fr2 ^ 4 = (fr2 ^ 2) ^ 2 := by ring
  rw [h, fr2, Real.sq_sqrt (Real.sqrt_nonneg 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- **`[ℚ(⁴√2):ℚ] = 4`** from the general degree lemma (parent:
`finrank_adjoin_fr2`, which reproved irreducibility by hand). -/
theorem finrank_adjoin_fr2 : Module.finrank ℚ ℚ⟮fr2⟯ = 4 :=
  finrank_adjoin_eq (p := 2) Int.prime_two (n := 4) fr2_pow

end FourthRoot2Degree4OQ02

/-! ## Axiom audit

Confirms the headline results depend only on the foundational
`propext` / `Classical.choice` / `Quot.sound` — no `sorryAx`, no
`Lean.ofReduceBool` (i.e. no `native_decide`). -/

#print axioms FourthRoot2Degree4OQ02.irreducible_X_pow_sub_C_int
#print axioms FourthRoot2Degree4OQ02.irreducible_X_pow_sub_C_rat
#print axioms FourthRoot2Degree4OQ02.finrank_adjoin_eq
#print axioms FourthRoot2Degree4OQ02.finrank_adjoin_fr2
#print axioms FourthRoot2Degree4OQ02.finrank_adjoin_sqrt2
