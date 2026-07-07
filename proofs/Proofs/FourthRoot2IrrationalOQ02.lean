/-
# The exact algebraic degree of every prime radical: [ℚ(p^{1/n}) : ℚ] = n
  (fourth-root-2-irrational OQ-02)

The parent gallery entry **fourth-root-2-irrational** (`FourthRoot2Degree4.lean`)
proves that `⁴√2` has degree exactly 4 over ℚ, via Eisenstein's criterion at the
prime 2 on `X⁴ − 2` followed by Gauss's lemma. Its open question OQ-02 asks
whether that Eisenstein-then-Gauss route can be **packaged as a reusable lemma**
for `X^{2^k} − 2` (or `X^{p^k} − p`), filling the even-exponent / prime-power gap
that Mathlib's Kummer lemmas (`X_pow_sub_C_irreducible_of_prime_pow`, which needs
`p ≠ 2`, and `…_of_odd`, which needs odd exponent) mark with explicit `TODO`s.

The *irreducibility* half of that packaging already exists in the gallery:
`CubeRoot3IrrationalOQ01.irreducible_X_pow_sub_C_prime_{int,rat}` proves `Xⁿ − p`
irreducible over ℤ and ℚ for **every** prime `p` and **every** `n ≥ 1` — with no
parity or prime-power restriction — and `NthRootIrrationalOQ01` uses it to prove
`p^{1/n}` *irrational*. But irrationality only certifies algebraic degree `≥ 2`.
No file pins the degree of the real radical at *exactly* `n`.

This file closes that gap. Building directly on the existing irreducibility
lemma, it identifies the **minimal polynomial of the real radical** and computes
the **exact field degree**, uniformly in `p` and `n`:

  * `minpoly_primeRoot`          — `minpoly ℚ (p^{1/n}) = Xⁿ − p`;
  * `finrank_adjoin_primeRoot`   — `[ℚ(p^{1/n}) : ℚ] = n`;
  * `linearIndependent_primeRoot_powers` — `{1, r, …, rⁿ⁻¹}` are ℚ-independent.

The headline specializations are exactly the cases OQ-02 names:

  * `finrank_adjoin_two_pow_k` — `[ℚ(2^{1/2^k}) : ℚ] = 2^k`   (the even / prime-power exponent `2^k`);
  * `finrank_adjoin_prime_pow` — `[ℚ(p^{1/p^k}) : ℚ] = p^k`   (the general `X^{p^k} − p` case);
  * `finrank_adjoin_fourthRoot_two` — `[ℚ(2^{1/4}) : ℚ] = 4`, recovering the parent.

The real radical is modeled as `(p : ℝ) ^ ((1 : ℝ) / n)` (`Real.rpow`), matching
`NthRootIrrationalOQ01`, so the present degree results sit on top of that file's
irrationality results for the *same* term.

Zero axioms; self-contained on top of Mathlib. The reusable Eisenstein-then-Gauss
irreducibility core (`irreducible_X_pow_sub_C_prime_int/rat`, `minpoly_eq_of_pow_eq_prime`)
is proved directly below, so this file no longer depends on the sibling
`CubeRoot3IrrationalOQ01` module.
-/
import Mathlib

open Polynomial IntermediateField

namespace FourthRoot2IrrationalOQ02

/-! ## Reusable Eisenstein-then-Gauss core: `Xⁿ − p` irreducible for every `n ≥ 1`

Mathlib's Kummer lemmas (`X_pow_sub_C_irreducible_of_odd`,
`X_pow_sub_C_irreducible_of_prime_pow`) require odd `n` or `p ≠ 2` and carry
explicit `TODO`s for the even / `p = 2` corners. The Eisenstein route below is
uniform in the exponent `n` and covers those corners directly. -/

/-- The coefficients of `Xⁿ − C a` over any commutative ring: `1` at index `n`,
`−a` at index `0`, and `0` elsewhere. -/
theorem coeff_X_pow_sub_C {R : Type*} [CommRing R] (n : ℕ) (a : R) (k : ℕ) :
    (X ^ n - C a : R[X]).coeff k
      = (if k = n then (1 : R) else 0) - (if k = 0 then a else 0) := by
  simp only [coeff_sub, coeff_X_pow, coeff_C]

/-- **Reusable Eisenstein lemma.** For a prime `p : ℤ` and any exponent `n ≥ 1`,
the polynomial `Xⁿ − p` is irreducible over `ℤ`, uniformly in `n`. -/
theorem irreducible_X_pow_sub_C_prime_int {p : ℤ} (hp : Prime p) {n : ℕ}
    (hn : 0 < n) : Irreducible (X ^ n - C p : ℤ[X]) := by
  have hn0 : n ≠ 0 := hn.ne'
  have hmonic : (X ^ n - C p : ℤ[X]).Monic := monic_X_pow_sub_C _ hn0
  have hdeg : (X ^ n - C p : ℤ[X]).degree = n := degree_X_pow_sub_C hn p
  apply irreducible_of_eisenstein_criterion (P := Ideal.span {p})
  · exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  · have hlc : (X ^ n - C p : ℤ[X]).leadingCoeff = 1 := hmonic
    rw [hlc, Ideal.mem_span_singleton]
    exact fun h => hp.not_unit (isUnit_of_dvd_one h)
  · intro k hk
    rw [hdeg] at hk
    have hkn : k ≠ n := by
      have : k < n := by exact_mod_cast hk
      exact this.ne
    rw [coeff_X_pow_sub_C, if_neg hkn, Ideal.mem_span_singleton]
    split_ifs <;> simp [dvd_neg]
  · rw [hdeg]; exact_mod_cast hn
  · rw [coeff_X_pow_sub_C, if_neg (Ne.symm hn0), if_pos rfl, zero_sub,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    rw [dvd_neg, sq] at h
    have : p ∣ 1 := by
      have h1 : p * p ∣ p * 1 := by simpa using h
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp h1
    exact hp.not_unit (isUnit_of_dvd_one this)
  · exact hmonic.isPrimitive

/-- **Reusable Eisenstein-then-Gauss lemma over ℚ.** For a prime `p : ℤ` and any
`n ≥ 1`, `Xⁿ − p` is irreducible over ℚ. -/
theorem irreducible_X_pow_sub_C_prime_rat {p : ℤ} (hp : Prime p) {n : ℕ}
    (hn : 0 < n) : Irreducible (X ^ n - C (p : ℚ) : ℚ[X]) := by
  have hprim : (X ^ n - C p : ℤ[X]).IsPrimitive :=
    (monic_X_pow_sub_C _ hn.ne').isPrimitive
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    (irreducible_X_pow_sub_C_prime_int hp hn)
  have hmap : (X ^ n - C p : ℤ[X]).map (Int.castRingHom ℚ) = X ^ n - C (p : ℚ) := by
    simp [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  rwa [hmap] at h

/-- Convenience form for a natural-number prime `p`. -/
theorem irreducible_X_pow_sub_C_natPrime_rat {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : 0 < n) : Irreducible (X ^ n - C (p : ℚ) : ℚ[X]) := by
  have h := irreducible_X_pow_sub_C_prime_rat (p := (p : ℤ))
    (Nat.prime_iff_prime_int.mp hp) hn
  simpa using h

/-- **Headline even family.** `X^(2^k) − 2` is irreducible over ℚ for every `k` —
the `n = 2^k`, base `= 2` corner excluded by both Kummer `TODO`s. -/
theorem irreducible_X_two_pow_sub_two_rat (k : ℕ) :
    Irreducible (X ^ (2 ^ k) - C (2 : ℚ) : ℚ[X]) :=
  irreducible_X_pow_sub_C_natPrime_rat (Nat.prime_two) (pow_pos (by norm_num) k)

/-- The `⁴√2` instance (`k = 2`) recovered from the general even family. -/
theorem irreducible_X4_sub_2_rat : Irreducible (X ^ 4 - C (2 : ℚ) : ℚ[X]) := by
  have h := irreducible_X_two_pow_sub_two_rat 2
  norm_num at h
  exact h

/-- **Prime-power exponents at arbitrary prime base**, including `p = 2`. -/
theorem irreducible_X_pow_sub_C_primePow_prime_rat {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (k : ℕ) :
    Irreducible (X ^ (p ^ k) - C (q : ℚ) : ℚ[X]) :=
  irreducible_X_pow_sub_C_natPrime_rat hq (pow_pos hp.pos k)

/-- **Reusable minimal-polynomial lemma.** If `α` in a ℚ-algebra domain satisfies
`αⁿ = p` for a prime `p` (`n ≥ 1`), then `minpoly ℚ α = Xⁿ − p`. -/
theorem minpoly_eq_of_pow_eq_prime {A : Type*} [CommRing A] [IsDomain A]
    [Algebra ℚ A] {α : A} {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n)
    (hpow : α ^ n = (p : A)) :
    minpoly ℚ α = X ^ n - C (p : ℚ) := by
  refine (minpoly.eq_of_irreducible_of_monic
    (irreducible_X_pow_sub_C_natPrime_rat hp hn) ?_ (monic_X_pow_sub_C _ hn.ne')).symm
  rw [map_sub, map_pow, aeval_X, aeval_C, map_natCast, hpow, sub_self]

/-- The field degree `[ℚ(α) : ℚ] = n` whenever `αⁿ = p` is prime. -/
theorem natDegree_minpoly_eq_of_pow_eq_prime {A : Type*} [CommRing A] [IsDomain A]
    [Algebra ℚ A] {α : A} {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n)
    (hpow : α ^ n = (p : A)) :
    (minpoly ℚ α).natDegree = n := by
  rw [minpoly_eq_of_pow_eq_prime hp hn hpow, natDegree_X_pow_sub_C]

/-! ### The real radical and its defining power relation -/

/-- `(p^{1/n})ⁿ = p` for `p > 0`, `n ≥ 1`: the real `n`-th root of `p`, modeled as
`Real.rpow`, raised back to the `n`-th power returns `p`. -/
theorem rpow_inv_natCast_pow {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    ((p : ℝ) ^ ((1 : ℝ) / n)) ^ n = (p : ℝ) := by
  rw [← Real.rpow_natCast ((p : ℝ) ^ ((1 : ℝ) / n)) n,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [one_div, inv_mul_cancel₀ hn', Real.rpow_one]

/-- The real radical `p^{1/n}` is a root of `Xⁿ − p` over ℚ. -/
theorem aeval_primeRoot {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    (Polynomial.aeval ((p : ℝ) ^ ((1 : ℝ) / n))) (X ^ n - C (p : ℚ)) = 0 := by
  simp only [map_sub, map_pow, aeval_X, rpow_inv_natCast_pow hp hn,
    map_natCast, sub_self]

/-- `p^{1/n}` is integral over ℚ: a root of the monic `Xⁿ − p`. -/
theorem primeRoot_isIntegral {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    IsIntegral ℚ ((p : ℝ) ^ ((1 : ℝ) / n)) :=
  ⟨X ^ n - C (p : ℚ), monic_X_pow_sub_C _ hn.ne', aeval_primeRoot hp hn⟩

/-! ### The minimal polynomial and the exact degree -/

/-- **The minimal polynomial of `p^{1/n}` over ℚ is `Xⁿ − p`.** This uses the
sibling irreducibility lemma (Eisenstein at `p` + Gauss) and the fact that the
radical is a root of the monic `Xⁿ − p`. It is the sharp statement: the radical's
minimal polynomial is *the* full Eisenstein polynomial, not a proper factor. -/
theorem minpoly_primeRoot {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    minpoly ℚ ((p : ℝ) ^ ((1 : ℝ) / n)) = X ^ n - C (p : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic
    (irreducible_X_pow_sub_C_natPrime_rat hp hn)
    (aeval_primeRoot hp.pos hn)
    (monic_X_pow_sub_C _ hn.ne')).symm

/-- The minimal polynomial of `p^{1/n}` has degree exactly `n`. -/
theorem minpoly_natDegree_primeRoot {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (minpoly ℚ ((p : ℝ) ^ ((1 : ℝ) / n))).natDegree = n := by
  rw [minpoly_primeRoot hp hn, natDegree_X_pow_sub_C]

/-- **The exact field degree `[ℚ(p^{1/n}) : ℚ] = n`** for every prime `p` and
every `n ≥ 1`. This is strictly stronger than irrationality (degree `≥ 2`): it
pins the algebraic degree of the real radical at exactly `n`, with no parity or
prime-power restriction on the exponent. -/
theorem finrank_adjoin_primeRoot {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    Module.finrank ℚ ℚ⟮((p : ℝ) ^ ((1 : ℝ) / n))⟯ = n := by
  rw [IntermediateField.adjoin.finrank (primeRoot_isIntegral hp.pos hn),
      minpoly_natDegree_primeRoot hp hn]

/-- **The power basis `{1, r, r², …, rⁿ⁻¹}` of `r = p^{1/n}` is ℚ-linearly
independent.** Immediate from `[ℚ(r):ℚ] = n`: the powers below the minimal-
polynomial degree are independent. Generalizes the parent's
`linearIndependent_fr2_powers` (the `Fin 4` case for `⁴√2`). -/
theorem linearIndependent_primeRoot_powers {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    LinearIndependent ℚ (fun i : Fin n => ((p : ℝ) ^ ((1 : ℝ) / n)) ^ (i : ℕ)) := by
  have h := linearIndependent_pow (K := ℚ) ((p : ℝ) ^ ((1 : ℝ) / n))
  rw [minpoly_natDegree_primeRoot hp hn] at h
  exact h

/-! ### The headline specializations named by OQ-02 -/

/-- **`[ℚ(2^{1/2^k}) : ℚ] = 2^k`** — the even / prime-power exponent `2^k`. This is
precisely the case Mathlib's Kummer API cannot reach (it requires `p ≠ 2` or odd
exponent); Eisenstein at 2 is exponent-agnostic and handles it uniformly. -/
theorem finrank_adjoin_two_pow_k (k : ℕ) :
    Module.finrank ℚ ℚ⟮(((2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((2 ^ k : ℕ) : ℝ)))⟯ = 2 ^ k :=
  finrank_adjoin_primeRoot (p := 2) (n := 2 ^ k) (by norm_num) (by positivity)

/-- **`[ℚ(p^{1/p^k}) : ℚ] = p^k`** — the general `X^{p^k} − p` case named by OQ-02,
for an arbitrary prime `p`. -/
theorem finrank_adjoin_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Module.finrank ℚ ℚ⟮((p : ℝ) ^ ((1 : ℝ) / ((p ^ k : ℕ) : ℝ)))⟯ = p ^ k :=
  finrank_adjoin_primeRoot hp (pow_pos hp.pos k)

/-- **`[ℚ(2^{1/4}) : ℚ] = 4`** — recovering the parent entry's `finrank_adjoin_fr2`
as the `k = 2` instance of `finrank_adjoin_two_pow_k` (note `2^{1/4} = ⁴√2`). -/
theorem finrank_adjoin_fourthRoot_two :
    Module.finrank ℚ ℚ⟮(((2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((4 : ℕ) : ℝ)))⟯ = 4 :=
  finrank_adjoin_primeRoot (p := 2) (n := 4) (by norm_num) (by norm_num)

end FourthRoot2IrrationalOQ02
