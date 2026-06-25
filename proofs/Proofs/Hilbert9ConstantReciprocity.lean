/-
  Constant reciprocity in function fields F_q[T] over finite fields.

  This file answers a concrete, fully verified slice of the open question
  "What reciprocity-type phenomena exist in function fields?" raised by the
  gallery entry on Hilbert's Ninth Problem (the most general reciprocity law).

  Background.  In the polynomial ring F_q[T] (q an odd prime power) the role of
  the rational primes is played by the monic irreducible polynomials P, and the
  quadratic residue symbol (a / P) is defined through the residue field
  F_q[T]/(P) ≅ F_{q^{deg P}}.  For a *constant* a ∈ F_q^× the symbol (a / P)
  therefore measures whether a, viewed inside F_{q^{deg P}}, is a square.  The
  classical "constant reciprocity" law states that this depends only on the
  parity of deg P:

      (a / P) = χ_q(a) ^ {deg P},

  where χ_q is the quadratic character of F_q.  Equivalently, a constant that is
  a nonsquare in F_q becomes a square in F_{q^d} exactly when d is even.

  We formalize this as a relation between the quadratic characters of a finite
  field `F` and a finite extension `K`:

      quadraticChar K (algebraMap F K a) = (quadraticChar F a) ^ [K : F].

  Everything is derived from Mathlib's Euler criterion
  (`quadraticChar_eq_pow_of_char_ne_two'`); there are no axioms and no `sorry`.

  Main results:
  * `quadraticChar_algebraMap_eq_pow` — the constant reciprocity law above.
  * `isSquare_algebraMap_iff` — a constant `a` is a square in `K` iff it is a
    square in `F` or `[K : F]` is even.
  * `isSquare_algebraMap_of_even_finrank` — every constant becomes a square in an
    even-degree extension (e.g. all of F_q is square in F_{q^2}).
-/
import Mathlib

open Finset

namespace Hilbert9ConstantReciprocity

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [DecidableEq K] [Algebra F K]

omit [Fintype K] [DecidableEq K] in
/-- Two integers drawn from `{1, -1}` that agree after casting into a field of
characteristic `≠ 2` are equal.  This is the injectivity we need to pass from an
equality of character *values in `K`* back to an equality of integers. -/
private theorem cast_pm_inj (hcharK : ringChar K ≠ 2) {x y : ℤ}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) (h : (x : K) = (y : K)) : x = y := by
  have hne : (-1 : K) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hcharK
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · push_cast at h; exact absurd h.symm hne
  · push_cast at h; exact absurd h hne
  · rfl

omit [Fintype F] [DecidableEq F] [DecidableEq K] in
/-- The characteristic is unchanged when passing to an extension field. -/
private theorem ringChar_extension_ne_two (hF : ringChar F ≠ 2) : ringChar K ≠ 2 := by
  have hinj : Function.Injective (algebraMap F K) := FaithfulSMul.algebraMap_injective F K
  have hcK : CharP K (ringChar F) := charP_of_injective_algebraMap hinj (ringChar F)
  rwa [CharP.eq K (ringChar.charP K) hcK]

/--
**Constant reciprocity law.**  For a constant `a ∈ F` and a finite extension `K`
of a finite field `F` of odd characteristic, the quadratic character of `a`
computed in `K` is the `[K : F]`-th power of its quadratic character in `F`:

    quadraticChar K (algebraMap F K a) = (quadraticChar F a) ^ (finrank F K).

This is the function-field analogue of the statement that the residue symbol of a
*constant* depends only on the degree of the place modulo 2.
-/
theorem quadraticChar_algebraMap_eq_pow (hF : ringChar F ≠ 2) (a : F) :
    quadraticChar K (algebraMap F K a)
      = (quadraticChar F a) ^ (Module.finrank F K) := by
  have hcharK : ringChar K ≠ 2 := ringChar_extension_ne_two hF
  set d : ℕ := Module.finrank F K with hd
  have hdpos : 0 < d := Module.finrank_pos
  -- The `a = 0` case is degenerate: both sides vanish.
  by_cases ha : a = 0
  · subst ha
    rw [map_zero, MulChar.map_zero, MulChar.map_zero, zero_pow hdpos.ne']
  -- From now on `a ≠ 0`.
  set q : ℕ := Fintype.card F with hq
  set A : K := algebraMap F K a with hA
  have haA : A ≠ 0 := by
    rw [hA]; exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F K)).mpr ha
  -- Abbreviations for the half-cardinalities appearing in Euler's criterion.
  have hcard : Fintype.card K = q ^ d := Module.card_eq_pow_finrank
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hqodd : q % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hQodd : (q ^ d) % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hqodd).pow)
  -- `S = 1 + q + … + q^{d-1}`, the geometric sum.
  set S : ℕ := ∑ i ∈ range d, q ^ i with hS
  -- (1) `2 * (q / 2) = q - 1` because `q` is odd.
  have hM : 2 * (q / 2) = q - 1 := by
    have := Nat.div_add_mod q 2; omega
  -- (2) `(q - 1) * S = q^d - 1` (geometric series).
  have hdvd : (q - 1) ∣ (q ^ d - 1) := by
    simpa using Nat.sub_dvd_pow_sub_pow q 1 d
  have hgeom : (q - 1) * S = q ^ d - 1 := by
    rw [hS, Nat.geomSum_eq hq2 d, Nat.mul_div_cancel' hdvd]
  -- (3) The half-cardinality of `K` factors as `(q / 2) * S`.
  have hN : Fintype.card K / 2 = (q / 2) * S := by
    have e1 : 2 * (Fintype.card K / 2) = q ^ d - 1 := by
      have := Nat.div_add_mod (Fintype.card K) 2
      rw [hcard] at this ⊢; omega
    have key : 2 * (Fintype.card K / 2) = 2 * ((q / 2) * S) := by
      rw [e1, ← mul_assoc, hM, hgeom]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) key
  -- Euler's criterion in `F`, transported into `K` along the algebra map.
  have eulerF : ((quadraticChar F a : ℤ) : F) = a ^ (q / 2) :=
    quadraticChar_eq_pow_of_char_ne_two' hF a
  have hAM : ((quadraticChar F a : ℤ) : K) = A ^ (q / 2) := by
    have := congrArg (algebraMap F K) eulerF
    rwa [map_intCast, map_pow, ← hA] at this
  -- `A ^ (q - 1) = 1`, hence `(A ^ (q/2))^2 = 1`.
  have hAq1 : A ^ (q - 1) = 1 := by
    rw [hA, ← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]
  have hu2 : (A ^ (q / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, hM, hAq1]
  -- For `u` with `u^2 = 1`, `u^n` depends only on `n` mod 2.
  have hgen : ∀ n : ℕ, (A ^ (q / 2)) ^ n = (A ^ (q / 2)) ^ (n % 2) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, hu2, one_pow, one_mul]
  -- `S ≡ d (mod 2)` since each `q^i` is odd.
  have hSd : S % 2 = d % 2 := by
    have hterm : ∀ i ∈ range d, q ^ i % 2 = 1 := fun i _ =>
      Nat.odd_iff.mp ((Nat.odd_iff.mpr hqodd).pow)
    calc S % 2 = (∑ i ∈ range d, q ^ i % 2) % 2 := by rw [hS, Finset.sum_nat_mod]
      _ = (∑ _i ∈ range d, 1) % 2 := by rw [Finset.sum_congr rfl hterm]
      _ = d % 2 := by rw [Finset.sum_const, card_range, smul_eq_mul, mul_one]
  have hpow_eq : (A ^ (q / 2)) ^ S = (A ^ (q / 2)) ^ d := by
    rw [hgen S, hgen d, hSd]
  -- Assemble the equality of character values inside `K`.
  have hcast : (quadraticChar K A : K) = (((quadraticChar F a) ^ d : ℤ) : K) := by
    rw [quadraticChar_eq_pow_of_char_ne_two' hcharK A, hN, pow_mul, hpow_eq]
    push_cast
    rw [hAM]
  -- Pass back to an equality of integers using `cast_pm_inj`.
  refine cast_pm_inj hcharK (quadraticChar_dichotomy haA) ?_ hcast
  rcases quadraticChar_dichotomy ha with h | h <;> rw [h]
  · left; exact one_pow d
  · rcases Nat.even_or_odd d with he | ho
    · left; exact he.neg_one_pow
    · right; exact ho.neg_one_pow

/--
**Constant square criterion.**  A nonzero constant `a ∈ F` becomes a square in a
finite extension `K` (of a finite field of odd characteristic) if and only if it
is already a square in `F` or the degree `[K : F]` is even.

In F_q[T] terms: a constant `a` is a quadratic residue modulo a monic irreducible
`P` iff `a` is a square in F_q or `deg P` is even.
-/
theorem isSquare_algebraMap_iff (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    IsSquare (algebraMap F K a) ↔ (IsSquare a ∨ Even (Module.finrank F K)) := by
  have haA : algebraMap F K a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F K)).mpr ha
  rw [← quadraticChar_one_iff_isSquare haA, quadraticChar_algebraMap_eq_pow hF a]
  rcases quadraticChar_dichotomy ha with h | h
  · rw [h, one_pow]
    simp [(quadraticChar_one_iff_isSquare ha).mp h]
  · rw [h]
    have hns : ¬ IsSquare a := quadraticChar_neg_one_iff_not_isSquare.mp h
    constructor
    · intro hpow
      refine Or.inr ?_
      by_contra hodd
      rw [(Nat.not_even_iff_odd.mp hodd).neg_one_pow] at hpow
      exact (by norm_num : (-1 : ℤ) ≠ 1) hpow
    · rintro (hsq | hev)
      · exact absurd hsq hns
      · rw [hev.neg_one_pow]

/-- Every constant is a square in an even-degree extension; in particular all of
F_q is a square in the quadratic extension F_{q^2}. -/
theorem isSquare_algebraMap_of_even_finrank (hF : ringChar F ≠ 2)
    (hev : Even (Module.finrank F K)) (a : F) : IsSquare (algebraMap F K a) := by
  by_cases ha : a = 0
  · rw [ha, map_zero]; exact IsSquare.zero
  · exact (isSquare_algebraMap_iff hF ha).mpr (Or.inr hev)

end Hilbert9ConstantReciprocity
