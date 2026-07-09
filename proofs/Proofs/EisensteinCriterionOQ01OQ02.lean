/-
  Degree of `ℚ(ⁿ√p)`: the minimal polynomial `Xⁿ − p` via Eisenstein
  (eisenstein-criterion-oq-01-oq-02)

  The gallery entry `eisenstein-criterion-oq-01` proves that `Xⁿ − p` is
  irreducible over `ℤ` for every prime `p` and every `n ≥ 1`
  (`EisensteinCriterionOQ01.irreducible_X_pow_sub_C_prime`).  This file draws the
  standard field-theoretic corollary:

  * Gauss's lemma transports that irreducibility to `ℚ`
    (`irreducible_X_pow_sub_C_prime_rat`).
  * Since `Xⁿ − p` is monic, irreducible over `ℚ`, and vanishes at the real
    `n`-th root `p^{1/n}`, it is *the* minimal polynomial of `p^{1/n}` over `ℚ`
    (`minpoly_eq_X_pow_sub_C`).
  * Hence `[ℚ(p^{1/n}) : ℚ] = n` (`finrank_adjoin_eq`), and Eisenstein produces
    a real algebraic number of every prescribed degree
    (`exists_algebraic_number_of_degree`).

  Concrete instances: `[ℚ(√2):ℚ] = 2` and `[ℚ(∛2):ℚ] = 3`.

  All results are `0`-sorry / `0`-axiom on top of Mathlib and the parent entry.
-/
import Mathlib
import Proofs.EisensteinCriterionOQ01

open Polynomial IntermediateField

namespace EisensteinCriterionOQ01OQ02

open EisensteinCriterionOQ01

/-! ### Irreducibility over `ℚ`

Gauss's lemma: a primitive integer polynomial is irreducible over `ℤ` iff its
image in `ℚ[X]` is irreducible.  `Xⁿ − p` is monic (hence primitive), so the
parent's `ℤ`-irreducibility gives irreducibility over `ℚ` for *every* `n ≥ 1`. -/

/-- `Xⁿ − p` is irreducible over `ℚ` for every prime `p` and every `n ≥ 1`. -/
theorem irreducible_X_pow_sub_C_prime_rat {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℚ[X]) ^ n - C (p : ℚ)) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hZ : Irreducible ((X : ℤ[X]) ^ n - C (p : ℤ)) :=
    irreducible_X_pow_sub_C_prime hpz hn
  have hprim : ((X : ℤ[X]) ^ n - C (p : ℤ)).IsPrimitive :=
    (monic_X_pow_sub_C (p : ℤ) hn.ne').isPrimitive
  -- the image of `Xⁿ − p` under `ℤ → ℚ` is `Xⁿ − p`
  have hmap : ((X : ℤ[X]) ^ n - C (p : ℤ)).map (Int.castRingHom ℚ)
      = (X : ℚ[X]) ^ n - C (p : ℚ) := by
    simp
  have := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hZ
  rwa [hmap] at this

/-! ### The minimal polynomial of a real `n`-th root of a prime -/

/-- The real `n`-th root `α` of a prime `p` (any `α` with `αⁿ = p`) is a root of
`Xⁿ − p` over `ℚ`. -/
theorem aeval_root {p : ℕ} {n : ℕ} {α : ℝ} (hα : α ^ n = (p : ℝ)) :
    (Polynomial.aeval α) ((X : ℚ[X]) ^ n - C (p : ℚ)) = 0 := by
  have h : (Polynomial.aeval α) ((X : ℚ[X]) ^ n - C (p : ℚ)) = α ^ n - (p : ℝ) := by
    simp
  rw [h, hα, sub_self]

/-- **Minimal polynomial.** For a prime `p`, `n ≥ 1`, and any real `α` with
`αⁿ = p`, the minimal polynomial of `α` over `ℚ` is exactly `Xⁿ − p`. -/
theorem minpoly_eq_X_pow_sub_C {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n)
    {α : ℝ} (hα : α ^ n = (p : ℝ)) :
    minpoly ℚ α = (X : ℚ[X]) ^ n - C (p : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic
    (irreducible_X_pow_sub_C_prime_rat hp hn)
    (aeval_root hα)
    (monic_X_pow_sub_C (p : ℚ) hn.ne')).symm

/-- Such an `α` is integral over `ℚ`. -/
theorem isIntegral_root {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n)
    {α : ℝ} (hα : α ^ n = (p : ℝ)) : IsIntegral ℚ α := by
  rw [← minpoly.ne_zero_iff, minpoly_eq_X_pow_sub_C hp hn hα]
  exact (monic_X_pow_sub_C (p : ℚ) hn.ne').ne_zero

/-! ### The degree of the radical extension -/

/-- **`[ℚ(p^{1/n}) : ℚ] = n`.** For a prime `p`, `n ≥ 1`, and any real `α` with
`αⁿ = p`, the simple extension `ℚ(α)/ℚ` has degree exactly `n`. -/
theorem finrank_adjoin_eq {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n)
    {α : ℝ} (hα : α ^ n = (p : ℝ)) :
    Module.finrank ℚ ℚ⟮α⟯ = n := by
  rw [IntermediateField.adjoin.finrank (isIntegral_root hp hn hα),
    minpoly_eq_X_pow_sub_C hp hn hα, natDegree_X_pow_sub_C]

/-- **Eisenstein produces an algebraic number of every prescribed degree.**
For every prime `p` and every `n ≥ 1`, the real `n`-th root `p^{1/n}` is
algebraic over `ℚ` of degree exactly `n`. -/
theorem exists_algebraic_number_of_degree {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    ∃ α : ℝ, IsIntegral ℚ α ∧ Module.finrank ℚ ℚ⟮α⟯ = n := by
  have hα : ((p : ℝ) ^ ((n : ℝ)⁻¹)) ^ n = (p : ℝ) :=
    Real.rpow_inv_natCast_pow (by positivity) hn.ne'
  exact ⟨(p : ℝ) ^ ((n : ℝ)⁻¹), isIntegral_root hp hn hα, finrank_adjoin_eq hp hn hα⟩

/-! ### Concrete instances -/

/-- `minpoly ℚ (√2) = X² − 2`. -/
theorem minpoly_sqrt_two : minpoly ℚ (Real.sqrt 2) = (X : ℚ[X]) ^ 2 - C 2 := by
  have hα : Real.sqrt 2 ^ 2 = ((2 : ℕ) : ℝ) := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have h := minpoly_eq_X_pow_sub_C Nat.prime_two (by norm_num) hα
  simpa using h

/-- `[ℚ(√2) : ℚ] = 2`. -/
theorem finrank_adjoin_sqrt_two : Module.finrank ℚ ℚ⟮(Real.sqrt 2)⟯ = 2 := by
  have hα : Real.sqrt 2 ^ 2 = ((2 : ℕ) : ℝ) := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  exact finrank_adjoin_eq Nat.prime_two (by norm_num) hα

/-- `[ℚ(∛2) : ℚ] = 3`. -/
theorem finrank_adjoin_cbrt_two :
    Module.finrank ℚ ℚ⟮((2 : ℝ) ^ (((3 : ℕ) : ℝ)⁻¹))⟯ = 3 := by
  have hα : ((2 : ℝ) ^ (((3 : ℕ) : ℝ)⁻¹)) ^ 3 = ((2 : ℕ) : ℝ) := by
    have h := Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 3) (by norm_num) (by norm_num)
    simpa using h
  exact finrank_adjoin_eq Nat.prime_three (by norm_num) hα

end EisensteinCriterionOQ01OQ02
