import Mathlib
import Proofs.InverseGaloisOQ06OQ01

/-
# A Second Unramified Prime: the mod-11 (1,1,3) Witness (OQ-06 → OQ-02, p = 11)

The sibling file `InverseGaloisOQ06OQ02.lean` verifies, with no axioms, the
mod-7 algebraic input to Dedekind's theorem for

  `q = X⁵ - 5X⁴ + 10X³ - 10X² + 25X - 5`,

namely that `q mod 7` factors into distinct irreducibles of degrees `(1,1,3)`
and is squarefree (so 7 is unramified).

This file provides an **independent corroborating witness at a second prime,
`p = 11`** — the optional next step recorded for this research slug. A second
unramified prime with the same `(1,1,3)` factor type strengthens the
Dedekind-route evidence that `3 ∣ |Gal(q)|`: it exhibits a *second* 3-cycle in
`Gal(q)` (once Dedekind's theorem is available), and rules out the possibility
that the mod-7 factorization was an accident of that particular prime.

## The mod-11 factorization

  `q ≡ (X - 4)(X - 3)·(X³ + 2X² + X - 5)   (mod 11)`,

with the cubic `cubicMod11 = X³ + 2X² + X + 6` (note `-5 ≡ 6 mod 11`) having no
roots in `𝔽₁₁`, hence irreducible. The three factors are pairwise
non-associated and their product is squarefree, so 11 is unramified.

## Honest scope

As with the mod-7 file, this does **not** eliminate the axiom
`three_dvd_gal_card`; Dedekind's theorem itself remains a Mathlib 4.26 gap. What
is added is a second verified, 0-axiom, 0-sorry algebraic input: `q mod 11` is a
product of distinct irreducibles of degrees `(1,1,3)`, and 11 is unramified.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped Classical

namespace InverseGaloisOQ06OQ02P11

open Polynomial

/-- `11` is prime, so `ZMod 11` is a field (and `(ZMod 11)[X]` a Euclidean domain). -/
instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- `q` as an integer polynomial (the same `q` as the parent A₅ entry). -/
noncomputable def q_ℤ : ℤ[X] :=
  X ^ 5 - C 5 * X ^ 4 + C 10 * X ^ 3 - C 10 * X ^ 2 + C 25 * X - C 5

-- ============================================================================
-- § 1. The three factors and their degrees
-- ============================================================================

/-- The irreducible cubic factor of `q mod 11`: `X³ + 2X² + X + 6` (`-5 ≡ 6`). -/
noncomputable def cubicMod11 : (ZMod 11)[X] :=
  X ^ 3 + C 2 * X ^ 2 + C 1 * X + C 6

/-- The first linear factor `X - 4` over `𝔽₁₁`. -/
noncomputable def linFactor4 : (ZMod 11)[X] := X - C 4

/-- The second linear factor `X - 3` over `𝔽₁₁`. -/
noncomputable def linFactor3 : (ZMod 11)[X] := X - C 3

theorem cubicMod11_natDegree : cubicMod11.natDegree = 3 := by
  unfold cubicMod11; compute_degree!

theorem linFactor4_natDegree : linFactor4.natDegree = 1 := by
  unfold linFactor4; compute_degree!

theorem linFactor3_natDegree : linFactor3.natDegree = 1 := by
  unfold linFactor3; compute_degree!

theorem linFactor4_ne_zero : linFactor4 ≠ 0 := (monic_X_sub_C 4).ne_zero
theorem linFactor3_ne_zero : linFactor3 ≠ 0 := (monic_X_sub_C 3).ne_zero

theorem cubicMod11_ne_zero : cubicMod11 ≠ 0 := by
  intro h0
  have hd := cubicMod11_natDegree
  rw [h0, natDegree_zero] at hd
  exact absurd hd (by decide)

-- ============================================================================
-- § 2. The cubic has no roots in 𝔽₁₁, hence is irreducible
-- ============================================================================

/-- `cubicMod11` has no roots in `𝔽₁₁` (finite check over all 11 residues). -/
theorem cubicMod11_no_roots : ∀ x : ZMod 11, eval x cubicMod11 ≠ 0 := by
  intro x
  fin_cases x <;>
    simp only [cubicMod11, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one,
      eval_neg, eval_zero] <;>
    decide

/-- **The cubic factor is irreducible over `𝔽₁₁`.**
A degree-3 polynomial over a field with no root is irreducible. -/
theorem cubicMod11_irreducible : Irreducible cubicMod11 := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [cubicMod11_natDegree]; decide
  · intro x; exact cubicMod11_no_roots x

theorem linFactor4_irreducible : Irreducible linFactor4 := irreducible_X_sub_C 4
theorem linFactor3_irreducible : Irreducible linFactor3 := irreducible_X_sub_C 3

-- ============================================================================
-- § 3. The three factors are pairwise non-associated (distinct primes)
-- ============================================================================

/-- The two linear factors are not associated: associated monic linears are
equal, forcing `4 = 3` in `𝔽₁₁`, which is false. -/
theorem linFactors_not_associated : ¬ Associated linFactor4 linFactor3 := by
  intro h
  have heq : linFactor4 = linFactor3 :=
    eq_of_monic_of_associated (monic_X_sub_C 4) (monic_X_sub_C 3) h
  have h0 := congrArg (eval (0 : ZMod 11)) heq
  simp only [linFactor4, linFactor3, eval_sub, eval_X, eval_C] at h0
  revert h0; decide

/-- A degree-1 factor cannot be associated to the degree-3 cubic. -/
theorem linFactor4_not_associated_cubic : ¬ Associated linFactor4 cubicMod11 := by
  intro h
  have h1 := natDegree_le_of_dvd h.dvd cubicMod11_ne_zero
  have h2 := natDegree_le_of_dvd h.symm.dvd linFactor4_ne_zero
  rw [linFactor4_natDegree, cubicMod11_natDegree] at h1 h2
  omega

/-- A degree-1 factor cannot be associated to the degree-3 cubic. -/
theorem linFactor3_not_associated_cubic : ¬ Associated linFactor3 cubicMod11 := by
  intro h
  have h1 := natDegree_le_of_dvd h.dvd cubicMod11_ne_zero
  have h2 := natDegree_le_of_dvd h.symm.dvd linFactor3_ne_zero
  rw [linFactor3_natDegree, cubicMod11_natDegree] at h1 h2
  omega

-- ============================================================================
-- § 4. Pairwise coprimality and squarefreeness (11 is unramified)
-- ============================================================================

/-- `X - 4` and `X - 3` are coprime: their difference `4 - 3 = 1` is a unit. -/
theorem linFactors_isCoprime : IsCoprime linFactor4 linFactor3 := by
  show IsCoprime (X - C (4 : ZMod 11)) (X - C 3)
  exact isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (by decide))

/-- `X - 4` is coprime to the cubic: `4` is not a root of the cubic. -/
theorem linFactor4_cubic_isCoprime : IsCoprime linFactor4 cubicMod11 := by
  have h : IsRelPrime linFactor4 cubicMod11 := by
    show IsRelPrime (X - C (4 : ZMod 11)) cubicMod11
    rw [(irreducible_X_sub_C (4 : ZMod 11)).isRelPrime_iff_not_dvd, dvd_iff_isRoot]
    exact cubicMod11_no_roots 4
  exact h.isCoprime

/-- `X - 3` is coprime to the cubic: `3` is not a root of the cubic. -/
theorem linFactor3_cubic_isCoprime : IsCoprime linFactor3 cubicMod11 := by
  have h : IsRelPrime linFactor3 cubicMod11 := by
    show IsRelPrime (X - C (3 : ZMod 11)) cubicMod11
    rw [(irreducible_X_sub_C (3 : ZMod 11)).isRelPrime_iff_not_dvd, dvd_iff_isRoot]
    exact cubicMod11_no_roots 3
  exact h.isCoprime

/-- **`q mod 11` is squarefree** — equivalently, 11 does not divide the
discriminant of `q`, so 11 is unramified. Built from the explicit factorization
`(X-4)(X-3)·cubic` into pairwise-coprime irreducibles. -/
theorem q_mod11_squarefree :
    Squarefree (linFactor4 * linFactor3 * cubicMod11) := by
  rw [squarefree_mul_iff]
  refine ⟨?_, ?_, cubicMod11_irreducible.squarefree⟩
  · exact (linFactor4_cubic_isCoprime.mul_left linFactor3_cubic_isCoprime).isRelPrime
  · rw [squarefree_mul_iff]
    exact ⟨linFactors_isCoprime.isRelPrime, linFactor4_irreducible.squarefree,
           linFactor3_irreducible.squarefree⟩

-- ============================================================================
-- § 5. The factorization is genuinely a factorization of `q mod 11`
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- **`q ≡ (X-4)(X-3)·cubicMod11  (mod 11)`** — the explicit factorization,
proved coefficient-by-coefficient (so these really are the factors of `q`). -/
theorem q_ℤ_mod11_factorization :
    q_ℤ.map (Int.castRingHom (ZMod 11)) = linFactor4 * linFactor3 * cubicMod11 := by
  have h1 : (linFactor4 : (ZMod 11)[X]) = X + C 7 := by
    simp only [linFactor4, sub_eq_add_neg, ← Polynomial.C_neg,
      show (-4 : ZMod 11) = 7 from by decide]
  have h2 : (linFactor3 : (ZMod 11)[X]) = X + C 8 := by
    simp only [linFactor3, sub_eq_add_neg, ← Polynomial.C_neg,
      show (-3 : ZMod 11) = 8 from by decide]
  rw [h1, h2]
  apply Polynomial.ext; intro n
  by_cases hn : n < 6
  · interval_cases n <;>
      simp only [Polynomial.coeff_map, q_ℤ, cubicMod11,
        Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_zero,
        Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_empty, Finset.sum_cons, Finset.sum_singleton,
        Finset.mem_cons, Finset.mem_singleton, Prod.mk.injEq,
        mul_ite, ite_mul, if_true, if_false] <;>
      decide
  · push_neg at hn
    have hqZ_deg : q_ℤ.natDegree ≤ 5 := by
      simp only [q_ℤ]; compute_degree
    have hrd_deg : ((X + C 7 : (ZMod 11)[X]) * (X + C 8) * cubicMod11).natDegree ≤ 5 := by
      simp only [cubicMod11]; compute_degree
    have hld : (q_ℤ.map (Int.castRingHom (ZMod 11))).natDegree < n := by
      have hle : (q_ℤ.map (Int.castRingHom (ZMod 11))).natDegree ≤ q_ℤ.natDegree :=
        Polynomial.natDegree_map_le
      omega
    have hrd : ((X + C 7 : (ZMod 11)[X]) * (X + C 8) * cubicMod11).natDegree < n := by
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hld,
        Polynomial.coeff_eq_zero_of_natDegree_lt hrd]

-- ============================================================================
-- § 6. Packaged Dedekind input at p = 11
-- ============================================================================

/-- **The mod-11 factor type of `q` is `(1, 1, 3)` into distinct irreducibles.**

A second unramified prime with the same factor type as `p = 7`:
* three irreducible factors, of degrees `1, 1, 3`,
* pairwise non-associated (distinct primes),
* with squarefree product (`p = 11` unramified),
* whose product is genuinely `q mod 11` (`q_ℤ_mod11_factorization`).

Combined with Dedekind's theorem (still a Mathlib gap; sibling track), this
gives a *second* 3-cycle in `Gal(q)`, corroborating `3 ∣ |Gal(q)|`. -/
theorem q_mod11_factor_type :
    Irreducible linFactor4 ∧ Irreducible linFactor3 ∧ Irreducible cubicMod11 ∧
    linFactor4.natDegree = 1 ∧ linFactor3.natDegree = 1 ∧ cubicMod11.natDegree = 3 ∧
    (¬ Associated linFactor4 linFactor3) ∧
    (¬ Associated linFactor4 cubicMod11) ∧
    (¬ Associated linFactor3 cubicMod11) ∧
    Squarefree (linFactor4 * linFactor3 * cubicMod11) ∧
    q_ℤ.map (Int.castRingHom (ZMod 11)) = linFactor4 * linFactor3 * cubicMod11 :=
  ⟨linFactor4_irreducible, linFactor3_irreducible, cubicMod11_irreducible,
   linFactor4_natDegree, linFactor3_natDegree, cubicMod11_natDegree,
   linFactors_not_associated, linFactor4_not_associated_cubic,
   linFactor3_not_associated_cubic, q_mod11_squarefree, q_ℤ_mod11_factorization⟩

end InverseGaloisOQ06OQ02P11
