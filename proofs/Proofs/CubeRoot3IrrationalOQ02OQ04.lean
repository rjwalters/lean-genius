/-
# Eisenstein Irreducibility for Squarefree Radicands

**Open Question OQ-04** (from `cube-root-3-irrational-oq-02`, the Eisenstein proof of
∛3's irrationality):

> Does the Eisenstein approach extend to **non-prime** radicands? For example, `X^n - 6`
> is Eisenstein-irreducible at `p = 2` or `p = 3` (both work: `2 | 6`, `4 ∤ 6`, and
> `3 | 6`, `9 ∤ 6`). What about `X^n - 30`? Eisenstein applies at `p = 2, 3` or `5` — any
> **squarefree** `m` gives an Eisenstein-irreducible `X^n - m`. Where does the criterion
> fail?

## What This File Adds

The parent chain (`CubeRoot2IrrationalOQ03`) already proves a `sqfree_factor` criterion:
`X^n - m` is irreducible over ℚ **provided the caller exhibits a specific prime `p` with
`p | m` and `p² ∤ m`**. That places the burden of finding a good prime on the user.

This file removes that burden and pins down the exact boundary of the method:

1. **Existence of an Eisenstein prime** (`squarefree_has_eisenstein_prime`): for any
   squarefree `m ≥ 2`, a suitable prime `p` (with `p ∣ m`, `p² ∤ m`) *always exists* — it
   is any prime factor, since squarefreeness makes `p² ∤ m` automatic.

2. **Single-hypothesis criterion** (`irreducible_X_pow_sub_C_of_squarefree`):
   `Squarefree m → 2 ≤ m → 2 ≤ n → Irreducible (X^n - C m)` over ℚ. Keyed only on
   `Squarefree m`; the prime is discharged internally. This is the clean statement the
   open question asks for.

3. **Corollaries for squarefree radicands**: `X^n - m` has no rational root, `m^(1/n)` is
   irrational, and `[ℚ(m^(1/n)) : ℚ] = n` — all for *any* squarefree `m ≥ 2`, with `X^n - 30`
   and `X^n - 6` as the concrete instances named in the question.

4. **The sharp boundary** (`Part V`). Squarefreeness is **sufficient but not necessary**:
   `X² - 12` is irreducible even though `12 = 2²·3` is not squarefree (Eisenstein still
   applies at `p = 3`, which divides 12 to the first power). The real dividing line is
   whether `m` has *any* prime factor to the first power. When it does not — i.e. when `m`
   is **powerful** (every prime factor appears squared) — no Eisenstein prime exists
   (`powerful_no_eisenstein_prime`), and irreducibility can genuinely fail:
   `X² - 4 = (X - 2)(X + 2)` is reducible (`X_sq_sub_four_reducible`). So the criterion
   cannot be pushed past the "has a prime factor to the first power" condition, and
   squarefree is the natural clean sufficient hypothesis.

## Status: 0 sorries, 0 axioms
-/

import Proofs.CubeRoot2IrrationalOQ03
import Mathlib.NumberTheory.Real.Irrational

open Polynomial IntermediateField CubeRoot2IrrationalOQ03

namespace CubeRoot3IrrationalOQ02OQ04

/-! ## Part I: Every squarefree `m ≥ 2` has an Eisenstein prime -/

/-- For a squarefree `m ≥ 2`, there is a prime `p` with `p ∣ m` and `p² ∤ m`.

    Any prime factor works: `m ≥ 2` guarantees one exists, and squarefreeness
    (`p * p ∣ m → IsUnit p`) forbids `p² ∣ m` since a prime is not a unit. -/
theorem squarefree_has_eisenstein_prime (m : ℕ) (hsq : Squarefree m) (hm : 2 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ¬ p ^ 2 ∣ m := by
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  refine ⟨p, hp, hpdvd, ?_⟩
  intro hp2
  -- p² ∣ m means p * p ∣ m, so squarefreeness forces IsUnit p — i.e. p = 1, impossible.
  rw [pow_two] at hp2
  have hu : p = 1 := Nat.isUnit_iff.mp (hsq p hp2)
  have := hp.two_le
  omega

/-! ## Part II: The single-hypothesis squarefree criterion -/

/-- **Squarefree Eisenstein criterion.** For any squarefree `m ≥ 2` and any `n ≥ 2`,
    `X^n - m` is irreducible over ℚ.

    Unlike `eisenstein_X_pow_sub_of_sqfree_factor`, the caller need not name a prime:
    squarefreeness supplies one via `squarefree_has_eisenstein_prime`. This is the direct
    answer to "does Eisenstein extend to non-prime radicands?" — yes, to every squarefree
    radicand. -/
theorem irreducible_X_pow_sub_C_of_squarefree (n m : ℕ) (hn : 2 ≤ n)
    (hsq : Squarefree m) (hm : 2 ≤ m) :
    Irreducible (X ^ n - C (m : ℚ) : ℚ[X]) := by
  obtain ⟨p, hp, hpdvd, hp2⟩ := squarefree_has_eisenstein_prime m hsq hm
  exact eisenstein_X_pow_sub_of_sqfree_factor n m p hn hp hpdvd hp2 (by omega)

/-! ## Part III: No rational roots, for any squarefree radicand -/

/-- An irreducible polynomial of natDegree ≥ 2 has no root in its base field.

    (Generic version of the argument in `CubeRoot3IrrationalOQ02`: a root gives a linear
    factor `X - C q`, which can be neither a unit nor a cofactor-unit without collapsing
    the degree to 1.) -/
theorem no_root_of_irreducible_natDegree_ge_two {q : ℚ} {f : ℚ[X]}
    (hirr : Irreducible f) (hdeg : 2 ≤ f.natDegree) : f.eval q ≠ 0 := by
  intro hroot
  obtain ⟨R, hR⟩ := dvd_iff_isRoot.mpr hroot
  cases hirr.isUnit_or_isUnit hR with
  | inl h =>
    have := Polynomial.natDegree_eq_zero_of_isUnit h
    rw [natDegree_X_sub_C] at this
    omega
  | inr h =>
    have hRdeg : R.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit h
    have hf_ne : f ≠ 0 := hirr.ne_zero
    have hq_ne : (X - C q : ℚ[X]) ≠ 0 := X_sub_C_ne_zero q
    have hR_ne : R ≠ 0 := by rintro rfl; rw [mul_zero] at hR; exact hf_ne hR
    have : f.natDegree = 1 := by
      rw [hR, natDegree_mul hq_ne hR_ne, natDegree_X_sub_C, hRdeg]
    omega

/-- For any squarefree `m ≥ 2` and `n ≥ 2`, `X^n - m` has no rational root. -/
theorem X_pow_sub_squarefree_no_rat_root (n m : ℕ) (hn : 2 ≤ n)
    (hsq : Squarefree m) (hm : 2 ≤ m) (q : ℚ) :
    (X ^ n - C (m : ℚ)).eval q ≠ 0 := by
  apply no_root_of_irreducible_natDegree_ge_two
    (irreducible_X_pow_sub_C_of_squarefree n m hn hsq hm)
  rw [natDegree_X_pow_sub_nat_eq (by omega) (by omega)]
  exact hn

/-! ## Part IV: Irrationality and algebraic degree for squarefree radicands -/

/-- **Irrationality of `m^(1/n)` for squarefree `m`.** For any squarefree `m ≥ 2` and
    `n ≥ 2`, the real `n`-th root `m^(1/n)` is irrational.

    This is the OQ-02 argument (Eisenstein → no rational root → irrational) generalized
    from the prime radicand `3` to every squarefree radicand. -/
theorem irrational_nthRoot_of_squarefree (n m : ℕ) (hn : 2 ≤ n)
    (hsq : Squarefree m) (hm : 2 ≤ m) :
    Irrational ((m : ℝ) ^ ((1 : ℝ) / n)) := by
  rintro ⟨q, hq⟩
  -- q^n = m over ℝ, hence over ℚ, hence q is a rational root of X^n - m.
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hqn_real : (q : ℝ) ^ n = m := by
    rw [hq, ← Real.rpow_natCast ((m : ℝ) ^ ((1 : ℝ) / n)) n,
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ m)]
    rw [one_div, inv_mul_cancel₀ hn0, Real.rpow_one]
  have hqn : q ^ n = (m : ℚ) := by exact_mod_cast hqn_real
  have heval : (X ^ n - C (m : ℚ)).eval q = 0 := by
    simp [eval_sub, eval_pow, eval_X, hqn]
  exact X_pow_sub_squarefree_no_rat_root n m hn hsq hm q heval

/-- **Algebraic degree for squarefree radicands.** `[ℚ(m^(1/n)) : ℚ] = n` for any
    squarefree `m ≥ 2` and `n ≥ 2`. Repackages `adjoin_nthRoot_finrank` with the prime
    discharged by squarefreeness. -/
theorem adjoin_nthRoot_finrank_of_squarefree (n m : ℕ) (hn : 2 ≤ n)
    (hsq : Squarefree m) (hm : 2 ≤ m) :
    Module.finrank ℚ ℚ⟮(m : ℝ) ^ ((1 : ℝ) / ↑n)⟯ = n := by
  obtain ⟨p, hp, hpdvd, hp2⟩ := squarefree_has_eisenstein_prime m hsq hm
  exact adjoin_nthRoot_finrank n m p hn hp hpdvd hp2 (by omega)

/-! ## Concrete squarefree radicands from the open question -/

/-- `6 = 2·3` is squarefree (built multiplicatively from primes, keeping the file
    `native_decide`-free and hence axiom-free). -/
theorem squarefree_six : Squarefree (6 : ℕ) := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.squarefree_mul (by norm_num)]
  exact ⟨Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩

/-- `30 = 2·3·5` is squarefree. -/
theorem squarefree_thirty : Squarefree (30 : ℕ) := by
  rw [show (30 : ℕ) = 2 * 15 from rfl, Nat.squarefree_mul (by norm_num)]
  refine ⟨Nat.prime_two.prime.squarefree, ?_⟩
  rw [show (15 : ℕ) = 3 * 5 from rfl, Nat.squarefree_mul (by norm_num)]
  exact ⟨Nat.prime_three.prime.squarefree,
    (by norm_num : Nat.Prime 5).prime.squarefree⟩

/-- `X^n - 30` is irreducible over ℚ for every `n ≥ 2` — the flagship non-prime example
    from the open question. -/
theorem irreducible_X_pow_sub_thirty (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (X ^ n - C (30 : ℚ) : ℚ[X]) :=
  irreducible_X_pow_sub_C_of_squarefree n 30 hn squarefree_thirty (by norm_num)

/-- `X^n - 6` is irreducible over ℚ for every `n ≥ 2`. -/
theorem irreducible_X_pow_sub_six (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (X ^ n - C (6 : ℚ) : ℚ[X]) :=
  irreducible_X_pow_sub_C_of_squarefree n 6 hn squarefree_six (by norm_num)

/-- ⁿ√30 is irrational for every `n ≥ 2` (concrete corollary of the squarefree criterion). -/
theorem irrational_nthRoot_thirty (n : ℕ) (hn : 2 ≤ n) :
    Irrational ((30 : ℝ) ^ ((1 : ℝ) / n)) :=
  irrational_nthRoot_of_squarefree n 30 hn squarefree_thirty (by norm_num)

/-! ## Part V: The sharp boundary of the criterion -/

/-- **Squarefree is sufficient but not necessary.** `X² - 12` is irreducible even though
    `12 = 2²·3` is *not* squarefree: Eisenstein still applies at `p = 3`, which divides
    12 to the first power (`3 ∣ 12`, `9 ∤ 12`). So the criterion reaches strictly beyond
    squarefree radicands — the true requirement is a prime factor to the first power. -/
theorem irreducible_X_sq_sub_twelve : Irreducible (X ^ 2 - C (12 : ℚ) : ℚ[X]) :=
  -- Squarefreeness fails for 12, yet Eisenstein at p = 3 succeeds directly.
  eisenstein_X_pow_sub_of_sqfree_factor 2 12 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **Where the method stops: powerful `m`.** If every prime factor of `m` divides it at
    least twice (`m` is *powerful*), then no prime satisfies the Eisenstein hypothesis
    `p ∣ m ∧ p² ∤ m`. Squarefree `m ≥ 2` is exactly the opposite extreme, which is why it
    always supplies an Eisenstein prime. -/
theorem powerful_no_eisenstein_prime (m : ℕ)
    (hpow : ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m) :
    ¬ ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ¬ p ^ 2 ∣ m := by
  rintro ⟨p, hp, hpdvd, hp2⟩
  exact hp2 (hpow p hp hpdvd)

/-- **Irreducibility genuinely fails past the boundary.** `X² - 4 = (X - 2)(X + 2)` is
    reducible over ℚ. Here `m = 4 = 2²` is powerful: its only prime factor, 2, divides it
    twice, so `powerful_no_eisenstein_prime` applies and there is no Eisenstein prime — and
    indeed the polynomial is reducible. This witnesses that the "prime factor to the first
    power" hypothesis (of which squarefree is the clean special case) cannot be dropped. -/
theorem X_sq_sub_four_reducible : ¬ Irreducible (X ^ 2 - C (4 : ℚ) : ℚ[X]) := by
  intro hirr
  -- Exhibit the factorization X² - 4 = (X - 2)(X + 2); neither factor is a unit.
  have hfac : (X ^ 2 - C (4 : ℚ)) = (X - C 2) * (X + C 2) := by
    have h4 : (C 4 : ℚ[X]) = C 2 * C 2 := by rw [← C_mul]; norm_num
    rw [h4]; ring
  rcases hirr.isUnit_or_isUnit hfac with h | h
  · exact (Polynomial.not_isUnit_of_natDegree_pos _ (by rw [natDegree_X_sub_C]; norm_num)) h
  · exact (Polynomial.not_isUnit_of_natDegree_pos _ (by rw [natDegree_X_add_C]; norm_num)) h

/-- `4` is powerful (sanity check feeding `X_sq_sub_four_reducible`): its only prime
    factor 2 divides it twice. -/
theorem four_powerful : ∀ p : ℕ, p.Prime → p ∣ 4 → p ^ 2 ∣ 4 := by
  intro p hp hpdvd
  -- p ∣ 4 = 2² and p prime ⟹ p ∣ 2 ⟹ p = 2, whence p² = 4 ∣ 4.
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hpdvd)
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
  subst this; norm_num

end CubeRoot3IrrationalOQ02OQ04
