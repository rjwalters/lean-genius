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
import Mathlib.Data.Real.Irrational

open Polynomial CubeRoot2IrrationalOQ03

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
  -- p² ∣ m means p * p ∣ m, so squarefreeness forces IsUnit p — impossible for a prime.
  rw [pow_two] at hp2
  exact hp.not_unit (hsq p hp2)

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
    simp [eval_sub, eval_pow, eval_X, eval_C, hqn]
  exact X_pow_sub_squarefree_no_rat_root n m hn hsq hm q heval

/-- **Algebraic degree for squarefree radicands.** `[ℚ(m^(1/n)) : ℚ] = n` for any
    squarefree `m ≥ 2` and `n ≥ 2`. Repackages `adjoin_nthRoot_finrank` with the prime
    discharged by squarefreeness. -/
theorem adjoin_nthRoot_finrank_of_squarefree (n m : ℕ) (hn : 2 ≤ n)
    (hsq : Squarefree m) (hm : 2 ≤ m) :
    Module.finrank ℚ ℚ⟮(m : ℝ) ^ ((1 : ℝ) / ↑n)⟯ = n := by
  obtain ⟨p, hp, hpdvd, hp2⟩ := squarefree_has_eisenstein_prime m hsq hm
  exact adjoin_nthRoot_finrank n m p hn hp hpdvd hp2 (by omega)

/-! ## Part V: The sharp boundary of the criterion -/

/-- `X^n - 30` is irreducible over ℚ for every `n ≥ 2` — the flagship non-prime example
    from the open question. `30 = 2·3·5` is squarefree. -/
theorem irreducible_X_pow_sub_thirty (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (X ^ n - C (30 : ℚ) : ℚ[X]) :=
  irreducible_X_pow_sub_C_of_squarefree n 30 hn (by decide) (by norm_num)

/-- `X^n - 6` is irreducible over ℚ for every `n ≥ 2`. `6 = 2·3` is squarefree. -/
theorem irreducible_X_pow_sub_six (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (X ^ n - C (6 : ℚ) : ℚ[X]) :=
  irreducible_X_pow_sub_C_of_squarefree n 6 hn (by decide) (by norm_num)

/-- ⁿ√30 is irrational for every `n ≥ 2` (concrete corollary of the squarefree criterion). -/
theorem irrational_nthRoot_thirty (n : ℕ) (hn : 2 ≤ n) :
    Irrational ((30 : ℝ) ^ ((1 : ℝ) / n)) :=
  irrational_nthRoot_of_squarefree n 30 hn (by decide) (by norm_num)

/-- **Squarefree is sufficient but not necessary.** `X² - 12` is irreducible even though
    `12 = 2²·3` is *not* squarefree: Eisenstein still applies at `p = 3`, which divides
    12 to the first power (`3 ∣ 12`, `9 ∤ 12`). So the criterion reaches strictly beyond
    squarefree radicands — the true requirement is a prime factor to the first power. -/
theorem irreducible_X_sq_sub_twelve : Irreducible (X ^ 2 - C (12 : ℚ) : ℚ[X]) := by
  have h12 : ¬ Squarefree (12 : ℕ) := by decide
  -- Squarefree fails, yet Eisenstein at p = 3 succeeds directly.
  exact eisenstein_X_pow_sub_of_sqfree_factor 2 12 3 (by norm_num) (by norm_num)
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
  have hfac : (X ^ 2 - C (4 : ℚ)) = (X - C 2) * (X + C 2) := by ring
  rcases hirr.isUnit_or_isUnit hfac with h | h
  · exact (Polynomial.not_isUnit_of_natDegree_pos _ (by rw [natDegree_X_sub_C]; norm_num)) h
  · have hdeg : (X + C 2 : ℚ[X]).natDegree = 1 := by
      rw [show (X + C 2 : ℚ[X]) = X - C (-2) by ring, natDegree_X_sub_C]
    exact (Polynomial.not_isUnit_of_natDegree_pos _ (by rw [hdeg]; norm_num)) h

/-- `4` is powerful (sanity check feeding `X_sq_sub_four_reducible`): its only prime
    factor 2 divides it twice. -/
theorem four_powerful : ∀ p : ℕ, p.Prime → p ∣ 4 → p ^ 2 ∣ 4 := by
  intro p hp hpdvd
  interval_cases p <;> simp_all <;> omega

end CubeRoot3IrrationalOQ02OQ04
