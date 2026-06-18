/-
  Nth Root Irrationality OQ-02:
  Uniform prime-factorization approach to not-a-perfect-power lemmas

  The base file `NthRootIrrational.lean` proves the general theorem
  `irrational_nthRoot : ¬(∃ k : ℤ, k ^ n = m) → Irrational (m ^ (1/n))`, but
  it discharges each *not-a-perfect-power* hypothesis (`2` is not a perfect
  square, `3` is not a perfect cube, ...) by an ad-hoc bounded case analysis
  (`interval_cases` / `nlinarith` after deriving an explicit upper bound on the
  candidate root).  That style does **not** scale: certifying that a large value
  such as `1000003` is not a perfect square would require an `interval_cases`
  over roughly `1000` candidates, and certifying that `2` is not a perfect
  `100`-th power is hopeless that way.

  This file replaces those bounded arguments with a single, uniform
  **prime-factorization** criterion that scales to arbitrary values and
  arbitrary exponents:

      a positive `m` is a perfect `n`-th power  ⟹  for every prime `p`,
      `n ∣ (m.factorization p)`.

  Contrapositive (`not_perfect_pow_of_factorization`): if some prime `p` has an
  exponent in `m` that is **not** divisible by `n`, then `m` is not a perfect
  `n`-th power.  From this one lemma we obtain, with no case analysis:

  * `prime_not_perfect_pow` — no prime is a perfect `n`-th power (`n ≥ 2`),
    because the prime's own exponent is `1`.  This single result subsumes every
    `p_not_perfect_sq` / `p_not_perfect_cube` / ... lemma of the base file, for
    *all* primes and *all* exponents at once.
  * `not_perfect_pow_of_sq_not_dvd` — a value divisible by a prime `p` exactly
    once (`p ∣ m`, `p² ∤ m`) is not a perfect `n`-th power (`n ≥ 2`).  The two
    divisibility side-conditions are cheap `decide`s independent of the size of
    `m`, so this covers composite values (`6`, `12`, `2 · 1000003`, ...) as well.

  Bridging back through `Int.natAbs` (`not_perfect_pow_int`) feeds these into the
  base `irrational_nthRoot`, giving uniform irrationality corollaries that the
  bounded approach cannot reach (e.g. `Irrational (¹⁰⁰√2)`).

  Results (0 axioms, 0 sorries):
  - not_perfect_pow_of_factorization   (the uniform criterion)
  - not_perfect_pow_int                (ℕ ⟹ ℤ bridge via natAbs)
  - prime_not_perfect_pow              (primes, all exponents)
  - not_perfect_pow_of_sq_not_dvd      (single-prime-factor values)
  - irrational_nthRoot_prime           (irrationality of ⁿ√p)
  - irrational_nthRoot_of_sq_not_dvd   (irrationality of ⁿ√m)
  - Concrete corollaries that do not scale under bounded case analysis.
-/

import Mathlib
import Proofs.NthRootIrrational

set_option maxHeartbeats 1000000

namespace NthRootIrrationalOQ02

open NthRootIrrational

/-! ## Part 1: The Uniform Prime-Factorization Criterion

The heart of the generalization.  If `m = k ^ n` then, by
`Nat.factorization_pow`, every prime exponent of `m` is `n` times the
corresponding exponent of `k`, hence divisible by `n`.  Contrapositively, a
single prime whose exponent is *not* divisible by `n` certifies that `m` is not
a perfect `n`-th power — no search over candidate roots is required. -/

/-- **Uniform not-a-perfect-power criterion.**  If some prime exponent
`m.factorization p` of `m` is not divisible by `n`, then `m` is not a perfect
`n`-th power.  This is the prime-factorization replacement for the base file's
per-value `interval_cases` lemmas. -/
theorem not_perfect_pow_of_factorization {m n p : ℕ}
    (hndvd : ¬ n ∣ m.factorization p) : ¬ ∃ k : ℕ, k ^ n = m := by
  rintro ⟨k, rfl⟩
  apply hndvd
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  exact dvd_mul_right n _

/-! ## Part 2: From ℕ to ℤ

The base `irrational_nthRoot` phrases "not a perfect power" over `ℤ`.  Since
`(k ^ n).natAbs = k.natAbs ^ n`, an integer `n`-th root of a natural number
yields a natural `n`-th root, so it suffices to rule out natural roots. -/

/-- If `m` is not a perfect `n`-th power over `ℕ`, it is not one over `ℤ` either.
For `k ^ n = m` with `m : ℕ`, taking `Int.natAbs` gives `k.natAbs ^ n = m`. -/
theorem not_perfect_pow_int {m n : ℕ} (h : ¬ ∃ k : ℕ, k ^ n = m) :
    ¬ ∃ k : ℤ, k ^ n = (m : ℤ) := by
  rintro ⟨k, hk⟩
  refine h ⟨k.natAbs, ?_⟩
  have h2 := congrArg Int.natAbs hk
  rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2

/-! ## Part 3: Specializations

Two ready-to-use instances of the criterion.  Neither performs any search. -/

/-- **No prime is a perfect `n`-th power** for `n ≥ 2`: the prime's own exponent
is `1`, which is not divisible by `n`.  One lemma for every prime and every
exponent — replacing the entire `_not_perfect_sq` / `_not_perfect_cube` / ...
family of the base file. -/
theorem prime_not_perfect_pow {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) :
    ¬ ∃ k : ℕ, k ^ n = p := by
  apply not_perfect_pow_of_factorization (p := p)
  rw [hp.factorization_self]
  intro hdvd
  have := Nat.le_of_dvd one_pos hdvd
  omega

/-- **A value divisible by a prime exactly once is not a perfect power.**  If
`p ∣ m` but `p² ∤ m` (so `p` appears to exponent `1` in `m`), then `m` is not a
perfect `n`-th power for `n ≥ 2`.  The hypotheses are size-independent `decide`s,
so this handles composite values such as `6`, `12`, or `2 · 1000003`. -/
theorem not_perfect_pow_of_sq_not_dvd {m n p : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hn : 2 ≤ n) (hd : p ∣ m) (hnd : ¬ p ^ 2 ∣ m) : ¬ ∃ k : ℕ, k ^ n = m := by
  apply not_perfect_pow_of_factorization (p := p)
  have h1 : 1 ≤ m.factorization p :=
    (hp.pow_dvd_iff_le_factorization hm).mp (by simpa using hd)
  have h2 : ¬ 2 ≤ m.factorization p := fun hge =>
    hnd ((hp.pow_dvd_iff_le_factorization hm).mpr hge)
  have heq : m.factorization p = 1 := by omega
  rw [heq]
  intro hdvd
  have := Nat.le_of_dvd one_pos hdvd
  omega

/-! ## Part 4: Uniform Irrationality Corollaries

Feeding the criteria through the base `irrational_nthRoot`.  These reach values
and exponents the bounded approach cannot. -/

/-- **Irrationality of `ⁿ√p` for any prime `p` and any `n ≥ 2`.**  No bound on
the candidate root, no case analysis — uniform in both `p` and `n`. -/
theorem irrational_nthRoot_prime {p n : ℕ} (hp : p.Prime) (hn : 1 < n) :
    Irrational (nthRoot n p) :=
  irrational_nthRoot n p hn
    (not_perfect_pow_int (prime_not_perfect_pow hp (by omega)))

/-- **Irrationality of `ⁿ√m` whenever a prime divides `m` exactly once.**
Covers composite radicands via cheap divisibility checks. -/
theorem irrational_nthRoot_of_sq_not_dvd {m n p : ℕ} (hn : 1 < n) (hp : p.Prime)
    (hm : m ≠ 0) (hd : p ∣ m) (hnd : ¬ p ^ 2 ∣ m) :
    Irrational (nthRoot n m) :=
  irrational_nthRoot n m hn
    (not_perfect_pow_int (not_perfect_pow_of_sq_not_dvd hp hm (by omega) hd hnd))

/-! ## Part 5: Concrete Corollaries the Bounded Approach Cannot Reach

Each of these is a one-liner here.  Under the base file's `interval_cases`
strategy they would require enumerating hundreds of candidates (large primes)
or are outright infeasible (high exponents). -/

/-- `√2` irrational — the classic, now a special case. -/
theorem irrational_sqrt_two : Irrational (nthRoot 2 2) :=
  irrational_nthRoot_prime (by norm_num) (by norm_num)

/-- `√101` irrational.  No `interval_cases` over `k ≤ 10`. -/
theorem irrational_sqrt_101 : Irrational (nthRoot 2 101) :=
  irrational_nthRoot_prime (by norm_num) (by norm_num)

/-- `√1000003` irrational.  The bounded approach would enumerate ~1000
candidate roots; here the prime exponent argument is immediate. -/
theorem irrational_sqrt_1000003 : Irrational (nthRoot 2 1000003) :=
  irrational_nthRoot_prime (by norm_num) (by norm_num)

/-- `¹⁰⁰√2` irrational — *infeasible* under bounded case analysis, trivial here.
This is the key demonstration that the criterion is uniform in the exponent. -/
theorem irrational_hundredth_root_two : Irrational (nthRoot 100 2) :=
  irrational_nthRoot_prime (by norm_num) (by norm_num)

/-- `⁵√7` irrational. -/
theorem irrational_fifth_root_seven : Irrational (nthRoot 5 7) :=
  irrational_nthRoot_prime (by norm_num) (by norm_num)

/-- `√6` irrational — composite radicand, `2 ∣ 6` but `4 ∤ 6`. -/
theorem irrational_sqrt_six : Irrational (nthRoot 2 6) :=
  irrational_nthRoot_of_sq_not_dvd (by norm_num) (p := 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- `√12` irrational — `12 = 2² · 3`, certified via the lone prime `3`
(`3 ∣ 12`, `9 ∤ 12`), not via the square factor `2`. -/
theorem irrational_sqrt_twelve : Irrational (nthRoot 2 12) :=
  irrational_nthRoot_of_sq_not_dvd (by norm_num) (p := 3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- `∛12` irrational — same radicand, exponent `3`, uniform criterion. -/
theorem irrational_cbrt_twelve : Irrational (nthRoot 3 12) :=
  irrational_nthRoot_of_sq_not_dvd (by norm_num) (p := 3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end NthRootIrrationalOQ02
