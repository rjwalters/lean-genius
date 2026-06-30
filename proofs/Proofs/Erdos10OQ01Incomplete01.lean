/-
# Erdős Problem #10 — OQ-01 — Incomplete 01
## The elementary covering-congruence obstruction for k = 1 (a single power of two)

Erdős Problem #10 asks for a finite `k` such that every (sufficiently large) integer is a
prime plus at most `k` powers of `2`.  The parent file `Erdos10OQ01.lean` axiomatizes
Crocker's 1971 theorem that `k = 2` is insufficient.  The `k = 1` case — integers of the
form `2^a + p` — admits a completely **elementary** obstruction, due to Erdős (1950): a
covering system of congruences produces an arithmetic progression of integers `n` for which
the prime in *any* representation `n = 2^a + p` is forced to be one of six fixed small
primes.  In particular `n - 2^a` is composite for every `a` with `n - 2^a ∉ {3,5,7,13,17,241}`.

This file formalizes that obstruction with **no axioms and no sorries**.  It complements the
parent file, whose corresponding `k = 2` statement is (necessarily) axiomatized.

## The covering system

The six congruence classes for the exponent `a`,
  a ≡ 0 (mod 2),  a ≡ 0 (mod 3),  a ≡ 1 (mod 4),
  a ≡ 3 (mod 8),  a ≡ 7 (mod 12), a ≡ 23 (mod 24),
cover every natural number `a` (`covering`).  Each class is paired with a prime `q` whose
multiplicative order of `2` is the modulus, so that `2^a mod q` is *constant* on the class:

  | exponent class  | order of 2 | prime q | 2^a mod q |
  |-----------------|------------|---------|-----------|
  | a ≡ 0 (mod 2)   | 2          | 3       | 1         |
  | a ≡ 0 (mod 3)   | 3          | 7       | 1         |
  | a ≡ 1 (mod 4)   | 4          | 5       | 2         |
  | a ≡ 3 (mod 8)   | 8          | 17      | 8         |
  | a ≡ 7 (mod 12)  | 12         | 13      | 11        |
  | a ≡ 23 (mod 24) | 24         | 241     | 121       |

Choosing `n` with `n ≡ 2^a (mod q)` on each class — a single residue class modulo
`3·5·7·13·17·241 = 5592405` by the Chinese Remainder Theorem — forces `q ∣ (n - 2^a)` for
every `a`.  Since `q ∣ p` with `p` prime forces `p = q`, the only primes that can appear in
a representation `n = 2^a + p` are the six covering primes.

## References
- Erdős, P. (1950). "On integers of the form `2^k + p` and some related problems."
  Summa Brasiliensis Mathematicae 2, 113–123.
- Crocker, R. (1971). "On the sum of a prime and of two powers of two."
  Pacific J. Math. 36, 103–107.  (The `k = 2` statement, axiomatized in the parent file.)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

namespace Erdos10OQ01Incomplete01

/-! ## Part I: Periodicity of `2^a` modulo `q` -/

/-- If `2^d ≡ 1 (mod q)` and `q > 1`, then `2^a mod q` depends only on `a mod d`. -/
theorem pow_two_mod_period {q d : ℕ} (hq : 1 < q) (hd : 2 ^ d % q = 1) (a : ℕ) :
    2 ^ a % q = 2 ^ (a % d) % q := by
  conv_lhs => rw [← Nat.div_add_mod a d, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, hd, one_pow, Nat.one_mod_eq_one.mpr (by omega), one_mul,
    Nat.mod_mod]

/-! The six order facts.  Each says the multiplicative order of `2` modulo the prime divides
the stated modulus. -/

theorem ord3   : 2 ^ 2  % 3   = 1 := by decide
theorem ord7   : 2 ^ 3  % 7   = 1 := by decide
theorem ord5   : 2 ^ 4  % 5   = 1 := by decide
theorem ord17  : 2 ^ 8  % 17  = 1 := by decide
theorem ord13  : 2 ^ 12 % 13  = 1 := by decide
theorem ord241 : 2 ^ 24 % 241 = 1 := by decide

/-! ## Part II: The covering system -/

/-- **The covering system.** Every natural number `a` lies in at least one of the six
exponent classes. Proved by reduction to `a mod 24`. -/
theorem covering (a : ℕ) :
    a % 2 = 0 ∨ a % 3 = 0 ∨ a % 4 = 1 ∨ a % 8 = 3 ∨ a % 12 = 7 ∨ a % 24 = 23 := by
  omega

/-! ## Part III: The obstruction -/

/-- The six covering primes. -/
def coveringPrimes : Finset ℕ := {3, 5, 7, 13, 17, 241}

/-- **Covering obstruction.** If `n` lies in the CRT residue class (the six congruences
below), then for every exponent `a` there is a covering prime `q` with `2^a ≡ n (mod q)`,
i.e. `q ∣ (n - 2^a)`.

We combine three facts in each class with `omega` (treating each `_ % q` as an atom):
periodicity `2^a % q = 2^(a%d) % q`, the constant value `2^(a%d) % q = v` (`rewrite [ha]`
substitutes the class representative, then `decide` evaluates), and the hypothesis
`n % q = v`.  Using `rewrite` (not `rw`) avoids a trailing `rfl` that would force a slow
kernel reduction of the concrete power. -/
theorem obstruction {n : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121) (a : ℕ) :
    ∃ q ∈ coveringPrimes, 2 ^ a % q = n % q := by
  rcases covering a with ha | ha | ha | ha | ha | ha
  · refine ⟨3, by decide, ?_⟩
    have h1 : 2 ^ a % 3 = 2 ^ (a % 2) % 3 := pow_two_mod_period (by norm_num) ord3 a
    have h2 : 2 ^ (a % 2) % 3 = 1 := by rewrite [ha]; decide
    omega
  · refine ⟨7, by decide, ?_⟩
    have h1 : 2 ^ a % 7 = 2 ^ (a % 3) % 7 := pow_two_mod_period (by norm_num) ord7 a
    have h2 : 2 ^ (a % 3) % 7 = 1 := by rewrite [ha]; decide
    omega
  · refine ⟨5, by decide, ?_⟩
    have h1 : 2 ^ a % 5 = 2 ^ (a % 4) % 5 := pow_two_mod_period (by norm_num) ord5 a
    have h2 : 2 ^ (a % 4) % 5 = 2 := by rewrite [ha]; decide
    omega
  · refine ⟨17, by decide, ?_⟩
    have h1 : 2 ^ a % 17 = 2 ^ (a % 8) % 17 := pow_two_mod_period (by norm_num) ord17 a
    have h2 : 2 ^ (a % 8) % 17 = 8 := by rewrite [ha]; decide
    omega
  · refine ⟨13, by decide, ?_⟩
    have h1 : 2 ^ a % 13 = 2 ^ (a % 12) % 13 := pow_two_mod_period (by norm_num) ord13 a
    have h2 : 2 ^ (a % 12) % 13 = 11 := by rewrite [ha]; decide
    omega
  · refine ⟨241, by decide, ?_⟩
    have h1 : 2 ^ a % 241 = 2 ^ (a % 24) % 241 := pow_two_mod_period (by norm_num) ord241 a
    have h2 : 2 ^ (a % 24) % 241 = 121 := by rewrite [ha]; decide
    omega

/-! ## Part IV: Consequence for representations `n = 2^a + p` -/

/-- **Forced prime.** For `n` in the residue class, if `n = 2^a + p` with `p` prime, then
`p` is one of the six covering primes.  Equivalently: `n - 2^a` is composite unless it is
one of `{3, 5, 7, 13, 17, 241}`.  This is the elementary `k = 1` analogue of Crocker's
(axiomatized) `k = 2` theorem. -/
theorem prime_forced_small {n : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121)
    {a p : ℕ} (hp : p.Prime) (hrep : n = 2 ^ a + p) :
    p ∈ coveringPrimes := by
  obtain ⟨q, hqmem, hq⟩ := obstruction h3 h7 h5 h17 h13 h241 a
  -- From `2^a ≡ n (mod q)` and `n = 2^a + p` we get `q ∣ p`.
  have hle : 2 ^ a ≤ n := by omega
  have hmod : 2 ^ a ≡ n [MOD q] := hq
  have hqdvd : q ∣ (n - 2 ^ a) := (Nat.modEq_iff_dvd' hle).mp hmod
  have hqp : q ∣ p := by
    rwa [hrep, Nat.add_sub_cancel_left] at hqdvd
  -- A prime divisor of a prime equals it.
  have hq1 : q ≠ 1 := by fin_cases hqmem <;> norm_num
  rcases hp.eq_one_or_self_of_dvd q hqp with h | h
  · exact absurd h hq1
  · rwa [← h]

/-! ## Part V: Infinitely many such `n` (the arithmetic progression) -/

/-- The explicit CRT witness: `n₀ = 2036812` satisfies all six congruences. -/
theorem witness :
    (2036812 % 3 = 1) ∧ (2036812 % 7 = 1) ∧ (2036812 % 5 = 2) ∧
    (2036812 % 17 = 8) ∧ (2036812 % 13 = 11) ∧ (2036812 % 241 = 121) := by
  decide

/-- The CRT residue class is infinite: it is `{2036812 + 5592405 · t}`, and the modulus
`5592405 = 3·5·7·13·17·241` is divisible by each of the six prime moduli. -/
theorem residue_class_infinite :
    {n : ℕ | n % 3 = 1 ∧ n % 7 = 1 ∧ n % 5 = 2 ∧
             n % 17 = 8 ∧ n % 13 = 11 ∧ n % 241 = 121}.Infinite := by
  have hinj : Function.Injective (fun t : ℕ => 2036812 + 5592405 * t) := by
    intro a b hab
    simp only at hab
    omega
  have hmem : ∀ t : ℕ,
      (fun t : ℕ => 2036812 + 5592405 * t) t ∈
        {n : ℕ | n % 3 = 1 ∧ n % 7 = 1 ∧ n % 5 = 2 ∧
                 n % 17 = 8 ∧ n % 13 = 11 ∧ n % 241 = 121} := by
    intro t
    simp only [Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  exact Set.infinite_of_injective_forall_mem hinj hmem

/-- **Main result.** There are infinitely many integers `n` such that the only primes `p`
appearing in a representation `n = 2^a + p` are the six covering primes `{3,5,7,13,17,241}`.
Consequently, for each such `n`, `n - 2^a` is composite whenever it exceeds `241`. -/
theorem infinitely_many_forced :
    {n : ℕ | ∀ a p, p.Prime → n = 2 ^ a + p → p ∈ coveringPrimes}.Infinite := by
  apply residue_class_infinite.mono
  intro n hn
  obtain ⟨h3, h7, h5, h17, h13, h241⟩ := hn
  intro a p hp hrep
  exact prime_forced_small h3 h7 h5 h17 h13 h241 hp hrep

#check @prime_forced_small
#check @obstruction
#check @infinitely_many_forced

end Erdos10OQ01Incomplete01
