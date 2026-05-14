/-
# Euler's Converse for Even Perfect Numbers (Self-Contained Scaffold)

## What This File Provides

A pedagogical decomposition of Euler's 1747 theorem — every even perfect number
has the form `n = 2^k · (2^(k+1) - 1)` where `2^(k+1) - 1` is a Mersenne prime —
into 6 named intermediate lemmas exposing the algebraic skeleton:

  Step 1. σ-multiplicativity over coprime factorizations.
  Step 2. σ(2^k) = M_{k+1}.
  Step 3. Perfect equation yields M_{k+1} · σ(m) = 2^(k+1) · m.
  Step 4. M_{k+1} divides the odd part m.
  Step 5. Substitution gives σ(m) = m + c with c = m / M_{k+1}.
  Step 6. The two-divisor analysis forces c = 1 and m.Prime.

The bundled Archive proof
`Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`
performs all six steps in a single block; this file exposes them named.

## S2 SCAFFOLD Status

- Step 2 (`sigma_two_pow_eq_mersenne`): proved (direct alias of Archive).
- Steps 1, 3, 4, 5, 6: `sorry` placeholders. Discharge planned for S3+.
- Top-level theorem `euler_converse_self_contained`: `sorry` (chains steps).

## Honesty Note

If the per-step proofs in S3+ collapse to direct quotations of the Archive proof's
internal structure (which is the expected outcome), the gallery value is
documentation/naming only. The slug should then be closed as
"covered-by-parent / pedagogical-only".

See `research/problems/sum-of-divisors-oq-02/knowledge.md` for the
detailed proof skeleton + Mathlib API inventory.
-/
import Archive.Wiedijk100Theorems.PerfectNumbers
import Mathlib.Tactic

namespace SumOfDivisorsOQ02

open ArithmeticFunction Finset Nat
open scoped sigma

/-- **Step 1** (sigma multiplicativity, specialized to `2^k · m` with `m` odd).
Since `m` is odd, `gcd(2^k, m) = 1`, so σ(2^k · m) = σ(2^k) · σ(m).
S3+ proof plan: `isMultiplicative_sigma.map_mul_of_coprime
((Odd.coprime_two_right hm_odd).pow_right _)` (mirroring the Archive line). -/
lemma sigma_two_pow_mul_odd (k m : ℕ) (hm_odd : Odd m) :
    σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m := by
  sorry

/-- **Step 2** (σ of a power of 2). Direct alias of the Archive lemma.
`σ(2^k) = 2^(k+1) - 1 = M_{k+1}`. -/
lemma sigma_two_pow_eq_mersenne (k : ℕ) :
    σ 1 (2 ^ k) = mersenne (k + 1) :=
  Theorems100.Nat.sigma_two_pow_eq_mersenne_succ k

/-- **Step 3** (perfect equation expansion). If `n = 2^k · m` is perfect with `m` odd
and `0 < m`, combining `σ(n) = 2n` with Steps 1+2 gives `M_{k+1} · σ(m) = 2^(k+1) · m`.
S3+ proof plan: rewrite via `Nat.perfect_iff_sum_divisors_eq_two_mul`, apply Steps 1+2,
then `← mul_assoc, ← pow_succ'` (mirroring the Archive). -/
lemma mersenne_mul_sigma_eq_two_pow_mul
    (k m : ℕ) (hm_odd : Odd m) (h_perfect : (2 ^ k * m).Perfect) :
    mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m := by
  sorry

/-- **Step 4** (Mersenne factor divides the odd part). `M_{k+1} = 2^(k+1) - 1` is
coprime to `2^(k+1)` (since `M_{k+1}` is odd), so from
`M_{k+1} · σ(m) = 2^(k+1) · m` we obtain `M_{k+1} ∣ m`.
S3+ proof plan: `((Odd.coprime_two_right ?).pow_right _).dvd_of_dvd_mul_left` on
`Dvd.intro _ h_eq` (Archive style). -/
lemma mersenne_dvd_odd_part
    (k m : ℕ) (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    mersenne (k + 1) ∣ m := by
  sorry

/-- **Step 5** (sigma identity post-substitution). Writing `m = M_{k+1} · c` (from
Step 4) and combining with Step 3 gives `σ(m) = m + c`. The trick is `2^(k+1) = M_{k+1} + 1`,
so `2^(k+1) · c = (M_{k+1} + 1) · c = M_{k+1} · c + c = m + c`.
S3+ proof plan: substitute `m`, cancel `M_{k+1}` from `mersenne_mul_sigma_eq_two_pow_mul`,
then rewrite `2^(k+1) = M_{k+1} + 1` via `succ_mersenne`. -/
lemma sigma_eq_self_add_cofactor
    (k m c : ℕ) (hm : m = mersenne (k + 1) * c)
    (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    σ 1 m = m + c := by
  sorry

/-- **Step 6** (two-divisor forces primality). If `σ(m) = m + c` with `c ∣ m`
and `c < m` (witness: `m > 1`, so `c = 1` is the only sub-`m` divisor option),
then `c = 1` and `m.Prime`.
S3+ proof plan: `Nat.sum_divisors_eq_sum_properDivisors_add_self`, then
`Nat.sum_properDivisors_dvd` case-split. The `c = 1` branch invokes
`Nat.sum_properDivisors_eq_one_iff_prime`. -/
lemma cofactor_one_and_prime
    (m c : ℕ) (hc_dvd : c ∣ m) (hc_lt : c < m) (hm_lt : 1 < m)
    (h_sigma : σ 1 m = m + c) :
    c = 1 ∧ m.Prime := by
  sorry

/-- **Euler's Converse — self-contained**. Composing Steps 1–6, every even perfect
number has the form `2^k · M_{k+1}` with `M_{k+1}` a Mersenne prime.
S3+ proof plan: `eq_two_pow_mul_odd` (Archive) splits `n = 2^k · m` with `m` odd,
then Steps 1–6 chain to identify `m = M_{k+1}` and `m.Prime`. -/
theorem euler_converse_self_contained
    (n : ℕ) (h_even : Even n) (h_perfect : n.Perfect) :
    ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) := by
  sorry

end SumOfDivisorsOQ02
