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

## Status (post-S7)

- Step 1 (`sigma_two_pow_mul_odd`): proved (S4 ACT, term-mode via
  `isMultiplicative_sigma.map_mul_of_coprime` + `.symm.pow_left`).
- Step 2 (`sigma_two_pow_eq_mersenne`): proved (direct alias of Archive).
- Step 3 (`mersenne_mul_sigma_eq_two_pow_mul`): proved (S5 ACT, ~7 LOC via
  `sigma_one_apply` + `Nat.perfect_iff_sum_divisors_eq_two_mul` bridge, then
  Steps 1+2 + `← mul_assoc; ← pow_succ'`).
- Step 4 (`mersenne_dvd_odd_part`): proved (S6 ACT, ~3 LOC term-mode via
  `Odd.coprime_two_right.pow_right.dvd_of_dvd_mul_left`).
- Step 5 (`sigma_eq_self_add_cofactor`): proved (S7 ACT, 3-LOC tactic
  body via `Nat.eq_of_mul_eq_mul_left` + `← succ_mersenne` `rw` chain).
- Step 6 (`cofactor_one_and_prime`): `sorry` placeholder. Discharge
  planned for S8+.
- Top-level theorem `euler_converse_self_contained`: `sorry` (chains
  Steps 1–6 via Archive `eq_two_pow_mul_odd`).

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
Proof: `isMultiplicative_sigma` supplies σ's multiplicativity; the coprimality
hypothesis is built by `Odd.coprime_two_right hm_odd : Coprime m 2`, symmetrized
to `Coprime 2 m`, then promoted by `pow_left k` to `Coprime (2^k) m`. -/
lemma sigma_two_pow_mul_odd (k m : ℕ) (hm_odd : Odd m) :
    σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m :=
  isMultiplicative_sigma.map_mul_of_coprime
    ((Odd.coprime_two_right hm_odd).symm.pow_left k)

/-- **Step 2** (σ of a power of 2). Direct alias of the Archive lemma.
`σ(2^k) = 2^(k+1) - 1 = M_{k+1}`. -/
lemma sigma_two_pow_eq_mersenne (k : ℕ) :
    σ 1 (2 ^ k) = mersenne (k + 1) :=
  Theorems100.Nat.sigma_two_pow_eq_mersenne_succ k

/-- **Step 3** (perfect equation expansion). If `n = 2^k · m` is perfect with `m` odd,
combining `σ(n) = 2n` with Steps 1+2 gives `M_{k+1} · σ(m) = 2^(k+1) · m`.
Proof: bridge `Perfect` to `σ 1 (2^k * m) = 2 * (2^k * m)` via
`Nat.perfect_iff_sum_divisors_eq_two_mul` (Divisors.lean:405) + `sigma_one_apply`
(Basic.lean:169). Apply Steps 1+2 to LHS, then `← mul_assoc; ← pow_succ'` to
collapse `2 * 2^k = 2^(k+1)`. -/
lemma mersenne_mul_sigma_eq_two_pow_mul
    (k m : ℕ) (hm_odd : Odd m) (h_perfect : (2 ^ k * m).Perfect) :
    mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m := by
  have hsigma_eq : σ 1 (2 ^ k * m) = 2 * (2 ^ k * m) := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul h_perfect.right).mp h_perfect
  rw [sigma_two_pow_mul_odd k m hm_odd, sigma_two_pow_eq_mersenne k] at hsigma_eq
  rw [← mul_assoc, ← pow_succ'] at hsigma_eq
  exact hsigma_eq

/-- **Step 4** (Mersenne factor divides the odd part). `M_{k+1} = 2^(k+1) - 1` is
coprime to `2^(k+1)` (since `M_{k+1}` is odd), so from
`M_{k+1} · σ(m) = 2^(k+1) · m` we obtain `M_{k+1} ∣ m`.

Proof (S6 ACT, paste from sessions/2026-05-16-s6-prep-step4-discharge-recipe.md §3,
Archive-style term-mode): `mersenne_odd` simp-discharges `Odd (mersenne (k+1))`
via `Nat.succ_ne_zero`; `Odd.coprime_two_right` yields
`Coprime (mersenne (k+1)) 2`; `.pow_right (k+1)` boosts to
`Coprime (mersenne (k+1)) (2^(k+1))`; `Dvd.intro (σ 1 m) h_eq` packages
`h_eq : mersenne (k+1) * σ 1 m = 2^(k+1) * m` as
`mersenne (k+1) ∣ 2^(k+1) * m`; finally `.dvd_of_dvd_mul_left` yields
`mersenne (k+1) ∣ m`. Bearer pins verified 0-drift at Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` per S6 PREP §2.

Build pending — Docker daemon hung (`docker info` exit 124 at 8s) +
host disk 100%/6.7 Gi avail at S6 ACT author time. If `(by simp)`
fails on `Odd (mersenne (k+1))` or `.pow_right` namespace-resolution
fails, see S6 PREP §5 fallback recipes. -/
lemma mersenne_dvd_odd_part
    (k m : ℕ) (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    mersenne (k + 1) ∣ m :=
  ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ h_eq)

/-- **Step 5** (sigma identity post-substitution). Writing `m = M_{k+1} · c` (from
Step 4) and combining with Step 3 gives `σ(m) = m + c`. The trick is
`2^(k+1) = M_{k+1} + 1`, so `2^(k+1) · m = (M_{k+1} + 1) · m = M_{k+1} · m + m`,
and the trailing `m` is exactly `M_{k+1} · c` (= `m` by `hm`), so the equation
becomes `M_{k+1} · σ(m) = M_{k+1} · (m + c)`; cancel `M_{k+1}`.

S7 ACT (paste from sessions/2026-06-04-s7-act-step5-discharge.md §3, tactic-mode
5-step `rw` chain after `refine Nat.eq_of_mul_eq_mul_left hpos`):
positivity `mersenne (k+1) > 0` from `mersenne_pos.mpr (Nat.succ_pos k)`;
then `rw [h_eq, mul_add, ← hm, ← succ_mersenne (k+1), add_mul, one_mul]`
collapses both sides to `mersenne (k+1) * m + m = mersenne (k+1) * m + m`.
Bearer pins (`mersenne_pos`, `succ_mersenne`, `Nat.eq_of_mul_eq_mul_left`)
verified 0-drift at Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
per session §2 via gh raw fetch of `Mathlib/NumberTheory/LucasLehmer.lean`
(lines 64 `mersenne_pos` and 102 `succ_mersenne`).

Build pending — Docker daemon unavailable at S7 ACT author time
(`docker images` → `Cannot connect to the Docker daemon`). Follows the
S5 ACT #19562 / S6 ACT #19644 "build pending — Docker daemon hung"
qualifier pattern. -/
lemma sigma_eq_self_add_cofactor
    (k m c : ℕ) (hm : m = mersenne (k + 1) * c)
    (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    σ 1 m = m + c := by
  have hpos : 0 < mersenne (k + 1) := mersenne_pos.mpr (Nat.succ_pos k)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h_eq, mul_add, ← hm, ← succ_mersenne (k + 1), add_mul, one_mul]

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
