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
- Step 6 (`cofactor_one_and_prime`): proved (S8 ACT, ~8 LOC). The two-divisor
  analysis: `σ 1 m = (∑ properDivisors) + m` gives `∑ properDivisors = c`; since
  `c ∣ m`, `Nat.sum_properDivisors_dvd` forces this self-dividing proper-divisor
  sum to be `1` or `m`. The `m` branch contradicts `c < m`; the `1` branch gives
  `c = 1` and primality via `Nat.sum_properDivisors_eq_one_iff_prime`.
- Top-level theorem `euler_converse_self_contained`: proved (S8 ACT). Chains
  Steps 3–6 after the Archive 2-adic split `eq_two_pow_mul_odd`. The bounds
  feeding Step 6 are derived here: `1 < m` (else `σ 1 m = 1` forces `c = 0`,
  hence `m = 0`), `k ≠ 0` (else `n = m` is odd, contradicting evenness), and
  `c < m` from `m = mersenne(k+1)·c` with `mersenne(k+1) > 1` (as `2^(k+1) ≥ 4`).

## Status: VERIFIED (0 sorries, 0 axioms; Docker build clean)

All six steps and the capstone are machine-checked. The Archive is used only for
the foundational 2-adic split (`eq_two_pow_mul_odd`) and the `σ(2^k)` value; the
core two-divisor argument (Step 6) and the bound derivations are self-contained.

## Honesty Note

The mathematical content (Euler's converse) is already in Mathlib's Archive as a
single block; the gallery value of this file is the *named six-step decomposition*
exposing the algebraic skeleton, with the two-divisor heart (Step 6) and the
capstone's bound-chasing proved from first principles rather than quoted.

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
    (m c : ℕ) (hc_dvd : c ∣ m) (hc_lt : c < m) (_hm_lt : 1 < m)
    (h_sigma : σ 1 m = m + c) :
    c = 1 ∧ m.Prime := by
  -- `σ 1 m` splits as (proper-divisor sum) + m, so the proper-divisor sum is `c`.
  have hsplit : σ 1 m = (∑ i ∈ m.properDivisors, i) + m := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have hsum : (∑ i ∈ m.properDivisors, i) = c := by omega
  -- `c ∣ m` makes the proper-divisor sum a divisor of `m`; such a self-dividing
  -- proper-divisor sum is forced to be either `1` or `m` (`Nat.sum_properDivisors_dvd`).
  have hdvd : (∑ i ∈ m.properDivisors, i) ∣ m := by rw [hsum]; exact hc_dvd
  rcases Nat.sum_properDivisors_dvd hdvd with h1 | hmeq
  · -- Sum = 1: then `c = 1`, and proper-divisor sum `= 1` exactly characterizes primes.
    exact ⟨by omega, (Nat.sum_properDivisors_eq_one_iff_prime).mp h1⟩
  · -- Sum = m would force `c = m`, contradicting `c < m`.
    exfalso; omega

/-- **Euler's Converse — self-contained**. Composing Steps 1–6, every even perfect
number has the form `2^k · M_{k+1}` with `M_{k+1}` a Mersenne prime.
S3+ proof plan: `eq_two_pow_mul_odd` (Archive) splits `n = 2^k · m` with `m` odd,
then Steps 1–6 chain to identify `m = M_{k+1}` and `m.Prime`. -/
theorem euler_converse_self_contained
    (n : ℕ) (h_even : Even n) (h_perfect : n.Perfect) :
    ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) := by
  -- 2-adic split (Archive): `n = 2^k · m` with `m` odd.
  have hpos := h_perfect.2
  obtain ⟨k, m, rfl, hm_not_even⟩ := Theorems100.Nat.eq_two_pow_mul_odd hpos
  have hm_odd : Odd m := Nat.not_even_iff_odd.mp hm_not_even
  -- `m` is positive (an odd number is nonzero).
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hm_not_even
    · exact h
  -- `k ≠ 0`: if `k = 0` then `n = m` is odd, contradicting evenness.
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at h_even
    exact hm_not_even h_even
  -- Steps 3–5: the perfect equation, the Mersenne divisibility, and `σ m = m + c`.
  have h3 : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m :=
    mersenne_mul_sigma_eq_two_pow_mul k m hm_odd h_perfect
  obtain ⟨c, hc⟩ := mersenne_dvd_odd_part k m h3
  have h5 : σ 1 m = m + c := sigma_eq_self_add_cofactor k m c hc h3
  -- `m ≠ 1`: otherwise `σ 1 m = 1` forces `c = 0`, hence `m = 0` — impossible.
  have hm_ne_one : m ≠ 1 := by
    rintro rfl
    rw [show σ 1 1 = 1 by simp] at h5
    have hc0 : c = 0 := by omega
    rw [hc0, mul_zero] at hc
    simp at hc
  have hm_gt_one : 1 < m := by omega
  -- `mersenne (k+1) > 1` since `k ≥ 1` gives `2^(k+1) ≥ 4`.
  have hmer : 1 < mersenne (k + 1) := by
    have h4 : 4 ≤ 2 ^ (k + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [mersenne]; omega
  -- `c` is a proper divisor of `m`: `c ∣ m`, `0 < c`, and `c < m`.
  have hcm : c ∣ m := ⟨mersenne (k + 1), by rw [hc]; ring⟩
  have hc_pos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · rw [mul_zero] at hc; omega
    · exact h
  have hc_lt : c < m := by
    rw [hc]; exact (lt_mul_iff_one_lt_left hc_pos).mpr hmer
  -- Step 6: `c = 1` and `m` is prime; hence `m = mersenne (k+1)`.
  obtain ⟨hc1, hm_prime⟩ := cofactor_one_and_prime m c hcm hc_lt hm_gt_one h5
  have hm_eq : m = mersenne (k + 1) := by rw [hc, hc1, mul_one]
  exact ⟨k, hm_eq ▸ hm_prime, by rw [hm_eq]⟩

end SumOfDivisorsOQ02
