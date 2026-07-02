/-
# Infinitely Many Primitive Abundant Numbers

A **primitive abundant number** is an abundant number all of whose proper
divisors are deficient -- i.e. a minimal abundant number under divisibility.
The sibling entry `abundant-number-oq-04-oq-01-oq-02` defines these and proves
that `20` is the least one. This entry proves the classical fact that there are
**infinitely many** of them.

## The construction

For an integer `k ≥ 2` and an odd prime `p` in the window
`2^k - 1 < p < 2^(k+1) - 1`, the number `n = 2^k · p` is primitive abundant:

* **Abundance.** Since `p` is coprime to `2^k`, the divisor sum is multiplicative,
  `σ(2^k·p) = (2^(k+1) - 1)(p + 1)`, and the abundance inequality `2n < σ(n)`
  reduces to exactly `p < 2^(k+1) - 1`.
* **Primitivity.** Every proper divisor of `2^k·p` is either a power of two
  `2^a` (always deficient, `Nat.Prime.deficient_pow`) or `2^a·p` with `a < k`;
  in the latter case `σ(2^a·p) < 2·2^a·p` reduces to `p > 2^(a+1) - 1`, which
  holds because `a + 1 ≤ k` gives `2^(a+1) - 1 ≤ 2^k - 1 < p`.

## Infinitude via Bertrand's postulate

Applying Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`) to the base
`2^k - 1` yields a prime `p` with `2^k - 1 < p ≤ 2·(2^k - 1) = 2^(k+1) - 2`,
which lands strictly inside the required window (and, by choosing the base to be
`2^k - 1` rather than `2^k`, dodges the perfect-number boundary `p = 2^(k+1) - 1`
entirely -- no Mersenne-prime special-casing needed). Since `2^k·p ≥ 2^k` grows
without bound, the primitive abundant numbers are unbounded, hence infinite.

All results are elementary and axiom-free.
-/
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace AbundantPrimitiveInfiniteOQ0104

open Finset Nat

/-- A **primitive abundant number**: abundant, yet every proper divisor is
deficient. (Same definition as the sibling `abundant-number-oq-04-oq-01-oq-02`,
restated here so this file is self-contained.) -/
abbrev IsPrimitiveAbundant (n : ℕ) : Prop :=
  n.Abundant ∧ ∀ d ∈ n.properDivisors, d.Deficient

/-! ### Elementary reformulations of abundance / deficiency via the divisor sum -/

/-- `n` is abundant iff `2n < σ(n)` where `σ(n) = ∑_{d ∣ n} d`. -/
theorem abundant_iff_two_mul_lt_sum_divisors {n : ℕ} :
    n.Abundant ↔ 2 * n < ∑ d ∈ n.divisors, d := by
  simp only [Nat.Abundant, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega

/-- `n` is deficient iff `σ(n) < 2n`. -/
theorem deficient_iff_sum_divisors_lt_two_mul {n : ℕ} :
    n.Deficient ↔ ∑ d ∈ n.divisors, d < 2 * n := by
  simp only [Nat.Deficient, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega

/-! ### The divisor sum of `2^a · p` -/

/-- Geometric sum in `ℕ`: `∑_{i<n} 2^i = 2^n - 1`. -/
theorem two_pow_geom (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [Finset.sum_range_succ, ih]; omega

/-- **Divisor sum of `2^a · p`** for an odd prime `p`:
`σ(2^a·p) = (2^(a+1) - 1)(p + 1)`, from multiplicativity of `σ` on the coprime
factorisation `2^a · p`. -/
theorem sum_divisors_two_pow_mul_prime {a p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ d ∈ (2 ^ a * p).divisors, d = (2 ^ (a + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ a) p :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left a
  rw [hcop.sum_divisors_mul]
  have e1 : ∑ d ∈ (2 ^ a).divisors, d = 2 ^ (a + 1) - 1 := by
    rw [Nat.sum_divisors_prime_pow Nat.prime_two]
    exact two_pow_geom (a + 1)
  have e2 : ∑ d ∈ p.divisors, d = p + 1 := by
    rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]; omega
  rw [e1, e2]

/-! ### The core construction -/

/-- For an odd prime `p` with `2^(a+1) - 1 < p`, the number `2^a · p` is
deficient. (Reduces to `2^(a+1) - 1 < p` after the divisor-sum formula.) -/
theorem deficient_two_pow_mul_prime {a p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : 2 ^ (a + 1) - 1 < p) : (2 ^ a * p).Deficient := by
  rw [deficient_iff_sum_divisors_lt_two_mul, sum_divisors_two_pow_mul_prime hp hp2]
  have hrw : 2 * (2 ^ a * p) = 2 ^ (a + 1) * p := by rw [pow_succ]; ring
  rw [hrw]
  have h1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ (a + 1) = c + 1 := ⟨2 ^ (a + 1) - 1, by omega⟩
  rw [hc]; simp only [Nat.add_sub_cancel]
  -- goal: c * (p + 1) < (c + 1) * p
  have hcp : c < p := by omega
  nlinarith [hcp]

/-- For `k ≥ 2` and an odd prime `p` with `p < 2^(k+1) - 1`, the number
`2^k · p` is abundant. (Reduces to `p < 2^(k+1) - 1` after the divisor-sum
formula.) -/
theorem abundant_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hhi : p < 2 ^ (k + 1) - 1) : (2 ^ k * p).Abundant := by
  rw [abundant_iff_two_mul_lt_sum_divisors, sum_divisors_two_pow_mul_prime hp hp2]
  have hrw : 2 * (2 ^ k * p) = 2 ^ (k + 1) * p := by rw [pow_succ]; ring
  rw [hrw]
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ (k + 1) = c + 1 := ⟨2 ^ (k + 1) - 1, by omega⟩
  rw [hc]; simp only [Nat.add_sub_cancel]
  -- goal: (c + 1) * p < c * (p + 1)
  have hcp : p < c := by omega
  nlinarith [hcp]

/-- **Core theorem.** For `k ≥ 2` and a prime `p` in the window
`2^k - 1 < p < 2^(k+1) - 1`, the number `2^k · p` is primitive abundant. -/
theorem isPrimitiveAbundant_two_pow_mul_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hlo : 2 ^ k - 1 < p) (hhi : p < 2 ^ (k + 1) - 1) :
    IsPrimitiveAbundant (2 ^ k * p) := by
  -- `p` is an odd prime: `p > 2^k - 1 ≥ 3`.
  have hp2 : p ≠ 2 := by
    have h4 : (4 : ℕ) ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  refine ⟨abundant_two_pow_mul_prime hp hp2 hhi, ?_⟩
  intro d hd
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨hdvd, hdlt⟩ := hd
  by_cases hpd : p ∣ d
  · -- `p ∣ d`: then `d = 2^a · p` with `a < k`.
    obtain ⟨e, rfl⟩ := hpd
    rw [mul_comm p e] at hdvd
    have hediv : e ∣ 2 ^ k := (mul_dvd_mul_iff_right hp.pos.ne').mp hdvd
    obtain ⟨a, hak, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hediv
    -- `d = p * 2^a`; show it is deficient.
    rw [mul_comm p (2 ^ a)]
    have h2a : 2 ^ a < 2 ^ k := by
      have hmul : p * 2 ^ a < p * 2 ^ k := by
        rw [mul_comm (2 ^ k) p] at hdlt; exact hdlt
      exact lt_of_mul_lt_mul_left hmul (Nat.zero_le p)
    have hak2 : a < k := by
      by_contra h
      push_neg at h
      have : 2 ^ k ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h
      omega
    have hbound : 2 ^ (a + 1) - 1 < p := by
      have hle : 2 ^ (a + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact deficient_two_pow_mul_prime hp hp2 hbound
  · -- `p ∤ d`: then `d ∣ 2^k`, a power of two, hence deficient.
    have hcop : Nat.Coprime p d := (hp.coprime_iff_not_dvd).mpr hpd
    have hd2k : d ∣ 2 ^ k := hcop.symm.dvd_of_dvd_mul_right hdvd
    obtain ⟨a, hak, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2k
    exact Nat.prime_two.deficient_pow

/-- Consistency check against the sibling entry: the least primitive abundant
number `20 = 2^2 · 5` arises from the construction with `k = 2`, `p = 5`. -/
example : IsPrimitiveAbundant 20 := by
  have h : IsPrimitiveAbundant (2 ^ 2 * 5) :=
    isPrimitiveAbundant_two_pow_mul_prime (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  norm_num at h; exact h

/-! ### Infinitude -/

/-- **There are infinitely many primitive abundant numbers.**

Given any bound `a`, take `k = a + 2` and apply Bertrand's postulate to
`2^k - 1` to obtain a prime `p` with `2^k - 1 < p ≤ 2^(k+1) - 2`. Then
`2^k · p` is primitive abundant (core theorem) and exceeds `a`. -/
theorem infinite_primitiveAbundant : {n : ℕ | IsPrimitiveAbundant n}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  set k := a + 2 with hk
  have hk2 : 2 ≤ k := by omega
  have hm : 2 ^ k - 1 ≠ 0 := by
    have h4 : (4 : ℕ) ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  obtain ⟨p, hp, hlo, hhi'⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ k - 1) hm
  -- Translate the Bertrand upper bound into the required strict window.
  have hhi : p < 2 ^ (k + 1) - 1 := by
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  refine ⟨2 ^ k * p, isPrimitiveAbundant_two_pow_mul_prime hk2 hp hlo hhi, ?_⟩
  -- `2^k · p > a`.
  have hk_lt : k < 2 ^ k := k.lt_two_pow_self
  have hbig : 2 ^ k ≤ 2 ^ k * p := le_mul_of_one_le_right (Nat.zero_le _) hp.one_lt.le
  omega

end AbundantPrimitiveInfiniteOQ0104
