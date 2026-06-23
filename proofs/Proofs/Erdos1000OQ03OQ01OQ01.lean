import Mathlib

/-!
# Multiplicativity and the Euler product of Jordan's totient `J_k`

**Follow-up open question (`erdos-1000-oq-03-oq-01-oq-01`).**  The gallery entry
`erdos-1000-oq-03-oq-01` proved that the **count**
`C_k(n) = #{ (a₀,…,a_{k-1}) ∈ (ℤ/n)^k : gcd(a₀,…,a_{k-1},n) = 1 }`
equals the Dirichlet-convolution closed form `∑_{d ∣ n} μ(d)·(n/d)^k`, i.e. that the
combinatorial count is Jordan's totient `J_k`.  That established *what* `J_k` is; this
file establishes its **multiplicative structure**, the heart of the classical theory:

* `J_k = μ ∗ pow k` is a **multiplicative** arithmetic function (convolution of two
  multiplicative functions), so `J_k(mn) = J_k(m)·J_k(n)` for coprime `m, n`.
* its value on **prime powers** is `J_k(p^i) = p^{ki} − p^{k(i−1)}`, and
* hence the **Euler product** `J_k(n) = ∏_{p ∣ n} (p^{k·v_p} − p^{k·(v_p−1)})`,
  which over `ℝ` is the familiar `J_k(n) = n^k · ∏_{p ∣ n}(1 − p^{−k})`.

## What this file proves (0 axioms, 0 sorries)

* `jordan` — `J_k := μ ∗ pow k`, valued in `ℤ`.
* `jordan_apply` — `J_k(n) = ∑_{d ∣ n} μ(d)·(n/d)^k` (the closed form of the parent).
* `isMultiplicative_jordan` — `J_k` is multiplicative.
* `jordan_prime_pow` — `J_k(p^i) = p^{ki} − p^{k(i−1)}` for prime `p`, `i ≥ 1`.
* `jordan_eq_prod_primeFactors` — the integer **Euler product** over `n.primeFactors`.
* `jordan_pos` — `J_k(n) > 0` for `k ≥ 1`, `n ≥ 1` (`J_k` is a genuine totient).
* `jordan_one_apply` — `J_1 = φ`, recovering Euler's totient (`k = 1`).
* `jordan_eq_mul_prod_primeFactors` — the real **Euler product**
  `J_k(n) = n^k · ∏_{p ∣ n}(1 − (p^k)⁻¹)`.

Everything rests on Mathlib's arithmetic-function multiplicativity infrastructure
(`IsMultiplicative.mul`, `multiplicative_factorization`); no analysis beyond the final
cast to `ℝ`.
-/

open Finset ArithmeticFunction

namespace Erdos1000OQ03OQ01OQ01

/-- **Jordan's totient** `J_k`, defined as the Dirichlet convolution `μ ∗ pow k`,
valued in `ℤ`.  By `erdos-1000-oq-03-oq-01` this convolution counts the jointly
coprime `k`-tuples mod `n`. -/
def jordan (k : ℕ) : ArithmeticFunction ℤ := moebius * (pow k : ArithmeticFunction ℤ)

/-- **Closed form.**  `J_k(n) = ∑_{d ∣ n} μ(d)·(n/d)^k` — the Dirichlet-convolution
formula proved combinatorially in `erdos-1000-oq-03-oq-01`. -/
theorem jordan_apply {k n : ℕ} (hn : n ≠ 0) :
    jordan k n = ∑ d ∈ n.divisors, (moebius d) * ((n / d : ℕ) : ℤ) ^ k := by
  rw [jordan, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => (moebius x) * ((pow k : ArithmeticFunction ℤ) y))]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
  have hpos : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_mem_divisors hd)
  rw [natCoe_apply, pow_apply, if_neg (by simp [hpos.ne']), Nat.cast_pow]

/-- **`J_k` is multiplicative**: it is the Dirichlet convolution of the two
multiplicative functions `μ` and `pow k`, so `J_k(mn) = J_k(m)·J_k(n)` for coprime
`m, n`. -/
theorem isMultiplicative_jordan {k : ℕ} : IsMultiplicative (jordan k) :=
  isMultiplicative_moebius.mul isMultiplicative_pow.natCast

/-- **Value on prime powers.**  `J_k(p^i) = p^{ki} − p^{k(i−1)}` for a prime `p` and
`i ≥ 1`; only the squarefree divisors `1` and `p` survive the Möbius weights. -/
theorem jordan_prime_pow {k p i : ℕ} (hp : p.Prime) (hi : 0 < i) :
    jordan k (p ^ i) = (p : ℤ) ^ (k * i) - (p : ℤ) ^ (k * (i - 1)) := by
  have hppos : 0 < p := hp.pos
  rw [jordan_apply (pow_ne_zero i hp.pos.ne'), Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  -- the summand at `j` is `μ(p^j) · (p^(i-j))^k`
  have hquot : ∀ j ∈ Finset.range (i + 1),
      (moebius (p ^ j)) * (((p ^ i / p ^ j : ℕ)) : ℤ) ^ k
        = (moebius (p ^ j)) * ((p : ℤ) ^ ((i - j) * k)) := by
    intro j hj
    have hji : j ≤ i := by simpa [Nat.lt_succ_iff] using hj
    rw [Nat.pow_div hji hppos, Nat.cast_pow, pow_mul]
  rw [Finset.sum_congr rfl hquot]
  -- peel the `j = 0` and `j = 1` terms; the rest vanish (`μ(p^{j+2}) = 0`)
  rw [show i + 1 = (i - 1) + 1 + 1 from by omega, Finset.sum_range_succ', Finset.sum_range_succ']
  have htail : ∑ x ∈ Finset.range (i - 1),
      (moebius (p ^ (x + 1 + 1))) * ((p : ℤ) ^ ((i - (x + 1 + 1)) * k)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega), zero_mul]
  rw [htail, zero_add]
  -- evaluate the two surviving terms `j = 1` and `j = 0`
  simp only [zero_add, Nat.sub_zero, pow_zero, moebius_apply_one]
  rw [moebius_apply_prime_pow hp one_ne_zero, if_pos rfl, mul_comm i k, mul_comm (i - 1) k]
  ring

/-- **Integer Euler product.**  `J_k(n) = ∏_{p ∣ n} (p^{k·v_p(n)} − p^{k·(v_p(n)−1)})`,
the product running over the prime factors of `n`. -/
theorem jordan_eq_prod_primeFactors {k n : ℕ} (hn : n ≠ 0) :
    jordan k n =
      ∏ p ∈ n.primeFactors,
        ((p : ℤ) ^ (k * n.factorization p) - (p : ℤ) ^ (k * (n.factorization p - 1))) := by
  rw [isMultiplicative_jordan.multiplicative_factorization _ hn]
  refine (Finset.prod_congr n.support_factorization fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hipos : 0 < n.factorization p := by
    rwa [← Nat.support_factorization, Finsupp.mem_support_iff, ← pos_iff_ne_zero] at hp
  exact jordan_prime_pow hpp hipos

/-- **Positivity.**  For `k ≥ 1` and `n ≥ 1`, Jordan's totient is a positive integer —
it genuinely counts the jointly coprime `k`-tuples mod `n`. -/
theorem jordan_pos {k n : ℕ} (hk : 0 < k) (hn : 0 < n) : 0 < jordan k n := by
  rw [jordan_eq_prod_primeFactors hn.ne']
  apply Finset.prod_pos
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hipos : 0 < n.factorization p := by
    rwa [← Nat.support_factorization, Finsupp.mem_support_iff, ← pos_iff_ne_zero] at hp
  have h2 : (p : ℤ) ≥ 2 := by exact_mod_cast hpp.two_le
  have hlt : k * (n.factorization p - 1) < k * n.factorization p :=
    Nat.mul_lt_mul_of_pos_left (by omega) hk
  have : (p : ℤ) ^ (k * (n.factorization p - 1)) < (p : ℤ) ^ (k * n.factorization p) :=
    pow_lt_pow_right₀ (by linarith) hlt
  linarith

/-- **Euler totient recovery (`k = 1`).**  `J_1 = φ`: the Jordan totient specialises to
Euler's totient, since `μ ∗ id = φ` is the Möbius inversion of `∑_{d ∣ n} φ(d) = n`. -/
theorem jordan_one_apply (n : ℕ) : jordan 1 n = (Nat.totient n : ℤ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [jordan]
  rw [jordan_apply hn]
  -- Möbius inversion of Gauss's `∑_{d ∣ m} φ(d) = m`
  have H : ∀ m, 0 < m → ∑ i ∈ m.divisors, (Nat.totient i : ℤ) = ((m : ℕ) : ℤ) := by
    intro m _
    rw [← Nat.cast_sum, Nat.sum_totient]
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (f := fun i => (Nat.totient i : ℤ)) (g := fun m => ((m : ℕ) : ℤ))).mp H n
      (Nat.pos_of_ne_zero hn)
  rw [← hinv, Nat.sum_divisorsAntidiagonal (fun p q => (moebius p) • ((q : ℕ) : ℤ))]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [pow_one]

/-- **Real Euler product.**  `J_k(n) = n^k · ∏_{p ∣ n}(1 − (p^k)⁻¹)`, the classical
closed form of Jordan's totient over `ℝ` (`k ≥ 1`, `n ≥ 1`). -/
theorem jordan_eq_mul_prod_primeFactors {k n : ℕ} (hn : n ≠ 0) :
    (jordan k n : ℝ)
      = (n : ℝ) ^ k * ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ k)⁻¹) := by
  rw [jordan_eq_prod_primeFactors hn]
  push_cast
  -- reassemble `n^k = ∏_{p ∣ n} p^{k·v_p}`
  have hnat : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
  have hnk : (n : ℝ) ^ k = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (k * n.factorization p) := by
    conv_lhs => rw [hnat]
    push_cast; rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun p _ => by rw [← pow_mul, Nat.mul_comm]
  rw [hnk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hipos : 0 < n.factorization p := by
    rwa [← Nat.support_factorization, Finsupp.mem_support_iff, ← pos_iff_ne_zero] at hp
  -- termwise: `p^{k·v_p} − p^{k·(v_p−1)} = p^{k·v_p}·(1 − (p^k)⁻¹)`
  have hexp : k * (n.factorization p - 1) + k = k * n.factorization p := by
    have h1 : n.factorization p - 1 + 1 = n.factorization p := Nat.succ_pred_eq_of_pos hipos
    calc k * (n.factorization p - 1) + k
        = k * (n.factorization p - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = k * n.factorization p := by rw [h1]
  have key : (p : ℝ) ^ (k * n.factorization p) * ((p : ℝ) ^ k)⁻¹
      = (p : ℝ) ^ (k * (n.factorization p - 1)) := by
    rw [← hexp, pow_add, mul_inv_cancel_right₀ (pow_ne_zero k hppos.ne')]
  rw [mul_sub, mul_one, key]

end Erdos1000OQ03OQ01OQ01
