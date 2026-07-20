/-
  Roth Theorem OQ-04 (structural companion): the first-moment divisor sum
  `S(N) = ∑_{d∣N} φ(N/d)·√d` is a MULTIPLICATIVE arithmetic function.

  `RothTheoremOQ04FirstMoment` evaluates the exact `L¹` first moment of the
  quadratic Gauss sum at odd `N`:

      `∑_{r} ‖G(r)‖ = √N · ∑_{d∣N} φ(N/d)·√d`   (`sum_norm_sqGaussSum_eq_of_odd`).

  The arithmetic core of that ceiling is the divisor sum
  `S(N) := ∑_{d∣N} φ(N/d)·√d`.  This file identifies `S` as the **Dirichlet
  convolution** `φ ⋆ (√·)` of the (multiplicative) Euler totient and the
  (completely multiplicative) real square root.  Mathlib's
  `ArithmeticFunction.IsMultiplicative.mul` then gives, for free, that `S` is
  multiplicative:

      `gcd(m, n) = 1  ⟹  S(m · n) = S(m) · S(n)`   (`isMultiplicative_firstMomentAF`).

  Multiplicativity reduces the first moment at *every* odd `N` to its prime-power
  values, given in closed form by

  * `firstMomentDivisorSum_prime_pow` — `S(p^k) = ∑_{j≤k} φ(p^{k-j})·p^{j/2}`, and
  * `firstMomentDivisorSum_prime` — `S(p) = (p-1) + √p`; multiplying by `√p`
    recovers the prime first moment `p + (p-1)·√p` of
    `sum_norm_sqGaussSum_eq_of_prime`.

  Because `firstMomentAF N` is, by `firstMomentAF_apply`, *definitionally* the
  same divisor sum that appears (times `√N`) in `sum_norm_sqGaussSum_eq_of_odd`,
  this file makes the first moment of the quadratic Gauss sum a `√N`-multiple of
  a multiplicative arithmetic function whose prime-power values are explicit —
  a structural characterisation that the earlier ad-hoc evaluations (`N = 9`,
  the prime case) are now special cases of.

  All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`,
  Mathlib only (no dependency on the heavy `RothTheorem` file).
-/
import Mathlib

open Finset ArithmeticFunction

namespace Szemeredi.Roth

/-- The real square root as an arithmetic function `ℕ → ℝ` (with `√0 = 0`). -/
noncomputable def sqrtAF : ArithmeticFunction ℝ := ⟨fun n => Real.sqrt n, by simp⟩

/-- The Euler totient as a real-valued arithmetic function (`φ 0 = 0`). -/
noncomputable def totientAF : ArithmeticFunction ℝ := ⟨fun n => (n.totient : ℝ), by simp⟩

/-- The **first-moment divisor sum** `S(N) = ∑_{d∣N} φ(N/d)·√d`, packaged as the
    Dirichlet convolution `φ ⋆ (√·)`. -/
noncomputable def firstMomentAF : ArithmeticFunction ℝ := totientAF * sqrtAF

@[simp] theorem sqrtAF_apply (n : ℕ) : sqrtAF n = Real.sqrt n := rfl

@[simp] theorem totientAF_apply (n : ℕ) : totientAF n = (n.totient : ℝ) := rfl

/-- `√·` is multiplicative: `√1 = 1` and `√(m·n) = √m·√n` (in fact completely so). -/
theorem isMultiplicative_sqrtAF : sqrtAF.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n _
  simp only [sqrtAF_apply, Nat.cast_mul]
  exact Real.sqrt_mul (by positivity) _

/-- The real totient is multiplicative (cast of `Nat.totient_mul`). -/
theorem isMultiplicative_totientAF : totientAF.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n hmn
  simp only [totientAF_apply]
  rw [Nat.totient_mul hmn, Nat.cast_mul]

/-- **The first-moment divisor sum is multiplicative.**  A Dirichlet convolution
    of two multiplicative arithmetic functions is multiplicative
    (`ArithmeticFunction.IsMultiplicative.mul`), so `gcd(m,n)=1 ⟹ S(mn)=S(m)S(n)`. -/
theorem isMultiplicative_firstMomentAF : firstMomentAF.IsMultiplicative :=
  isMultiplicative_totientAF.mul isMultiplicative_sqrtAF

/-- **`S(N)` is the first-moment divisor sum.**  Unfolding the Dirichlet
    convolution and reindexing the antidiagonal by `d ↦ (N/d, d)` gives exactly
    the sum `∑_{d∣N} φ(N/d)·√d` that appears (times `√N`) in
    `RothTheoremOQ04FirstMoment.sum_norm_sqGaussSum_eq_of_odd`. -/
theorem firstMomentAF_apply (N : ℕ) :
    firstMomentAF N = ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d := by
  rw [firstMomentAF, mul_apply, Nat.sum_divisorsAntidiagonal' (f := fun a b => totientAF a * sqrtAF b)]
  simp only [totientAF_apply, sqrtAF_apply]

/-- Multiplicative shorthand `S(m·n) = S(m)·S(n)` at coprime arguments. -/
theorem firstMomentAF_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    firstMomentAF (m * n) = firstMomentAF m * firstMomentAF n :=
  isMultiplicative_firstMomentAF.map_mul_of_coprime h

/-- **Closed form of `S` at prime powers.**  `S(p^k) = ∑_{j=0}^{k} φ(p^{k-j})·p^{j/2}`.
    Every divisor of `p^k` is `p^j` with `0 ≤ j ≤ k`, and `p^k / p^j = p^{k-j}`. -/
theorem firstMomentDivisorSum_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    firstMomentAF (p ^ k)
      = ∑ j ∈ range (k + 1), ((p ^ (k - j)).totient : ℝ) * Real.sqrt ((p : ℝ) ^ j) := by
  rw [firstMomentAF_apply, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hdiv : p ^ k / p ^ j = p ^ (k - j) := Nat.pow_div hjk hp.pos
  rw [hdiv, Nat.cast_pow]

/-- **Closed form of `S` at primes.**  `S(p) = (p-1) + √p`.  Multiplying by `√p`
    recovers the prime first moment `√p · S(p) = p + (p-1)·√p` of
    `RothTheoremOQ04FirstMoment.sum_norm_sqGaussSum_eq_of_prime`. -/
theorem firstMomentDivisorSum_prime {p : ℕ} (hp : p.Prime) :
    firstMomentAF p = ((p : ℝ) - 1) + Real.sqrt p := by
  have hk : firstMomentAF (p ^ 1) = _ := firstMomentDivisorSum_prime_pow hp 1
  rw [pow_one] at hk
  rw [hk]
  -- ∑_{j∈{0,1}} φ(p^{1-j})·p^{j/2} = φ(p)·1 + φ(1)·√p = (p-1) + √p
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, pow_one, Nat.sub_self, pow_zero, Nat.totient_one, Nat.cast_one,
    Real.sqrt_one, mul_one, Nat.totient_prime hp]
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  ring

end Szemeredi.Roth
