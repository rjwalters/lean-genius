import Mathlib

/-
# Erdős #1000 OQ-03 → OQ-03: The Gauss divisor-sum identity for Jordan's totient, via the Dirichlet ring

## Open question

`erdos-1000-oq-03-oq-03`: *the Gauss divisor-sum identity for the Jordan totient*
`∑_{d ∣ n} J_k(d) = n^k`.

## Where this sits in the gallery

The sibling entries develop Jordan's totient `J_k` from two independent angles:

* `erdos-1000-oq-03-oq-01` / `-oq-02` prove the **geometric** divisor-sum identity
  `∑_{d ∣ n} C_k(d) = n^k` for the *combinatorial count* `C_k(n) = #{ a ∈ (ℤ/n)^k :
  gcd(a, n) = 1 }`, by an explicit fibrewise bijection on `k`-tuples, and Möbius-invert
  it to obtain `C_k = μ ∗ pow k`.
* `erdos-1000-oq-03-oq-01-oq-01` studies the **arithmetic function** `J_k := μ ∗ pow k`
  (valued in `ℤ`): its multiplicativity, prime-power values, and the Euler product.

What neither entry states is the divisor-sum identity **at the level of the abstract
arithmetic function** `J_k = μ ∗ pow k`, i.e. the *reconstruction* dual of the gallery's
*Möbius-inversion* result. That is exactly this file: it works entirely inside Mathlib's
Dirichlet convolution ring `ArithmeticFunction ℤ`, where the identity becomes a one-line
ring computation, and it adds the **uniqueness characterisation** — that the Gauss
divisor-sum *determines* `J_k` — which is genuinely new to the gallery.

## What this file proves (0 axioms, 0 sorries)

* `jordan` — `J_k := μ ∗ pow k`, the arithmetic function of `-oq-01-oq-01`.
* `jordan_mul_zeta` — the **arithmetic-function identity** `J_k ∗ ζ = pow k`.  This is the
  reconstruction dual of the gallery's inversion `J_k = μ ∗ pow k`: convolving by `ζ`
  (summation over divisors) undoes the Möbius weighting, because `μ ∗ ζ = 1` in the
  Dirichlet ring.
* `jordan_divisor_sum` — the headline **Gauss identity** `∑_{d ∣ n} J_k(d) = n^k` (`n ≠ 0`),
  read off `jordan_mul_zeta` pointwise via `coe_mul_zeta_apply`.
* `jordan_unique` — **the divisor-sum characterises `J_k`.**  Any `f : ℕ → ℤ` satisfying
  `∑_{d ∣ n} f(d) = n^k` for all `n > 0` agrees with `J_k` on the positives.  This is the
  Möbius-inversion converse: the Gauss identity has a *unique* solution.
* `jordan_one_apply` — `J_1 = φ` (`k = 1`), Euler's totient.
* `sum_totient_eq_self` — Gauss's classical `∑_{d ∣ n} φ(d) = n` recovered as the `k = 1`
  specialisation of `jordan_divisor_sum`.

## Method

Everything is convolution algebra in the commutative ring `ArithmeticFunction ℤ`:
`coe_moebius_mul_coe_zeta` (`μ ∗ ζ = 1`), `coe_mul_zeta_apply` (`(f ∗ ζ) n = ∑_{d ∣ n} f d`),
and `sum_eq_iff_sum_smul_moebius_eq` (Möbius inversion) for uniqueness.  No combinatorics,
no analysis beyond none.

No axioms, no native_decide.

Tags: number-theory, totient-function, jordan-totient, gauss-identity, divisor-sums,
dirichlet-convolution, moebius-inversion, arithmetic-function, erdos-1000
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace Erdos1000OQ03OQ03

/-- **Jordan's totient** `J_k`, as the Dirichlet convolution `μ ∗ pow k` in the ring
`ArithmeticFunction ℤ` (the definition of `erdos-1000-oq-03-oq-01-oq-01`). -/
def jordan (k : ℕ) : ArithmeticFunction ℤ := moebius * (pow k : ArithmeticFunction ℤ)

/-- **Reconstruction identity** `J_k ∗ ζ = pow k`.

This is the Dirichlet-ring dual of the gallery's Möbius inversion `J_k = μ ∗ pow k`:
convolving with `ζ` (summing over divisors) cancels the Möbius factor, because
`μ ∗ ζ = 1` is the multiplicative identity of the convolution ring. -/
theorem jordan_mul_zeta (k : ℕ) :
    jordan k * (ζ : ArithmeticFunction ℤ) = (pow k : ArithmeticFunction ℤ) := by
  rw [jordan, mul_right_comm, moebius_mul_coe_zeta, one_mul]

/-- **Gauss's divisor-sum identity for Jordan's totient**: `∑_{d ∣ n} J_k(d) = n^k`.

The pointwise reading of `jordan_mul_zeta`, since `(f ∗ ζ) n = ∑_{d ∣ n} f d`. -/
theorem jordan_divisor_sum (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, jordan k d = (n : ℤ) ^ k := by
  have h : (jordan k * (ζ : ArithmeticFunction ℤ)) n = ∑ d ∈ n.divisors, jordan k d :=
    coe_mul_zeta_apply
  rw [jordan_mul_zeta] at h
  rw [← h, natCoe_apply, pow_apply, if_neg (by simp [hn]), Nat.cast_pow]

/-- **The Gauss identity characterises `J_k`.**

If `f : ℕ → ℤ` satisfies `∑_{d ∣ n} f(d) = n^k` for every `n > 0`, then `f` agrees with
Jordan's totient on the positive integers.  This is the Möbius-inversion converse of
`jordan_divisor_sum`: the divisor-sum equation has a unique solution. -/
theorem jordan_unique (k : ℕ) (f : ℕ → ℤ)
    (hf : ∀ (n : ℕ), 0 < n → ∑ d ∈ n.divisors, f d = (n : ℤ) ^ k) :
    ∀ (n : ℕ), 0 < n → f n = jordan k n := by
  intro n hn
  -- Möbius-invert the hypothesis: `f n = ∑_{x*y = n} μ(x)·y^k`.
  have hinv := (sum_eq_iff_sum_smul_moebius_eq (f := f) (g := fun m => (m : ℤ) ^ k)).mp
    (fun m hm => hf m hm) n hn
  rw [← hinv, jordan, mul_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hx2 : x.2 ≠ 0 := fun h => hn0 (by rw [← hprod, h, mul_zero])
  rw [natCoe_apply, pow_apply, if_neg (by simp [hx2]), Nat.cast_pow, smul_eq_mul]

/-- **Euler-totient recovery (`k = 1`).**  `J_1 = φ`, since `μ ∗ id = φ` is the Möbius
inversion of Gauss's `∑_{d ∣ n} φ(d) = n`. -/
theorem jordan_one_apply (n : ℕ) : jordan 1 n = (Nat.totient n : ℤ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [jordan]
  -- `jordan 1` and `↑φ` both have divisor-sum `n`, so equal by uniqueness.
  refine (jordan_unique 1 (fun m => (Nat.totient m : ℤ)) (fun m _ => ?_) n
    (Nat.pos_of_ne_zero hn)).symm
  rw [← Nat.cast_sum, Nat.sum_totient, pow_one]

/-- **Gauss's classical totient identity**, `∑_{d ∣ n} φ(d) = n`, as the `k = 1`
specialisation of `jordan_divisor_sum`. -/
theorem sum_totient_eq_self {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (Nat.totient d : ℤ) = (n : ℤ) := by
  have h := jordan_divisor_sum 1 hn
  rw [pow_one] at h
  rw [← h]
  exact Finset.sum_congr rfl fun d _ => (jordan_one_apply d).symm

end Erdos1000OQ03OQ03
