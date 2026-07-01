import Mathlib

/-!
# The Gauss divisor-sum identity for Jordan's totient `J_k`, via Dirichlet convolution

**Follow-up open question (`erdos-1000-oq-03-oq-03`).**  The Jordan-totient family in
this gallery defines `J_k` as the Dirichlet convolution `J_k = μ ∗ pow k`
(`erdos-1000-oq-03-oq-01-oq-01`) and establishes its multiplicativity, prime-power
values, Euler product, and positivity.  The *combinatorial* companion
(`erdos-1000-oq-03-oq-01`) proves the Gauss-type identity `∑_{d ∣ n} C_k(d) = n^k`
for the tuple count `C_k` by an explicit fiberwise bijection, and separately identifies
`C_k = J_k`.

This file closes the remaining gap by proving the Gauss identity **directly for the
convolution `J_k`**, through pure **Dirichlet-convolution algebra** rather than a
combinatorial bijection.  The key observation is that summing an arithmetic function
over the divisors of `n` is *convolution with `ζ`*, and that `ζ` is a unit in the
arithmetic-function ring with inverse `μ` (`ζ ∗ μ = 1`).  Hence

$$ \zeta * J_k \;=\; \zeta * (\mu * \mathrm{pow}\,k)
   \;=\; (\zeta * \mu) * \mathrm{pow}\,k \;=\; \mathrm{pow}\,k, $$

which read at `n` is exactly `∑_{d ∣ n} J_k(d) = n^k`.

## What this file proves (0 axioms, 0 sorries)

* `zeta_mul_jordan` — the **structural identity** `ζ ∗ J_k = pow k` at the level of
  arithmetic functions.  This is the true content: the numeric Gauss identity is its
  evaluation at a point.
* `jordan_divisor_sum` — `∑_{d ∣ n} J_k(d) = n^k`, the Gauss divisor-sum identity for
  Jordan's totient (generalizing `∑_{d ∣ n} φ(d) = n`).
* `jordan_unique` — **uniqueness / characterization**: `J_k` is the *only* arithmetic
  function whose divisor sums are `n ↦ n^k`.  Since `ζ` is a unit (inverse `μ`), the
  Gauss identity *characterizes* `J_k = μ ∗ pow k`.  Proved by Möbius inversion.
* `jordan_apply` — the closed form `J_k(n) = ∑_{d ∣ n} μ(d)·(n/d)^k`.
* `jordan_one_apply` — `J_1 = φ`, recovering Euler's totient (`k = 1`).
* `gauss_sum_totient` — the classical `∑_{d ∣ n} φ(d) = n` recovered as the `k = 1`
  specialization of `jordan_divisor_sum`.

The whole development rests on Mathlib's Dirichlet-convolution machinery
(`coe_zeta_mul_apply`, `coe_zeta_mul_moebius`, `sum_eq_iff_sum_smul_moebius_eq`); no
analysis, no `native_decide`.

Tags: number-theory, totient-function, jordan-totient, gauss-identity, divisor-sums,
Dirichlet-convolution, moebius-inversion
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace Erdos1000OQ03OQ03

/-- **Jordan's totient** `J_k := μ ∗ pow k`, the Dirichlet convolution defining the
generalized totient (the same definition used in `erdos-1000-oq-03-oq-01-oq-01`). -/
def jordan (k : ℕ) : ArithmeticFunction ℤ := moebius * (pow k : ArithmeticFunction ℤ)

/-- **Structural identity.**  `ζ ∗ J_k = pow k` as arithmetic functions.

Convolving Jordan's totient with `ζ` — i.e. forming the summatory (divisor-sum)
function — returns `pow k`.  This is the arithmetic-function form of the Gauss identity
and the reason `J_k` is the Möbius inverse of `n ↦ n^k`.  Read pointwise (via
`coe_zeta_mul_apply`), both sides are divisor sums and the identity collapses to one
line of convolution algebra: `ζ ∗ (μ ∗ pow k) = (ζ ∗ μ) ∗ pow k = 1 ∗ pow k = pow k`. -/
theorem zeta_mul_jordan (k : ℕ) :
    (ζ : ArithmeticFunction ℤ) * jordan k = (pow k : ArithmeticFunction ℤ) := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [coe_zeta_mul_apply, jordan, ← coe_zeta_mul_apply, ← mul_assoc,
      coe_zeta_mul_moebius, one_mul]

/-- **Gauss divisor-sum identity for Jordan's totient.**
`∑_{d ∣ n} J_k(d) = n^k` — the exact generalization of Gauss's `∑_{d ∣ n} φ(d) = n`
(the `k = 1` case).

Proof: rewrite the divisor sum as `(ζ ∗ J_k)(n)` via `coe_zeta_mul_apply`, collapse
`ζ ∗ μ = 1`, and evaluate `pow k` at `n`.  This is a genuinely different proof from the
combinatorial fiberwise bijection of `erdos-1000-oq-03-oq-01`. -/
theorem jordan_divisor_sum (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, jordan k d = (n : ℤ) ^ k := by
  rw [← coe_zeta_mul_apply, jordan, ← mul_assoc, coe_zeta_mul_moebius, one_mul,
      natCoe_apply, pow_apply, if_neg (fun hc => hn hc.2), Nat.cast_pow]

/-- **Closed form.**  `J_k(n) = ∑_{d ∣ n} μ(d)·(n/d)^k` — the Dirichlet-convolution
formula (as in `erdos-1000-oq-03-oq-01-oq-01`), recorded here so the uniqueness and
`k = 1` results below are self-contained. -/
theorem jordan_apply {k n : ℕ} (hn : n ≠ 0) :
    jordan k n = ∑ d ∈ n.divisors, (moebius d) * ((n / d : ℕ) : ℤ) ^ k := by
  rw [jordan, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => (moebius x) * ((pow k : ArithmeticFunction ℤ) y))]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
  have hpos : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_mem_divisors hd)
  rw [natCoe_apply, pow_apply, if_neg (by simp [hpos.ne']), Nat.cast_pow]

/-- **Uniqueness / characterization.**  `J_k` is the *unique* arithmetic function whose
divisor sums are `n ↦ n^k`: if `∑_{d ∣ m} f(d) = m^k` for every `m ≥ 1`, then `f = J_k`.

Because `ζ` is a unit in the Dirichlet-convolution ring with inverse `μ`, the
divisor-sum operator is invertible, so the Gauss identity *pins down* `J_k = μ ∗ pow k`.
Concretely this is Möbius inversion (`sum_eq_iff_sum_smul_moebius_eq`). -/
theorem jordan_unique (k : ℕ) (f : ArithmeticFunction ℤ)
    (hf : ∀ m : ℕ, 0 < m → ∑ d ∈ m.divisors, f d = (m : ℤ) ^ k) :
    f = jordan k := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [jordan]
  have H : ∀ m : ℕ, 0 < m → ∑ i ∈ m.divisors, f i = ((m : ℕ) : ℤ) ^ k := hf
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (f := fun i => f i) (g := fun m => ((m : ℕ) : ℤ) ^ k)).mp H n hn
  rw [← hinv, jordan_apply hn.ne',
      Nat.sum_divisorsAntidiagonal (fun p q => (moebius p) • ((q : ℕ) : ℤ) ^ k)]
  exact Finset.sum_congr rfl fun d _ => smul_eq_mul _ _

/-- **Euler-totient recovery (`k = 1`).**  `J_1 = φ`: Jordan's totient specialises to
Euler's totient, since `μ ∗ id = φ` is the Möbius inversion of `∑_{d ∣ n} φ(d) = n`. -/
theorem jordan_one_apply (n : ℕ) : jordan 1 n = (Nat.totient n : ℤ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [jordan]
  rw [jordan_apply hn]
  have H : ∀ m, 0 < m → ∑ i ∈ m.divisors, (Nat.totient i : ℤ) = ((m : ℕ) : ℤ) := by
    intro m _
    rw [← Nat.cast_sum, Nat.sum_totient]
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (f := fun i => (Nat.totient i : ℤ)) (g := fun m => ((m : ℕ) : ℤ))).mp H n
      (Nat.pos_of_ne_zero hn)
  rw [← hinv, Nat.sum_divisorsAntidiagonal (fun p q => (moebius p) • ((q : ℕ) : ℤ))]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [pow_one]

/-- **Classical Gauss identity recovered.**  `∑_{d ∣ n} φ(d) = n`, obtained as the
`k = 1` specialization of `jordan_divisor_sum` together with `J_1 = φ`. -/
theorem gauss_sum_totient {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (Nat.totient d : ℤ) = (n : ℤ) := by
  have h := jordan_divisor_sum 1 (n := n) hn
  rw [pow_one] at h
  rw [← h]
  exact Finset.sum_congr rfl fun d _ => (jordan_one_apply d).symm

end Erdos1000OQ03OQ03
