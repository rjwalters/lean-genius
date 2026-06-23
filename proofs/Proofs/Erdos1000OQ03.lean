import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Jordan's totient `J_k`: an elementary, axiom-free generalization of Euler's `φ`

**Open question (`erdos-1000-oq-03`)**: *does the divisor-sum / multiplicativity
theory of Euler's totient extend to other generalized totients?*

The canonical generalization is **Jordan's totient** `J_k(n) = n^k ∏_{p∣n}(1 - p^{-k})`,
introduced by Camille Jordan (1870), which counts the `k`-tuples in `(ℤ/n)^k` whose
coordinates together with `n` are setwise coprime.  It satisfies `J_1 = φ` and the
fundamental divisor-sum identity

$$\sum_{d \mid n} J_k(d) = n^k,$$

the exact generalization of Gauss's `∑_{d∣n} φ(d) = n` (`Nat.sum_totient`).

## What this file proves (0 axioms, 0 sorries)

Rather than the combinatorial counting definition, we take the **Dirichlet
convolution** definition `J_k = μ * pow k` (Möbius times the `k`-th power
function) inside Mathlib's `ArithmeticFunction ℤ` ring.  This makes the deep
identities fall out of the ring structure (`μ * ζ = 1`):

* `jordan_mul_zeta`   : `J_k * ζ = pow k`  (the defining Dirichlet relation)
* `jordan_divisor_sum`: `∑_{d∣n} J_k(d) = n^k`  — **headline**, generalizes `Nat.sum_totient`
* `jordan_one`        : `J_k(1) = 1`
* `jordan_isMultiplicative` : `J_k` is multiplicative
* `jordan_prime_pow`  : `J_k(p^a) = p^{ka} - p^{k(a-1)}`  (prime powers; telescoping)
* `jordan_eq_prod`    : `J_k(n) = ∏_{p^a ∥ n} (p^{ka} - p^{k(a-1)})`  (the integer product formula)
* `jordan_one_eq_totient` : `J_1(n) = φ(n)`  (recovers Euler's totient)
* `jordan_nonneg`, `jordan_le_pow` : `0 ≤ J_k(n) ≤ n^k`

## Significance relative to the gallery

The gallery entry `erdos-1001-oq-03` (a deep analytic density problem) **axiomatizes**
Jordan's totient via `axiom jordan_one : jordanTotient 1 q = φ q` and
`axiom jordan_le_pow : jordanTotient d q ≤ q^d`.  Both are *proved* here from an
honest definition, so the elementary core of that entry is no longer axiomatic.
The entry `euler-totient-oq-02-oq-01` explicitly poses, as an open question, whether
the product formula for `φ` generalizes to `J_k`; `jordan_eq_prod` answers it in the
integer-product form.
-/

namespace Erdos1000OQ03

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- **Jordan's totient** of order `k`, defined as the Dirichlet convolution
`μ * pow k` inside the ring of integer arithmetic functions.  For `k = 1` this is
Euler's `φ` (see `jordan_one_eq_totient`); the value at `n` is
`∑_{d∣n} μ(d)·(n/d)^k = n^k ∏_{p∣n}(1 - p^{-k})`. -/
noncomputable def jordanTotient (k : ℕ) : ArithmeticFunction ℤ :=
  ArithmeticFunction.moebius * (↑(ArithmeticFunction.pow k) : ArithmeticFunction ℤ)

/-- The defining Dirichlet relation: `J_k * ζ = pow k`.  This is the arithmetic-function
form of the divisor-sum identity, obtained from `μ * ζ = 1`. -/
theorem jordan_mul_zeta (k : ℕ) :
    jordanTotient k * ζ = (↑(ArithmeticFunction.pow k) : ArithmeticFunction ℤ) := by
  have h : jordanTotient k * ζ
      = (↑(ArithmeticFunction.pow k) : ArithmeticFunction ℤ) * (μ * ζ) := by
    rw [jordanTotient]; ring
  rw [h, moebius_mul_coe_zeta, mul_one]

/-- **Headline.** The Jordan totients of the divisors of `n` sum to `n^k`:
`∑_{d∣n} J_k(d) = n^k`.  For `k = 1` this is Gauss's `∑_{d∣n} φ(d) = n`. -/
theorem jordan_divisor_sum (k : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, jordanTotient k d = (n : ℤ) ^ k := by
  have h := coe_mul_zeta_apply (f := jordanTotient k) (x := n)
  rw [jordan_mul_zeta] at h
  rw [natCoe_apply, pow_apply, if_neg (by rintro ⟨-, h0⟩; omega)] at h
  rw [← h]
  push_cast
  ring

/-- `J_k(1) = 1`. -/
theorem jordan_one (k : ℕ) : jordanTotient k 1 = 1 := by
  have h := jordan_divisor_sum k (n := 1) one_pos
  simpa using h

/-- `J_k` is multiplicative (a Dirichlet convolution of multiplicative functions). -/
theorem jordan_isMultiplicative (k : ℕ) : (jordanTotient k).IsMultiplicative := by
  rw [jordanTotient]
  exact isMultiplicative_moebius.mul isMultiplicative_pow.natCast

/-- **Prime-power values.** For a prime `p` and `a ≥ 1`,
`J_k(p^a) = p^{ka} - p^{k(a-1)}`.  Proved by telescoping the divisor-sum identity
across `p^a` and `p^{a-1}`. -/
theorem jordan_prime_pow (k : ℕ) {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) :
    jordanTotient k (p ^ a) = (p : ℤ) ^ (k * a) - (p : ℤ) ^ (k * (a - 1)) := by
  have hsum : ∀ m : ℕ,
      ∑ i ∈ range (m + 1), jordanTotient k (p ^ i) = (p : ℤ) ^ (k * m) := by
    intro m
    have hpm : 0 < p ^ m := pow_pos hp.pos m
    have hd := jordan_divisor_sum k (n := p ^ m) hpm
    rw [Nat.sum_divisors_prime_pow hp] at hd
    rw [hd]
    push_cast
    rw [← pow_mul, mul_comm m k]
  have h1 := hsum a
  have h2 := hsum (a - 1)
  rw [sum_range_succ] at h1
  rw [Nat.sub_add_cancel ha] at h2
  rw [h2] at h1
  linarith

/-- **Integer product formula** (answers `euler-totient-oq-02-oq-01`):
`J_k(n) = ∏_{p^a ∥ n} (p^{ka} - p^{k(a-1)})`, the generalization of Euler's product. -/
theorem jordan_eq_prod (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    jordanTotient k n
      = n.factorization.prod fun p a => (p : ℤ) ^ (k * a) - (p : ℤ) ^ (k * (a - 1)) := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization
        (jordanTotient k) (jordan_isMultiplicative k) hn]
  apply Finsupp.prod_congr
  intro p hp
  have ha : 1 ≤ n.factorization p :=
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  rw [Nat.support_factorization] at hp
  exact jordan_prime_pow k (Nat.prime_of_mem_primeFactors hp) ha

/-- `J_1 = φ`: Jordan's totient of order one is Euler's totient.  This de-axiomatizes
`axiom jordan_one` in the gallery entry `erdos-1001-oq-03`. -/
theorem jordan_one_eq_totient {n : ℕ} (hn : 0 < n) :
    jordanTotient 1 n = (Nat.totient n : ℤ) := by
  have h : ∀ m : ℕ, 0 < m → ∑ i ∈ m.divisors, (Nat.totient i : ℤ) = (m : ℤ) := by
    intro m _
    rw [← Nat.cast_sum]
    exact_mod_cast Nat.sum_totient m
  have key := (sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := fun i => (Nat.totient i : ℤ)) (g := fun m => (m : ℤ))).mp h n hn
  rw [jordanTotient, mul_apply, ← key]
  apply Finset.sum_congr rfl
  intro x hx
  have hsnd : (↑(ArithmeticFunction.pow 1) : ArithmeticFunction ℤ) x.snd = (x.snd : ℤ) := by
    rw [natCoe_apply, pow_apply, if_neg (by rintro ⟨h1, -⟩; exact one_ne_zero h1), pow_one]
  rw [hsnd]
  push_cast
  ring

/-- `0 ≤ J_k(n)`. -/
theorem jordan_nonneg (k n : ℕ) : 0 ≤ jordanTotient k n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [jordanTotient]
  · rw [jordan_eq_prod k hn, Finsupp.prod]
    apply Finset.prod_nonneg
    intro p hp
    have ha : 1 ≤ n.factorization p :=
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hpp.one_lt.le
    have hexp : k * (n.factorization p - 1) ≤ k * n.factorization p :=
      Nat.mul_le_mul_left k (by omega)
    have := pow_le_pow_right₀ h1 hexp
    linarith

/-- `J_k(n) ≤ n^k`: the divisor-sum identity bounds `J_k` by the top term.  This
de-axiomatizes `axiom jordan_le_pow` in the gallery entry `erdos-1001-oq-03`. -/
theorem jordan_le_pow (k : ℕ) {n : ℕ} (hn : 0 < n) :
    jordanTotient k n ≤ (n : ℤ) ^ k := by
  rw [← jordan_divisor_sum k hn]
  exact Finset.single_le_sum (fun d _ => jordan_nonneg k d)
    (Nat.mem_divisors_self n hn.ne')

end Erdos1000OQ03
