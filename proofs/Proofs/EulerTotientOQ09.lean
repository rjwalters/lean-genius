import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

/-!
# The totient under prime-saturated products and powers: `φ(nᵏ) = nᵏ⁻¹·φ(n)`

**Open Question (`euler-totient-oq-09`)**: how does Euler's totient behave under
the *power* `n ↦ nᵏ`?  Mathlib has the multiplicative law `Nat.totient_mul`
(valid only for **coprime** arguments) and the prime-power values
`Nat.totient_prime_pow`, but it has **no** lemma describing `φ(nᵏ)` for a general
base `n`.  Note `n` and `nᵏ` are very far from coprime, so `totient_mul` does not
apply.

The closed form is the classical
$$\varphi(n^k) = n^{k-1}\,\varphi(n) \qquad (k \ge 1),$$
which holds for *every* `n` (including `0`).  It is a consequence of the product
formula `φ(n)/n = ∏_{p∣n}(1 - 1/p)`: since `n` and `nᵏ` have exactly the same set
of prime factors, the products agree and only the leading `n` versus `nᵏ` differs.

## The engine

Rather than prove the power law in isolation, we isolate the underlying mechanism
as a reusable lemma that Mathlib does not state:

  `totient_mul_of_primeFactors_subset` :
      `m.primeFactors ⊆ n.primeFactors → φ(m * n) = m * φ(n)`.

In words: **multiplying by a factor whose primes already divide `n` scales the
totient by exactly that factor.**  This generalises `Nat.totient_mul_of_prime_of_dvd`
(`φ(p·n) = p·φ(n)` for a prime `p ∣ n`) from a single prime to an arbitrary
"prime-saturated" multiplier.  Everything else in the file is a corollary.

## Contents

* `totient_mul_of_primeFactors_subset` — the engine: `φ(m·n) = m·φ(n)` when
  `m.primeFactors ⊆ n.primeFactors`.
* `totient_pow`           — the headline closed form `φ(nᵏ) = nᵏ⁻¹·φ(n)` for `k ≥ 1`.
* `totient_pow_succ`      — the recurrence `φ(nᵏ⁺¹) = n·φ(nᵏ)` for `k ≥ 1`.
* `totient_sq`            — the quadratic case `φ(n²) = n·φ(n)`.
* `pow_pred_dvd_totient_pow`, `totient_dvd_totient_pow` — divisibility consequences.
* `totient_two_mul_of_even`, `totient_two_mul_of_odd` — the `n ↦ 2n` dichotomy.

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace EulerTotientOQ09

open Nat

/-- **The engine.**  If every prime factor of `m` already divides `n`, then
multiplying by `m` scales the totient by exactly `m`:  `φ(m·n) = m·φ(n)`.

This is a clean generalisation of `Nat.totient_mul_of_prime_of_dvd` (the single
prime case `φ(p·n) = p·φ(n)`).  The proof goes through Euler's product formula
`(φ n : ℚ) = n · ∏_{p ∣ n}(1 - 1/p)`: the hypothesis forces
`(m·n).primeFactors = n.primeFactors`, so the two products coincide and only the
leading `m·n` versus `n` differ. -/
theorem totient_mul_of_primeFactors_subset {m n : ℕ}
    (h : m.primeFactors ⊆ n.primeFactors) : φ (m * n) = m * φ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  -- The prime factors of `m * n` collapse onto those of `n`.
  have hpf : (m * n).primeFactors = n.primeFactors := by
    rw [Nat.primeFactors_mul hm hn, Finset.union_eq_right.mpr h]
  -- Compare the two totients through the rational product formula.
  have key : (φ (m * n) : ℚ) = (m : ℚ) * (φ n : ℚ) := by
    rw [totient_eq_mul_prod_factors (m * n), hpf, totient_eq_mul_prod_factors n]
    push_cast
    ring
  exact_mod_cast key

/-- **Headline closed form.**  For every base `n` and exponent `k ≥ 1`,
`φ(nᵏ) = nᵏ⁻¹ · φ(n)`.  Mathlib has no such lemma for a general base.

The proof writes `nᵏ = nᵏ⁻¹ · n` and applies the engine: `nᵏ⁻¹` has the same prime
factors as `n` (or none at all, when `k = 1`), so the totient scales by `nᵏ⁻¹`. -/
theorem totient_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    φ (n ^ k) = n ^ (k - 1) * φ n := by
  have hk1 : (k - 1) + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
  conv_lhs => rw [← hk1, pow_succ]
  apply totient_mul_of_primeFactors_subset
  rcases eq_or_ne (k - 1) 0 with h0 | h0
  · rw [h0, pow_zero, Nat.primeFactors_one]
    exact Finset.empty_subset _
  · exact le_of_eq (Nat.primeFactors_pow n h0)

/-- **Recurrence form.**  For `k ≥ 1`, increasing the exponent by one multiplies the
totient by the base: `φ(nᵏ⁺¹) = n · φ(nᵏ)`.  Equivalently `φ(nᵏ⁺¹)/φ(nᵏ) = n`. -/
theorem totient_pow_succ (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    φ (n ^ (k + 1)) = n * φ (n ^ k) := by
  rw [pow_succ']
  exact totient_mul_of_primeFactors_subset (ge_of_eq (Nat.primeFactors_pow n hk))

/-- The quadratic special case `φ(n²) = n · φ(n)`. -/
theorem totient_sq (n : ℕ) : φ (n ^ 2) = n * φ n := by
  have h := totient_pow n (k := 2) (by norm_num)
  simpa using h

/-- `nᵏ⁻¹` divides `φ(nᵏ)` — the leading power factor survives the totient. -/
theorem pow_pred_dvd_totient_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    n ^ (k - 1) ∣ φ (n ^ k) := by
  rw [totient_pow n hk]; exact dvd_mul_right _ _

/-- `φ(n)` divides `φ(nᵏ)` for every `k ≥ 1`. -/
theorem totient_dvd_totient_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    φ n ∣ φ (n ^ k) := by
  rw [totient_pow n hk]; exact dvd_mul_left _ _

/-- The `n ↦ 2n` dichotomy, even half: if `n` is even then `φ(2n) = 2·φ(n)`.
This is the prime case `p = 2` of `Nat.totient_mul_of_prime_of_dvd`. -/
theorem totient_two_mul_of_even {n : ℕ} (h : 2 ∣ n) : φ (2 * n) = 2 * φ n :=
  Nat.totient_mul_of_prime_of_dvd Nat.prime_two h

/-- The `n ↦ 2n` dichotomy, odd half: if `n` is odd then `φ(2n) = φ(n)`. -/
theorem totient_two_mul_of_odd {n : ℕ} (h : ¬ 2 ∣ n) : φ (2 * n) = φ n := by
  rw [Nat.totient_mul_of_prime_of_not_dvd Nat.prime_two h]; norm_num

end EulerTotientOQ09
