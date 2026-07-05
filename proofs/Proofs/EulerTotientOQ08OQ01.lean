/-
# Euler's totient periodicity beyond the coprime case (composite moduli)

Euler's theorem reduces the exponent of `aᵏ (mod n)` modulo `φ n` **only when
`gcd(a, n) = 1`**. `Mathlib/NumberTheory/PowModTotient.lean` records as an explicit
TODO the removal of that coprimality hypothesis, and the sibling file
`EulerTotientOQ08` carried this out for **prime-power moduli** `pᵉ`: for every base
`a` (invertible or not) and every `k ≥ e`,

  `a ^ (k + φ(pᵉ)) ≡ a ^ k [MOD pᵉ]`.

This file assembles those prime-power periodicities into the statement for an
**arbitrary composite modulus** `n` via the Chinese Remainder Theorem. Writing
`n = ∏ p pᵉ⁽ᵖ⁾` for its prime factorisation, once the exponent `k` exceeds every
`eₚ = vₚ(n)` (equivalently `k ≥ maxₚ vₚ(n)`) each prime-power factor is already in
its periodic régime, and since `φ` is multiplicative `φ(pᵉ⁽ᵖ⁾) ∣ φ(n)`, so the
`φ(n)`-shift is a whole number of periods for every factor. CRT glues the factorwise
congruences back together modulo `n`.

## Main results

* `EulerTotientOQ08OQ01.pow_add_totient_modEq` — for any base `a` and any modulus
  `n ≠ 0`, provided `k ≥ vₚ(n)` for every prime `p` (the composite pre-period
  condition):  `a ^ (k + φ n) ≡ a ^ k [MOD n]`.
* `EulerTotientOQ08OQ01.pow_add_mul_totient_modEq` — the multi-period version, adding
  any multiple `l · φ n` to the exponent.
* `EulerTotientOQ08OQ01.pow_modEq` — the full exponent reduction
  `a ^ k ≡ a ^ (K + (k - K) % φ n) [MOD n]` for `k ≥ K` where `K` bounds every
  `vₚ(n)`; the constant `K`-prefix is the composite pre-period.
* `EulerTotientOQ08OQ01.pow_add_totient_modEq_of_le` — a convenient factorisation-free
  sufficient condition: `n ≤ 2 ^ k` already forces `k ≥ vₚ(n)` for all `p`.

These are genuinely outside Mathlib's coprime-only coverage: e.g. they apply to
`2 ^ k (mod 12)` or `10 ^ k (mod 12)`, where the base shares a factor with the
modulus and Euler's theorem says nothing.
-/
import Mathlib
import Proofs.EulerTotientOQ08

open Nat (totient)
open Finset

namespace EulerTotientOQ08OQ01

open scoped Nat

/-!
### CRT assembly helper

A congruence that holds modulo each member of a pairwise-coprime family holds
modulo their product. This is the Chinese Remainder Theorem in its
`Nat.ModEq`/divisibility guise, packaged for a `Finset` of moduli.
-/

/-- If `x ≡ y` modulo every `f i` for `i ∈ s`, and the `f i` are pairwise coprime,
then `x ≡ y` modulo `∏ i ∈ s, f i`. -/
theorem modEq_prod_of_pairwiseCoprime {x y : ℕ} {s : Finset ℕ} {f : ℕ → ℕ}
    (hco : (s : Set ℕ).Pairwise (Function.onFun Nat.Coprime f))
    (h : ∀ i ∈ s, x ≡ y [MOD f i]) :
    x ≡ y [MOD ∏ i ∈ s, f i] := by
  induction s using Finset.induction with
  | empty => simpa using Nat.modEq_one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    -- `f a` is coprime to the product over the remaining factors.
    have hcoprime : (f a).Coprime (∏ i ∈ s, f i) := by
      refine Nat.Coprime.prod_right fun i hi => ?_
      exact hco (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (by rintro rfl; exact ha hi)
    refine (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp
      ⟨h a (Finset.mem_insert_self a s), ?_⟩
    exact ih (hco.mono (Finset.coe_subset.mpr (Finset.subset_insert a s)))
      (fun i hi => h i (Finset.mem_insert_of_mem hi))

/-!
### Composite-modulus periodicity
-/

/-- **Non-coprime composite Euler periodicity (single period).**
For every base `a`, modulus `n ≠ 0`, and exponent `k` at least as large as every
prime-power exponent of `n` (i.e. `n.factorization p ≤ k` for all `p`, equivalently
`k ≥ maxₚ vₚ(n)`), adding `φ n` to the exponent leaves `aᵏ` unchanged modulo `n` —
*even when `gcd(a, n) ≠ 1`*, the case Euler's theorem does not cover. -/
theorem pow_add_totient_modEq {n : ℕ} (hn : n ≠ 0) {a k : ℕ}
    (hk : ∀ p, n.factorization p ≤ k) :
    a ^ (k + totient n) ≡ a ^ k [MOD n] := by
  -- Rewrite the modulus as the product of its prime-power factors.
  have hn_eq : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    rw [← Nat.support_factorization]
    exact Nat.factorization_prod_pow_eq_self hn
  -- Rewrite only the modulus (keeping the `φ n` shift intact) as a product of
  -- prime powers, and glue the factorwise congruences via CRT.
  suffices h : a ^ (k + totient n) ≡ a ^ k
      [MOD ∏ p ∈ n.primeFactors, p ^ n.factorization p] by
    rwa [hn_eq] at h
  refine modEq_prod_of_pairwiseCoprime (f := fun p => p ^ n.factorization p) ?_ ?_
  · -- Distinct prime powers are coprime.
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp))
        (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq))).mpr hpq)
  · -- Factorwise: the `φ n`-shift is a whole number of `φ(pᵉ)`-periods.
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have he : 1 ≤ n.factorization p := by
      rw [← Nat.support_factorization] at hp
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
    -- `φ(pᵉ) ∣ φ n` because `pᵉ ∣ n` and `φ` is monotone under divisibility.
    obtain ⟨l, hl⟩ := Nat.totient_dvd_of_dvd (Nat.ordProj_dvd n p)
    rw [hl]
    calc a ^ (k + totient (p ^ n.factorization p) * l)
        = a ^ (k + l * totient (p ^ n.factorization p)) := by rw [Nat.mul_comm]
      _ ≡ a ^ k [MOD p ^ n.factorization p] :=
          EulerTotientOQ08.pow_add_mul_totient_modEq_primePow hpp he (hk p) l

/-- The multi-period form: adding any multiple `l · φ n` of the period to the
exponent leaves `aᵏ` unchanged modulo `n`, for every base `a` (non-coprime included),
provided `k` exceeds every prime-power exponent of `n`. -/
theorem pow_add_mul_totient_modEq {n : ℕ} (hn : n ≠ 0) {a k : ℕ}
    (hk : ∀ p, n.factorization p ≤ k) (l : ℕ) :
    a ^ (k + l * totient n) ≡ a ^ k [MOD n] := by
  induction l with
  | zero => simpa using Nat.ModEq.refl (a ^ k)
  | succ l ih =>
    have hstep : a ^ ((k + l * totient n) + totient n) ≡ a ^ (k + l * totient n) [MOD n] :=
      pow_add_totient_modEq hn (fun p => (hk p).trans (Nat.le_add_right _ _))
    calc a ^ (k + (l + 1) * totient n)
        = a ^ ((k + l * totient n) + totient n) := by congr 1; ring
      _ ≡ a ^ (k + l * totient n) [MOD n] := hstep
      _ ≡ a ^ k [MOD n] := ih

/-- **Full exponent reduction for composite moduli** (the non-coprime analogue of
`Nat.pow_totient_mod`). Fix any `K` bounding every prime-power exponent of `n`
(`n.factorization p ≤ K` for all `p`). Then for every base `a` and every `k ≥ K`,
the exponent of `aᵏ (mod n)` reduces to `K + (k - K) % φ n`. The leading `K` is the
composite pre-period: bases sharing a factor with `n` are not yet stable below it, but
from exponent `K` onward the sequence is periodic with period `φ n`. -/
theorem pow_modEq {n K : ℕ} (hn : n ≠ 0) (hK : ∀ p, n.factorization p ≤ K) {a k : ℕ}
    (hk : K ≤ k) :
    a ^ k ≡ a ^ (K + (k - K) % totient n) [MOD n] := by
  have hsplit : k = (K + (k - K) % totient n)
      + ((k - K) / totient n) * totient n := by
    have hdm : (k - K) % totient n + (k - K) / totient n * totient n = k - K :=
      Nat.mod_add_div' (k - K) (totient n)
    omega
  -- The reduced exponent still bounds every prime-power exponent of `n`.
  have hbound : ∀ p, n.factorization p ≤ K + (k - K) % totient n :=
    fun p => (hK p).trans (Nat.le_add_right _ _)
  calc a ^ k
      = a ^ ((K + (k - K) % totient n) + ((k - K) / totient n) * totient n) := by
        rw [← hsplit]
    _ ≡ a ^ (K + (k - K) % totient n) [MOD n] :=
        pow_add_mul_totient_modEq hn hbound ((k - K) / totient n)

/-- A factorisation-free sufficient condition. Since `vₚ(n) ≤ log₂ n` for every prime
`p`, the bound `n ≤ 2 ^ k` already guarantees `k ≥ vₚ(n)` for all `p`, so the
`φ n`-shift is periodic modulo `n`. -/
theorem pow_add_totient_modEq_of_le {n k : ℕ} (hn : n ≠ 0) (hnk : n ≤ 2 ^ k) {a : ℕ} :
    a ^ (k + totient n) ≡ a ^ k [MOD n] := by
  refine pow_add_totient_modEq hn fun p => ?_
  by_cases hpp : p.Prime
  · exact Nat.factorization_le_of_le_pow (hnk.trans (Nat.pow_le_pow_left hpp.two_le k))
  · simp [Nat.factorization_eq_zero_of_not_prime n hpp]

/-! ### Worked examples (non-coprime bases, composite moduli) -/

-- `2 ^ k (mod 12)`: `gcd(2, 12) = 2 ≠ 1`, so Euler's coprime theorem does not apply.
-- Here `12 ≤ 2⁴`, so the factorisation-free bound gives the period from `k = 4` on.
example : (2 : ℕ) ^ (4 + totient 12) ≡ 2 ^ 4 [MOD 12] :=
  pow_add_totient_modEq_of_le (by norm_num) (by norm_num)

-- Concrete sanity check of the same instance: `2⁸ = 256 ≡ 4` and `2⁴ = 16 ≡ 4 (mod 12)`.
example : (2 : ℕ) ^ 8 ≡ 2 ^ 4 [MOD 12] := by decide

-- Sharp pre-period for `n = 12 = 2²·3`: `maxₚ vₚ(12) = 2`, so the period already holds
-- from `k = 2`, which the factorisation-free `n ≤ 2ᵏ` bound (needing `k ≥ 4`) misses.
-- The bound `vₚ(12) ≤ 2` for every `p` holds because no `p³` divides `12`.
example : (2 : ℕ) ^ (2 + totient 12) ≡ 2 ^ 2 [MOD 12] := by
  refine pow_add_totient_modEq (by norm_num) fun p => ?_
  by_cases hp : p.Prime
  · by_contra hc
    push_neg at hc
    have hdvd : p ^ 3 ∣ 12 := (hp.pow_dvd_iff_le_factorization (by norm_num)).mpr (by omega)
    have hle : p ^ 3 ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    have hp2 : 2 ≤ p := hp.two_le
    have hpu : p < 3 := by
      by_contra h
      push_neg at h
      have : 27 ≤ p ^ 3 := by
        calc (27 : ℕ) = 3 ^ 3 := by norm_num
          _ ≤ p ^ 3 := Nat.pow_le_pow_left h 3
      omega
    interval_cases p
    · exact absurd hdvd (by decide)
  · simp [Nat.factorization_eq_zero_of_not_prime 12 hp]

-- `2⁶ = 64 ≡ 4` and `2² = 4 (mod 12)`: the sharp instance verified numerically.
example : (2 : ℕ) ^ 6 ≡ 2 ^ 2 [MOD 12] := by decide

-- `10 ^ k (mod 12)`: `gcd(10, 12) = 2`; full reduction of a large exponent of a
-- non-invertible base. `K = 2` bounds `vₚ(12)`, `φ(12) = 4`, so
-- `10 ^ 100 ≡ 10 ^ (2 + (100-2) % 4) = 10 ^ 4 (mod 12)`, and indeed `10⁴ ≡ 4`.
example : (10 : ℕ) ^ 100 ≡ 10 ^ 4 [MOD 12] := by decide

end EulerTotientOQ08OQ01
