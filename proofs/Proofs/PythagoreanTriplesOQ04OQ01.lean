import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-
# Sums of Two Squares from the Prime Case and Multiplicativity
# (pythagorean-triples-oq-04-oq-01)

The parent entry `pythagorean-triples-oq-04` packaged **Fermat's two-square
theorem for primes** — a prime `p` is a sum of two squares iff `p ≢ 3 (mod 4)` —
together with the **Brahmagupta–Fibonacci identity**, which closes the sums of
two squares under multiplication *for two factors*.

This file completes the natural next step: it lifts that two-factor
multiplicativity to **arbitrarily many prime factors**, yielding the constructive
*sufficiency* direction of the full two-square characterization:

> If every prime factor of `n` is `≢ 3 (mod 4)`, then `n` is a sum of two squares.

The proof is genuinely **constructive / algorithmic**, not a citation of
Mathlib's existence-only characterization `Nat.eq_sq_add_sq_iff`.  It works by
strong induction, peeling off the least prime factor:

* the least prime factor `p` of `n` is a sum of two squares by Fermat's prime
  case (`Nat.Prime.sq_add_sq`), since `p ≢ 3 (mod 4)`;
* `n / p` is smaller and inherits the hypothesis (its prime factors divide `n`),
  so the induction hypothesis represents it as a sum of two squares;
* the Brahmagupta–Fibonacci identity (`Nat.sq_add_sq_mul`) recombines the two
  representations into one for `n = p · (n / p)`.

Unrolling the recursion exhibits an *explicit* representation of `n` built up
from the Gaussian-integer factorizations of its primes.

## Results

| Result | Statement |
|--------|-----------|
| `sq_add_sq_of_forall_prime_factor` | all prime factors `≢ 3 (mod 4)` ⟹ `n = a²+b²` (constructive) |
| `sq_add_sq_pow` | `p` prime, `p ≢ 3 (mod 4)` ⟹ `pᵏ = a²+b²` |
| `sq_add_sq_of_forall_prime_factor'` | same as the headline, via `Nat.eq_sq_add_sq_iff` (cross-check) |

Status: 0 axioms, 0 sorries.
-/

namespace PythagoreanTriplesOQ04OQ01

open Nat

-- ============================================================================
-- Part I: Constructive sufficiency via strong induction
-- ============================================================================

/-- **Constructive sufficiency.** If every prime factor of `n` is `≢ 3 (mod 4)`,
then `n` is a sum of two squares.

The proof is by strong induction: peel off the least prime factor `p` (which is a
sum of two squares by Fermat's prime case, as `p ≢ 3`), apply the induction
hypothesis to the strictly smaller `n / p` (whose prime factors all divide `n`),
and recombine via the Brahmagupta–Fibonacci identity. This lifts the two-factor
multiplicativity of the parent entry to arbitrarily many prime factors and gives
the sufficiency half of the two-square theorem, constructively. -/
theorem sq_add_sq_of_forall_prime_factor :
    ∀ n : ℕ, (∀ p : ℕ, p.Prime → p ∣ n → p % 4 ≠ 3) → ∃ a b : ℕ, a ^ 2 + b ^ 2 = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h
    rcases Nat.lt_or_ge n 2 with hn | hn
    · -- Base cases `n = 0` and `n = 1`.
      interval_cases n
      · exact ⟨0, 0, by norm_num⟩
      · exact ⟨1, 0, by norm_num⟩
    · -- Inductive step: `n ≥ 2` has a least prime factor.
      have hn0 : 0 < n := by omega
      set p := n.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      have hpne3 : p % 4 ≠ 3 := h p hp hpdvd
      haveI : Fact p.Prime := ⟨hp⟩
      -- `p` itself is a sum of two squares (Fermat's prime case).
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := Nat.Prime.sq_add_sq hpne3
      -- The cofactor `m = n / p` is smaller and inherits the hypothesis.
      set m := n / p with hm_def
      have hpm : p * m = n := Nat.mul_div_cancel' hpdvd
      have hmdvd : m ∣ n := ⟨p, by rw [← hpm, Nat.mul_comm]⟩
      have hm_lt : m < n := Nat.div_lt_self hn0 hp.one_lt
      have hm_fac : ∀ q : ℕ, q.Prime → q ∣ m → q % 4 ≠ 3 :=
        fun q hq hqm => h q hq (hqm.trans hmdvd)
      obtain ⟨c, d, hcd⟩ := ih m hm_lt hm_fac
      -- Recombine with the Brahmagupta–Fibonacci identity.
      obtain ⟨r, s, hrs⟩ := Nat.sq_add_sq_mul hab.symm hcd.symm
      exact ⟨r, s, by rw [← hpm, hrs]⟩

-- ============================================================================
-- Part II: Prime powers
-- ============================================================================

/-- Every power `pᵏ` of a prime `p ≢ 3 (mod 4)` is a sum of two squares: the only
prime factor of `pᵏ` is `p`, so the hypothesis of the headline holds. -/
theorem sq_add_sq_pow {p : ℕ} (hp : p.Prime) (hp3 : p % 4 ≠ 3) (k : ℕ) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p ^ k := by
  apply sq_add_sq_of_forall_prime_factor
  intro q hq hqdvd
  have hqp : q ∣ p := hq.dvd_of_dvd_pow hqdvd
  have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  rwa [this]

-- ============================================================================
-- Part III: Cross-check against Mathlib's full characterization
-- ============================================================================

/-- The same sufficiency result, obtained instead from Mathlib's existence
characterization `Nat.eq_sq_add_sq_iff`: when no prime factor is `≡ 3 (mod 4)`,
the parity condition there is vacuously satisfied. This is a second, independent
(non-constructive) proof of `sq_add_sq_of_forall_prime_factor`, confirming the
two formulations agree. -/
theorem sq_add_sq_of_forall_prime_factor' (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p % 4 ≠ 3) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = n := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
    rw [Nat.eq_sq_add_sq_iff]
    intro q hq hq3
    exact absurd hq3 (h q (prime_of_mem_primeFactors hq) (dvd_of_mem_primeFactors hq))
  exact ⟨a, b, hab.symm⟩

end PythagoreanTriplesOQ04OQ01

#check @PythagoreanTriplesOQ04OQ01.sq_add_sq_of_forall_prime_factor
#check @PythagoreanTriplesOQ04OQ01.sq_add_sq_pow
#check @PythagoreanTriplesOQ04OQ01.sq_add_sq_of_forall_prime_factor'
