/-
# Erdős #458 OQ-05 — Prime-index values from `Nat.nth`, and axiom-free base cases

The parent `Erdos458Problem.lean` studies the LCM inequality

    lcm(1, …, p_{k+1} - 1) < p_k · lcm(1, …, p_k)      (Erdős #458, OPEN)

with `p_k = nthPrime k = Nat.nth Nat.Prime k`.  Its open question OQ-05 asks
whether the prime-index *value* facts (`nthPrime 0 = 2`, …) can be obtained
directly from the `Nat.nth` definition rather than asserted, and OQ-03 asks
for verification of the conjecture for more values of `k`.

This companion answers both, and additionally removes the `native_decide`
dependency of the parent's base cases:

* The prime-index values are extended to `nthPrime 5 = 13, …, nthPrime 10 = 31`,
  each proved from `Nat.nth_count` (the `Nat.nth`/`Nat.count` Galois bridge)
  together with kernel `decide`.  No `native_decide`, hence **no
  `Lean.ofReduceBool`** — these are axiom-free.

* The conjecture's base cases `k = 1, 2, 3, 4` are verified with kernel
  `decide` (again avoiding `native_decide`), extending the parent's `k = 1, 2`
  and making the verified instances genuinely axiom-free.

Everything is self-contained (imports only Mathlib) and reproves `lcm_upto`
and `nthPrime` so that each result is independently checkable and 0-axiom.

Main results (0 axioms, 0 sorries, no `native_decide`):
* `nthPrime_five … nthPrime_ten` — the 6th through 11th primes, from `Nat.nth`
* `erdos458_base` — the conjecture instance holds for `k = 1, 2, 3, 4`
-/

import Mathlib

open Finset

namespace Erdos458OQ05

/-- `lcm_upto n = lcm(1, 2, …, n)` (matches the parent definition). -/
def lcm_upto (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- The `k`-th prime, `p_k = Nat.nth Nat.Prime k` (matches the parent). -/
noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- Every `nthPrime` is prime. -/
theorem nthPrime_prime (k : ℕ) : (nthPrime k).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k

/-- `nthPrime` is strictly increasing. -/
theorem nthPrime_strictMono : StrictMono nthPrime := fun _ _ hij =>
  Nat.nth_strictMono Nat.infinite_setOf_prime hij

/-!
## Prime-index values from `Nat.nth`

`Nat.nth_count : p n → Nat.nth p (Nat.count p n) = n` turns a proof that `n`
is the `(Nat.count p n)`-th element of `p` into the value of `Nat.nth`.  With
`Nat.count Nat.Prime n` (the number of primes `< n`) evaluated by `decide`,
each prime index is pinned down without `native_decide`.
-/

/-- The 0th prime is `2` (included for a self-contained account). -/
theorem nthPrime_zero : nthPrime 0 = 2 := by
  show Nat.nth Nat.Prime 0 = 2
  have h := Nat.nth_count (p := Nat.Prime) Nat.prime_two
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  rwa [hc] at h

/-- `nthPrime 1 = 3`. -/
theorem nthPrime_one : nthPrime 1 = 3 := by
  show Nat.nth Nat.Prime 1 = 3
  have h := Nat.nth_count (p := Nat.Prime) Nat.prime_three
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  rwa [hc] at h

/-- `nthPrime 2 = 5`. -/
theorem nthPrime_two : nthPrime 2 = 5 := by
  show Nat.nth Nat.Prime 2 = 5
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 5 by decide)
  have hc : Nat.count Nat.Prime 5 = 2 := by decide
  rwa [hc] at h

/-- `nthPrime 3 = 7`. -/
theorem nthPrime_three : nthPrime 3 = 7 := by
  show Nat.nth Nat.Prime 3 = 7
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 7 by decide)
  have hc : Nat.count Nat.Prime 7 = 3 := by decide
  rwa [hc] at h

/-- `nthPrime 4 = 11`. -/
theorem nthPrime_four : nthPrime 4 = 11 := by
  show Nat.nth Nat.Prime 4 = 11
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 11 by decide)
  have hc : Nat.count Nat.Prime 11 = 4 := by decide
  rwa [hc] at h

/-- **New:** `nthPrime 5 = 13`. -/
theorem nthPrime_five : nthPrime 5 = 13 := by
  show Nat.nth Nat.Prime 5 = 13
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 13 by decide)
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  rwa [hc] at h

/-- **New:** `nthPrime 6 = 17`. -/
theorem nthPrime_six : nthPrime 6 = 17 := by
  show Nat.nth Nat.Prime 6 = 17
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 17 by decide)
  have hc : Nat.count Nat.Prime 17 = 6 := by decide
  rwa [hc] at h

/-- **New:** `nthPrime 7 = 19`. -/
theorem nthPrime_seven : nthPrime 7 = 19 := by
  show Nat.nth Nat.Prime 7 = 19
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 19 by decide)
  have hc : Nat.count Nat.Prime 19 = 7 := by decide
  rwa [hc] at h

/-- **New:** `nthPrime 8 = 23`. -/
theorem nthPrime_eight : nthPrime 8 = 23 := by
  show Nat.nth Nat.Prime 8 = 23
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 23 by decide)
  have hc : Nat.count Nat.Prime 23 = 8 := by decide
  rwa [hc] at h

/-- **New:** `nthPrime 9 = 29`. -/
theorem nthPrime_nine : nthPrime 9 = 29 := by
  show Nat.nth Nat.Prime 9 = 29
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 29 by decide)
  have hc : Nat.count Nat.Prime 29 = 9 := by decide
  rwa [hc] at h

/-- **New:** `nthPrime 10 = 31`. -/
theorem nthPrime_ten : nthPrime 10 = 31 := by
  show Nat.nth Nat.Prime 10 = 31
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 31 by decide)
  have hc : Nat.count Nat.Prime 31 = 10 := by decide
  rwa [hc] at h

/-!
## Axiom-free base cases of Erdős #458

The conjecture instance for a given `k` is

    lcm_upto (nthPrime (k+1) - 1) < nthPrime k * lcm_upto (nthPrime k).

Rewriting the two prime values to literals reduces each instance to a decidable
inequality between concrete naturals, closed by kernel `decide` (no
`native_decide`).  This extends the parent's `k = 1, 2` to `k = 1, 2, 3, 4`.
-/

/-- Base case `k = 1`: `lcm_upto 4 < 3 · lcm_upto 3`  (12 < 18). -/
theorem erdos458_k1 :
    lcm_upto (nthPrime 2 - 1) < nthPrime 1 * lcm_upto (nthPrime 1) := by
  rw [nthPrime_one, nthPrime_two]; decide

/-- Base case `k = 2`: `lcm_upto 6 < 5 · lcm_upto 5`  (60 < 300). -/
theorem erdos458_k2 :
    lcm_upto (nthPrime 3 - 1) < nthPrime 2 * lcm_upto (nthPrime 2) := by
  rw [nthPrime_two, nthPrime_three]; decide

/-- Base case `k = 3`: `lcm_upto 10 < 7 · lcm_upto 7`  (2520 < 2940). -/
theorem erdos458_k3 :
    lcm_upto (nthPrime 4 - 1) < nthPrime 3 * lcm_upto (nthPrime 3) := by
  rw [nthPrime_three, nthPrime_four]; decide

/-- Base case `k = 4`: `lcm_upto 12 < 11 · lcm_upto 11`  (27720 < 304920). -/
theorem erdos458_k4 :
    lcm_upto (nthPrime 5 - 1) < nthPrime 4 * lcm_upto (nthPrime 4) := by
  rw [nthPrime_four, nthPrime_five]; decide

/-- **Packaged base cases.**  Erdős #458 holds for `k ∈ {1, 2, 3, 4}`. -/
theorem erdos458_base (k : ℕ) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
    lcm_upto (nthPrime (k + 1) - 1) < nthPrime k * lcm_upto (nthPrime k) := by
  interval_cases k
  · exact erdos458_k1
  · exact erdos458_k2
  · exact erdos458_k3
  · exact erdos458_k4

end Erdos458OQ05
