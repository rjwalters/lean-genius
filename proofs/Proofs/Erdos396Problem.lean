/-
# Erdős Problem #396 — Descending Factorials Dividing Central Binomial Coefficients

Erdős and Graham asked: For every positive integer k, does there exist n
such that
  ∏_{i=0}^{k} (n − i) | C(2n, n)?

That is, does n(n−1)(n−2)⋯(n−k) divide the central binomial coefficient?

Known results:
- n+1 always divides C(2n, n) (Catalan numbers)
- n itself divides C(2n, n) only rarely
- Pomerance (2014): for any k ≥ 0, infinitely many n satisfy (n−k) | C(2n, n),
  but this set has upper density < 1/3
- Pomerance (2014): the set of n with ∏_{i=1}^{k} (n+i) | C(2n, n) has density 1

Reference: https://erdosproblems.com/396
-/

import Mathlib

open Nat

namespace Erdos396

/- ## Core Definitions -/

/-- The descending product `n · (n−1) · (n−2) ⋯ (n−k)` of length `k+1`.
    Equal to `Nat.descFactorial n (k+1)`; we re-expose it under a name
    matching the problem statement for readability. -/
def descProduct (n k : ℕ) : ℕ :=
  n.descFactorial (k + 1)

/-- The descending product equals the standard descending factorial of length `k+1`. -/
lemma descProduct_eq_descFactorial (n k : ℕ) :
    descProduct n k = n.descFactorial (k + 1) := rfl

/-- For `k = 0` the descending product collapses to `n` itself. -/
lemma descProduct_zero (n : ℕ) : descProduct n 0 = n := by
  simp [descProduct, Nat.descFactorial]

/-- **Erdős Problem #396 (Erdős–Graham).**
    For every `k`, there exists `n > k` such that
    `n · (n−1) · (n−2) ⋯ (n−k)` divides the central binomial coefficient `C(2n, n)`.

    The bound `k < n` rules out the vacuous case where the descending product
    truncates to `0` and divides everything in `ℕ`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, k < n ∧ descProduct n k ∣ Nat.centralBinom n

/- ## Basic Divisibility Results -/

/-- `n+1` always divides `C(2n, n)`, yielding the Catalan number `C(2n,n)/(n+1)`.
    This is the fundamental property behind Catalan numbers. -/
theorem catalan_divisibility (n : ℕ) :
    (n + 1) ∣ Nat.centralBinom n :=
  Nat.succ_dvd_centralBinom n

/-- `n` does **not** in general divide `C(2n, n)`. Concrete counterexample:
    `3 ∤ C(6, 3) = 20`. This shows that the `k = 0` slice of the conjecture
    is not a triviality — most `n` do not work. -/
theorem n_not_always_dvd_centralBinom :
    ∃ n : ℕ, ¬ (n ∣ Nat.centralBinom n) := by
  refine ⟨3, ?_⟩
  decide

/- ## Witnesses for Small k -/

/-- For `k = 0`, the conjecture holds with `n = 2`:
    `Nat.descFactorial 2 1 = 2` and `Nat.centralBinom 2 = C(4, 2) = 6`,
    so the descending product divides the central binomial coefficient. -/
theorem conjecture_holds_for_zero :
    ∃ n : ℕ, 0 < n ∧ descProduct n 0 ∣ Nat.centralBinom n := by
  refine ⟨2, by decide, ?_⟩
  decide

/-- For `k = 1`, the value `n = 2` is also a witness:
    `2 · 1 = 2 ∣ 6 = C(4, 2)`. -/
theorem conjecture_holds_for_one :
    ∃ n : ℕ, 1 < n ∧ descProduct n 1 ∣ Nat.centralBinom n := by
  refine ⟨2, by decide, ?_⟩
  decide

/- ## Pomerance's Results (2014)

  Pomerance: for any `k ≥ 0`, infinitely many `n` satisfy `(n−k) | C(2n,n)`,
  and the set of such `n` has upper density `< 1/3`.
  Pomerance: the set `{n : ∏_{i=1}^{k}(n+i) | C(2n,n)}` has asymptotic density 1.
  Measure-theoretic statements require density infrastructure not yet present here. -/

/- ## Computational Evidence -/

/-- The smallest `k = 0` witness `n = 2` checks out: `C(4, 2) = 6`. -/
example : Nat.centralBinom 2 = 6 := by decide

/-- `3 ∤ C(6, 3) = 20`, demonstrating that `n ∣ C(2n, n)` is not universal. -/
example : ¬ (3 ∣ Nat.centralBinom 3) := by decide

/-- The next `k = 0` witness after `n = 2` is `n = 6`: `6 ∣ C(12, 6) = 924`. -/
example : 6 ∣ Nat.centralBinom 6 := by decide

end Erdos396
