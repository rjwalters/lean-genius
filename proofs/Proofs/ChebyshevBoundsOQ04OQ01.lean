/-
  Chebyshev Bounds OQ-04-OQ-01: Toward an Elementary PNT (Selberg-Erdős)

  ## Open Question

  Prove ψ(n)/n → 1 (the Prime Number Theorem for the second Chebyshev
  function) elementarily, removing the axiom `chebyshevPsi_asymptotic`
  from `ChebyshevBoundsOQ04.lean`.

  ## Status: Iteration 2 / ACT

  Iter 1 scaffolded the Selberg-Erdős 1949 elementary proof strategy
  (Λ₂ and S₂ definitions, non-negativity, monotonicity, base values
  at 0 and 1). Iter 2 adds the **prime-case lemmas**:

  - `vonMangoldtConv_prime`: `(Λ ∗ Λ)(p) = 0` for prime `p`.
  - `selbergLambda2_prime`: `Λ₂(p) = (log p)²` for prime `p`.
  - `selbergSum2_one`: `S₂(1) = 0` (both summands `Λ₂(0)` and `Λ₂(1)`
    vanish).
  - `selbergSum2_two`: `S₂(2) = (log 2)²` (the first non-zero value of
    the partial sum, via `selbergLambda2_prime Nat.prime_two`).

  Definitions and roadmap from iter 1:

  - The Selberg auxiliary function
        Λ₂(n) = Λ(n)·log n + (Λ ∗ Λ)(n),
    where Λ ∗ Λ denotes Dirichlet convolution.
  - The Selberg partial sum S₂(N) = Σ_{n ≤ N} Λ₂(n).
  - Routine non-negativity, base-value, and monotonicity lemmas.
  - The elementary-PNT roadmap and identified Mathlib gaps.

  No new axioms are added; the parent file's `chebyshevPsi_asymptotic`
  axiom remains the open target.

  ## Roadmap

  1. **Selberg's symmetry formula**: S₂(N) = 2N·log N + O(N).

     This is the central identity of the elementary proof. It is
     provable from the Möbius–log identity
        Σ_{d ∣ n} μ(d)·log²(n/d) = Λ₂(n)   (n ≥ 1)
     combined with
        Σ_{n ≤ N} log²n = N·log²N − 2N·log N + O(log²N).

  2. **Reduction to oscillation control**: define
        R(x) := ψ(x) − x,    V(x) := |R(x)| / x.
     Selberg's symmetry formula yields the Tauberian inequality
        V(x)·log x ≤ (2/x)·Σ_{n ≤ x} V(x/n)·Λ(n) + O(1),
     which expresses oscillations of ψ(x)/x in terms of an averaged
     self-reference.

  3. **Erdős's combinatorial lemma**: if V(x) ≤ V for all x ≥ x₀ and
     V(x) attains a value close to V along a subsequence, then for some
     c > 0 the values V(x) cannot stay arbitrarily close to V on a long
     enough interval — forcing lim sup V(x) = 0.

  4. **Conclusion**: lim ψ(x)/x = 1, i.e. `chebyshevPsi_asymptotic`.

  ## Mathlib gaps observed (Mathlib v4.26.0)

  - No formalization of Selberg's symmetry formula.
  - No analogue of the Möbius–log identity Σ_{d ∣ n} μ(d)·log²(n/d).
  - No partial-summation framework specialized to Λ₂-type sums.

  ## References

  - Selberg, "An elementary proof of the prime-number theorem",
    Annals of Math. 50 (1949), 305–313.
  - Erdős, "On a new method in elementary number theory which leads to
    an elementary proof of the prime number theorem",
    PNAS 35 (1949), 374–384.
  - Tenenbaum, "Introduction to analytic and probabilistic number
    theory" (3rd ed., 2015), §I.6.
  - Iwaniec–Kowalski, "Analytic Number Theory", AMS Colloquium 53
    (2004), §2.3.
-/

import Mathlib
import Proofs.ChebyshevBoundsOQ04

namespace ChebyshevBoundsOQ04OQ01

open Nat Finset ArithmeticFunction
open scoped BigOperators

/-! ## Dirichlet convolution Λ ∗ Λ

We use the explicit divisor-sum form so that subsequent algebraic
manipulations (which the elementary proof requires) avoid the
`divisorsAntidiagonal` abstraction. -/

/-- The Dirichlet convolution `(Λ ∗ Λ)` at `n`, defined explicitly:
    `(Λ ∗ Λ)(n) = Σ_{d ∣ n} Λ(d) · Λ(n/d)`.
    For `n = 0`, the empty divisor set yields `0`. -/
noncomputable def vonMangoldtConv (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d)

/-! ## Selberg's auxiliary function Λ₂

Λ₂(n) := Λ(n)·log n + (Λ ∗ Λ)(n). The basic identity used by Selberg is

   Σ_{d ∣ n} μ(d)·log²(n/d) = Λ₂(n)   (n ≥ 1),

from which Selberg's symmetry formula

   Σ_{n ≤ N} Λ₂(n) = 2N·log N + O(N)

follows by standard Dirichlet hyperbola summation. -/

/-- Selberg's auxiliary function:
    `Λ₂(n) = Λ(n) · log n + (Λ ∗ Λ)(n)`. -/
noncomputable def selbergLambda2 (n : ℕ) : ℝ :=
  vonMangoldt n * Real.log n + vonMangoldtConv n

/-- The partial Selberg sum: `S₂(N) = Σ_{n ≤ N} Λ₂(n)`. -/
noncomputable def selbergSum2 (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), selbergLambda2 n

/-! ### Base values and non-negativity -/

/-- `(Λ ∗ Λ)(0) = 0` since `divisors 0 = ∅`. -/
theorem vonMangoldtConv_zero : vonMangoldtConv 0 = 0 := by
  unfold vonMangoldtConv
  simp

/-- `(Λ ∗ Λ)(1) = 0` since the only divisor is `1` and `Λ(1) = 0`. -/
theorem vonMangoldtConv_one : vonMangoldtConv 1 = 0 := by
  unfold vonMangoldtConv
  simp [vonMangoldt_apply_one]

/-- `(Λ ∗ Λ)(n) ≥ 0` for all `n`, since `Λ ≥ 0` everywhere. -/
theorem vonMangoldtConv_nonneg (n : ℕ) : 0 ≤ vonMangoldtConv n := by
  unfold vonMangoldtConv
  exact Finset.sum_nonneg (fun _ _ =>
    mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)

/-- `Λ₂(0) = 0`. -/
theorem selbergLambda2_zero : selbergLambda2 0 = 0 := by
  unfold selbergLambda2
  rw [vonMangoldtConv_zero]
  simp [ArithmeticFunction.map_zero]

/-- `Λ₂(1) = 0`: both summands vanish (Λ(1) = 0 and (Λ ∗ Λ)(1) = 0). -/
theorem selbergLambda2_one : selbergLambda2 1 = 0 := by
  unfold selbergLambda2
  rw [vonMangoldtConv_one, vonMangoldt_apply_one]
  ring

/-- `Λ₂(n) ≥ 0` for all `n`. The first summand is non-negative because
    `Λ(n) ≥ 0` and `log n ≥ 0` (with the convention `log 0 = 0`). -/
theorem selbergLambda2_nonneg (n : ℕ) : 0 ≤ selbergLambda2 n := by
  unfold selbergLambda2
  refine add_nonneg ?_ (vonMangoldtConv_nonneg n)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [ArithmeticFunction.map_zero]
  · exact mul_nonneg vonMangoldt_nonneg
      (Real.log_nonneg (by exact_mod_cast h))

/-! ### Prime values

For a prime `p` the divisor sum `(Λ ∗ Λ)(p)` collapses: the only
divisors are `1` and `p`, and `Λ(1) = 0` annihilates both cross terms.
Consequently `Λ₂(p)` reduces to the single summand `Λ(p) · log p`, which
is `(log p)²` by `vonMangoldt_apply_prime`.

These are the iter-2 deliverables flagged as routine in the iter-1
roadmap (items 1 and 2 of the "Future Work" list). They are the first
non-zero base-case values of `Λ₂`, and together with the `S₂` recurrence
established in iter 1 they yield the first non-trivial values of the
partial Selberg sum (`selbergSum2_two` below). -/

/-- Iter 2: `(Λ ∗ Λ)(p) = 0` for any prime `p`.

    The divisor set is `divisors p = {1, p}` (`Nat.Prime.divisors`), so
    the convolution expands to two terms:
      * `d = 1`: `Λ(1) · Λ(p)`. Annihilated by `vonMangoldt_apply_one`.
      * `d = p`: `Λ(p) · Λ(p / p) = Λ(p) · Λ(1)`. Same annihilator.
    The Finset sum `Finset.sum_pair` requires `1 ≠ p`, supplied by
    `hp.one_lt.ne`. No new imports. -/
theorem vonMangoldtConv_prime {p : ℕ} (hp : Nat.Prime p) :
    vonMangoldtConv p = 0 := by
  unfold vonMangoldtConv
  rw [Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne]
  simp [vonMangoldt_apply_one, Nat.div_self hp.pos]

/-- Iter 2: `Λ₂(p) = (log p)²` for any prime `p`.

    Immediate from `vonMangoldtConv_prime hp` (annihilates the
    convolution summand) and `vonMangoldt_apply_prime hp` (rewrites
    `Λ(p) = log p`, so the first summand becomes `log p · log p`). -/
theorem selbergLambda2_prime {p : ℕ} (hp : Nat.Prime p) :
    selbergLambda2 p = (Real.log p) ^ 2 := by
  unfold selbergLambda2
  rw [vonMangoldtConv_prime hp, vonMangoldt_apply_prime hp]
  ring

/-! ### Partial sum properties -/

/-- `S₂(0) = 0`: the only term is `Λ₂(0) = 0`. -/
theorem selbergSum2_zero : selbergSum2 0 = 0 := by
  unfold selbergSum2
  rw [Finset.sum_range_one, selbergLambda2_zero]

/-- `S₂(N+1) = S₂(N) + Λ₂(N+1)`: the partial-sum recurrence. -/
theorem selbergSum2_succ (N : ℕ) :
    selbergSum2 (N + 1) = selbergSum2 N + selbergLambda2 (N + 1) := by
  unfold selbergSum2
  rw [Finset.sum_range_succ]

/-- The partial Selberg sum is non-negative. -/
theorem selbergSum2_nonneg (N : ℕ) : 0 ≤ selbergSum2 N := by
  unfold selbergSum2
  exact Finset.sum_nonneg (fun n _ => selbergLambda2_nonneg n)

/-- The partial Selberg sum is monotone in the truncation parameter. -/
theorem selbergSum2_mono : Monotone selbergSum2 := by
  intro M N hMN
  unfold selbergSum2
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k _ _
    exact selbergLambda2_nonneg k

/-- Iter 2: `S₂(1) = 0`. Both summands `Λ₂(0)` and `Λ₂(1)` vanish, so
    the partial sum is `0`.

    The first non-zero value of `S₂` occurs at `N = 2`, as recorded by
    `selbergSum2_two` below. This places the support of the Selberg
    sequence `(S₂(N))_{N ≥ 0}` precisely on `N ≥ 2`. -/
theorem selbergSum2_one : selbergSum2 1 = 0 := by
  have h : selbergSum2 1 = selbergSum2 0 + selbergLambda2 1 :=
    selbergSum2_succ 0
  rw [h, selbergSum2_zero, selbergLambda2_one]
  ring

/-- Iter 2: `S₂(2) = (log 2)²`.

    The first non-zero value of the partial Selberg sum. Computation:
    `S₂(2) = S₂(1) + Λ₂(2) = 0 + (log 2)²` by `selbergSum2_succ`,
    `selbergSum2_one`, and `selbergLambda2_prime Nat.prime_two`. -/
theorem selbergSum2_two : selbergSum2 2 = (Real.log 2) ^ 2 := by
  have h : selbergSum2 2 = selbergSum2 1 + selbergLambda2 2 :=
    selbergSum2_succ 1
  rw [h, selbergSum2_one, selbergLambda2_prime Nat.prime_two]
  ring

/-! ## Future Work

Iter-2 status:

- ✅ **`vonMangoldtConv_prime`**: `(Λ ∗ Λ)(p) = 0` for prime `p`.
  Discharged via `Nat.Prime.divisors` + `Finset.sum_pair`.
- ✅ **`selbergLambda2_prime`**: `Λ₂(p) = (log p)²`. Discharged via
  `vonMangoldtConv_prime` + `vonMangoldt_apply_prime`.
- ✅ **`selbergSum2_one`** / **`selbergSum2_two`**: first non-trivial
  partial-sum values (`S₂(1) = 0`, `S₂(2) = (log 2)²`).

Remaining deliverables in order of increasing difficulty:

1. **`vonMangoldtConv_prime_pow`**: `(Λ ∗ Λ)(p^k) = (k-1) · (log p)²`
   for prime `p` and `k ≥ 1`. Generalizes `vonMangoldtConv_prime`
   (k = 1 case) via `Nat.divisors_prime_pow` and a small Finset sum
   over `range (k+1)`. Routine.

2. **`selbergLambda2_eq_moebius_log_sq`**: the identity
        Λ₂(n) = Σ_{d ∣ n} μ(d) · (log (n/d))²    (n ≥ 1).
   Provable from the Mathlib `moebius_mul_coe_zeta` machinery once one
   knows Λ = μ ∗ log (the standard expansion).

3. **`selbergSum2_eq_two_n_log_n_plus_O`**: Selberg's symmetry formula
        S₂(N) = 2 N · log N + O(N).
   This is the central identity. The error-term step requires summation
   by parts and quantitative control of Σ_{d ≤ x} μ(d) — but only its
   `O(x)` form, which is well within elementary bounds.

4. **Tauberian step → PNT**: Erdős–Selberg's combinatorial finishing
   argument, the longest part of the elementary proof.

The total estimated formalization size is several thousand lines, but
each step decomposes into Mathlib-friendly pieces. -/

end ChebyshevBoundsOQ04OQ01
